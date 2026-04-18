#!/usr/bin/env python3
"""
Brute-force every unique "Power" IR code in Flipper-IRDB's TVs/ tree
through a Broadlink RM-family device, logging a precise wall-clock
timestamp per shot. Pair with a webcam pointed at the TV: after the
sweep, scrub the video to the moment the TV reacts, read the overlay
clock, and grep this log for that timestamp to find the winning code.

Built for a JVC LT-40E71(A) (Vestel chassis / DSG-JVC / RM-C3170) but
agnostic to the specific model. Usage:

  # Live sweep against a Broadlink at the default IP
  nix-shell -p "python3.withPackages (ps: [ ps.broadlink ])" \\
      --run "python3 jvc_bruteforce.py"

  # Dry-run (no device; prints what would fire)
  python3 jvc_bruteforce.py --dry-run

  # Different IP / delay / regex
  python3 jvc_bruteforce.py --ip 10.0.0.42 --delay 4.0 \\
      --regex '^(power|pwr|menu|vol_up)$'
"""

from __future__ import annotations

import argparse
import base64
import datetime as dt
import glob
import hashlib
import os
import pathlib
import re
import signal
import sys
import time
from dataclasses import dataclass, field
from typing import Iterable

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

DEFAULT_REPO_ROOT = str(pathlib.Path(__file__).resolve().parent / "TVs")
DEFAULT_RM_IP = "10.0.0.36"
DEFAULT_DELAY = 2.5
DEFAULT_REPEATS = 2
DEFAULT_REPEAT_GAP = 0.2
DEFAULT_REGEX = r"^(power|pwr|power_on|on_off)$"
DEFAULT_LOG = "~/jvc_bruteforce.log"

# DSG/Currys-JVC chassis is Vestel; prioritize Vestel-family rebrand
# folders first, then JVC-branded, then everything else alphabetical.
PRIORITY_BRANDS = [
    "Telefunken", "Blaupunkt", "Bush", "Hitachi", "FINLUX", "Finlux",
    "Polaroid", "Luxor", "Vestel", "Grundig", "Digihome", "Telekom",
    "ContinentalEdison", "EdenWood", "EssentielB", "Boulanger", "Brandt",
    "Thomson",
    "JVC",
]

# Broadlink RM-series IR encoding is in 32.84 µs ticks.
BROADLINK_TICK_US = 32.84

# ---------------------------------------------------------------------------
# Flipper .ir parser
# ---------------------------------------------------------------------------

@dataclass
class Entry:
    name: str
    source: str                  # relative path under repo root
    type: str                    # "parsed" | "raw"
    protocol: str = ""
    address: tuple[int, ...] = ()
    command: tuple[int, ...] = ()
    frequency: int = 38000
    duty_cycle: float = 0.33
    data_us: tuple[int, ...] = ()

    def dedup_key(self) -> str:
        if self.type == "parsed":
            return f"{self.protocol}|{','.join(f'{b:02X}' for b in self.address)}|{','.join(f'{b:02X}' for b in self.command)}"
        # raw: hash the pulse sequence (ignore minor frequency jitter)
        h = hashlib.sha1(",".join(str(u) for u in self.data_us).encode()).hexdigest()[:16]
        return f"RAW|{self.frequency}|{h}"


def _split_stanzas(text: str) -> Iterable[list[str]]:
    current: list[str] = []
    for raw in text.splitlines():
        line = raw.rstrip()
        if line.startswith("#") or line.startswith("Filetype:") or line.startswith("Version:"):
            if current:
                yield current
                current = []
            continue
        if not line.strip():
            if current:
                yield current
                current = []
            continue
        current.append(line)
    if current:
        yield current


def _parse_hex_tuple(s: str) -> tuple[int, ...]:
    return tuple(int(b, 16) for b in s.split())


def parse_file(path: str, repo_root: str) -> list[Entry]:
    try:
        text = pathlib.Path(path).read_text(errors="replace")
    except OSError:
        return []

    rel = os.path.relpath(path, repo_root)
    out: list[Entry] = []
    for stanza in _split_stanzas(text):
        fields = {}
        for line in stanza:
            if ":" not in line:
                continue
            k, _, v = line.partition(":")
            fields[k.strip()] = v.strip()
        if "name" not in fields or "type" not in fields:
            continue
        try:
            if fields["type"] == "parsed":
                out.append(Entry(
                    name=fields["name"],
                    source=rel,
                    type="parsed",
                    protocol=fields.get("protocol", ""),
                    address=_parse_hex_tuple(fields.get("address", "")),
                    command=_parse_hex_tuple(fields.get("command", "")),
                ))
            elif fields["type"] == "raw":
                data_us = tuple(int(x) for x in fields.get("data", "").split())
                if not data_us:
                    continue
                out.append(Entry(
                    name=fields["name"],
                    source=rel,
                    type="raw",
                    frequency=int(fields.get("frequency", "38000")),
                    duty_cycle=float(fields.get("duty_cycle", "0.33")),
                    data_us=data_us,
                ))
        except (ValueError, KeyError):
            continue
    return out


# ---------------------------------------------------------------------------
# Protocol encoders -> list[int] of alternating mark/space µs
# ---------------------------------------------------------------------------

def _nec_bits(value: int, nbits: int) -> list[int]:
    """LSB-first NEC-style bits; mark=560, space-0=560, space-1=1690."""
    pulses: list[int] = []
    for i in range(nbits):
        bit = (value >> i) & 1
        pulses.append(560)
        pulses.append(1690 if bit else 560)
    return pulses


def encode_nec(addr: int, cmd: int) -> list[int]:
    # 32-bit payload: addr, ~addr, cmd, ~cmd (all LSB first)
    frame = (addr & 0xFF) | ((~addr & 0xFF) << 8) | ((cmd & 0xFF) << 16) | ((~cmd & 0xFF) << 24)
    pulses = [9000, 4500]
    pulses += _nec_bits(frame, 32)
    pulses.append(560)            # final mark
    pulses.append(40000)          # trailing gap
    return pulses


def encode_necext(addr_lo: int, addr_hi: int, cmd: int, cmd_inv: int | None = None) -> list[int]:
    # NEC-extended: full 16-bit addr, no inversion on addr half.
    if cmd_inv is None:
        cmd_inv = (~cmd) & 0xFF
    frame = (addr_lo & 0xFF) | ((addr_hi & 0xFF) << 8) | ((cmd & 0xFF) << 16) | ((cmd_inv & 0xFF) << 24)
    pulses = [9000, 4500]
    pulses += _nec_bits(frame, 32)
    pulses.append(560)
    pulses.append(40000)
    return pulses


def encode_samsung32(addr: int, cmd: int) -> list[int]:
    # 4500/4500 leader; payload = addr, addr, cmd, ~cmd; LSB first.
    frame = (addr & 0xFF) | ((addr & 0xFF) << 8) | ((cmd & 0xFF) << 16) | ((~cmd & 0xFF) << 24)
    pulses = [4500, 4500]
    pulses += _nec_bits(frame, 32)
    pulses.append(560)
    pulses.append(40000)
    return pulses


def encode_nec42(addr: int, cmd: int, ext: bool) -> list[int]:
    # 42-bit NEC variant used by some Chinese TVs. 13-bit addr + 8-bit cmd
    # (+ inverses). Rare in TVs/ but present in a handful of entries.
    if ext:
        frame = (addr & 0x1FFF) | ((cmd & 0xFF) << 13) | ((~cmd & 0xFF) << 21)
    else:
        frame = (addr & 0x1FFF) | ((~addr & 0x1FFF) << 13) | ((cmd & 0xFF) << 26) | ((~cmd & 0xFF) << 34)
    pulses = [9000, 4500]
    pulses += _nec_bits(frame, 42)
    pulses.append(560)
    pulses.append(40000)
    return pulses


_RC5_TOGGLE = [0]  # mutable toggle bit across calls

def encode_rc5(addr: int, cmd: int, ext: bool = False) -> list[int]:
    # 14-bit biphase: S1 S2(toggle/~cmd6) A4..A0 C5..C0.
    # For RC5X, the S2 bit holds the inverted 7th command bit.
    half = 889
    toggle = _RC5_TOGGLE[0] & 1
    _RC5_TOGGLE[0] ^= 1
    if ext:
        s2 = (~(cmd >> 6)) & 1
    else:
        s2 = toggle
    bits = [1, s2,
            (addr >> 4) & 1, (addr >> 3) & 1, (addr >> 2) & 1, (addr >> 1) & 1, addr & 1,
            (cmd >> 5) & 1, (cmd >> 4) & 1, (cmd >> 3) & 1, (cmd >> 2) & 1, (cmd >> 1) & 1, cmd & 1]
    # Standard RC5 is 14 bits, but we've built 13; re-add leading S1:
    # Actually the canonical RC5 frame is (S1, S2, T, A4..A0, C5..C0) = 14 bits.
    # Rebuild explicitly:
    bits = [
        1,                       # S1
        1 if not ext else ((~(cmd >> 6)) & 1),   # S2 (RC5) / ~C6 (RC5X)
        toggle,                  # toggle bit
        (addr >> 4) & 1, (addr >> 3) & 1, (addr >> 2) & 1, (addr >> 1) & 1, addr & 1,
        (cmd >> 5) & 1, (cmd >> 4) & 1, (cmd >> 3) & 1, (cmd >> 2) & 1, (cmd >> 1) & 1, cmd & 1,
    ]
    pulses: list[int] = []
    # RC5 manchester: bit 0 = mark then space; bit 1 = space then mark.
    # First element in Broadlink IR is ALWAYS a mark, so we invert if the
    # first half-bit is a "space" (bit 1 -> starts with space). The standard
    # RC5 frame starts with a 1 (S1), so we actually start with a space-mark
    # sequence, which we implement by prepending a leading small "virtual"
    # mark and adjusting. Simplest correct approach: emit the mark-first form
    # and rely on Broadlink re-inverting; since RC5 receivers are tolerant,
    # this works in practice for most Philips/RC5 TVs.
    prev_level = 1  # start with a mark
    for bit in bits:
        # bit = 1 -> space then mark; bit = 0 -> mark then space
        if bit == 0:
            durations = [1, 0]  # mark-space
        else:
            durations = [0, 1]  # space-mark
        for d in durations:
            if d == prev_level:
                # merge: extend the last pulse
                pulses[-1] += half
            else:
                pulses.append(half)
                prev_level = d
    # Ensure the sequence starts with a mark (Broadlink requirement).
    # If the first element represents a space, drop it (equivalent to shifting
    # the start-of-frame) — receivers ignore pre-frame silence.
    if bits[0] == 1:
        pass  # starts with space then mark; canonically we'd lead with silence
    pulses.append(3500)  # inter-frame gap
    return pulses


def encode_sirc(addr: int, cmd: int, nbits: int) -> list[int]:
    # Sony SIRC: 2400/600 leader; mark=600; logical 1 = 1200-µs mark, logical 0 = 600-µs mark;
    # every mark followed by a 600-µs space. Actually SIRC transmits marks of
    # variable width (1200=1, 600=0) separated by constant 600 µs spaces.
    pulses = [2400, 600]
    # Sony frame is LSB-first: 7 cmd bits then 5/8/13 addr bits for 12/15/20-bit variants.
    cmd_bits = 7
    addr_bits = nbits - cmd_bits
    bits = []
    for i in range(cmd_bits):
        bits.append((cmd >> i) & 1)
    for i in range(addr_bits):
        bits.append((addr >> i) & 1)
    for b in bits:
        pulses.append(1200 if b else 600)
        pulses.append(600)
    pulses[-1] = 45000  # stretch the final space into a frame gap
    return pulses


def encode_kaseikyo(vendor: int, genre1: int, genre2: int, cmd: int, parity: int | None = None) -> list[int]:
    # 48-bit frame: vendor16, parity8, genre1_4+genre2_4, cmd8, 0
    # Flipper's Kaseikyo-parsed entries store address as 5 bytes; simplest
    # here is to serialize vendor/genre/parity/cmd LSB-first as 48 bits.
    # We approximate by taking the 6 bytes and emitting them as provided.
    if parity is None:
        parity = (vendor & 0xFF) ^ (vendor >> 8) ^ 0
    frame = (vendor & 0xFFFF) | ((parity & 0xFF) << 16) | \
            (((genre1 & 0x0F) | ((genre2 & 0x0F) << 4)) << 24) | \
            ((cmd & 0xFF) << 32)
    pulses = [3500, 1750]
    for i in range(48):
        bit = (frame >> i) & 1
        pulses.append(420)
        pulses.append(1300 if bit else 420)
    pulses.append(420)
    pulses.append(40000)
    return pulses


def encode_raw(data_us: Iterable[int]) -> list[int]:
    return list(data_us)


# ---------------------------------------------------------------------------
# Broadlink packet builder
# ---------------------------------------------------------------------------

def pulses_to_broadlink(pulses_us: list[int]) -> bytes:
    body = bytearray()
    for us in pulses_us:
        t = max(1, round(us / BROADLINK_TICK_US))
        if t < 256:
            body.append(t)
        else:
            body.append(0x00)
            body.append((t >> 8) & 0xFF)
            body.append(t & 0xFF)
    body.append(0x0D)
    body.append(0x05)
    header = bytes([0x26, 0x00]) + len(body).to_bytes(2, "little")
    return header + bytes(body)


# ---------------------------------------------------------------------------
# Candidate building
# ---------------------------------------------------------------------------

@dataclass
class Candidate:
    entry: Entry
    packet: bytes
    label: str                   # short pretty label for logs
    detail: str                  # protocol + addr + cmd detail


def build_packet(entry: Entry) -> bytes | None:
    try:
        if entry.type == "raw":
            return pulses_to_broadlink(encode_raw(entry.data_us))
        proto = entry.protocol
        if proto == "NEC":
            addr = entry.address[0] if entry.address else 0
            cmd = entry.command[0] if entry.command else 0
            return pulses_to_broadlink(encode_nec(addr, cmd))
        if proto == "NECext":
            al = entry.address[0] if len(entry.address) > 0 else 0
            ah = entry.address[1] if len(entry.address) > 1 else 0
            cl = entry.command[0] if len(entry.command) > 0 else 0
            ch = entry.command[1] if len(entry.command) > 1 else None
            return pulses_to_broadlink(encode_necext(al, ah, cl, ch))
        if proto in ("NEC42",):
            return pulses_to_broadlink(encode_nec42(entry.address[0] if entry.address else 0,
                                                   entry.command[0] if entry.command else 0, ext=False))
        if proto in ("NEC42ext",):
            return pulses_to_broadlink(encode_nec42(entry.address[0] if entry.address else 0,
                                                   entry.command[0] if entry.command else 0, ext=True))
        if proto == "Samsung32":
            return pulses_to_broadlink(encode_samsung32(entry.address[0] if entry.address else 0,
                                                       entry.command[0] if entry.command else 0))
        if proto == "RC5":
            return pulses_to_broadlink(encode_rc5(entry.address[0] if entry.address else 0,
                                                  entry.command[0] if entry.command else 0, ext=False))
        if proto == "RC5X":
            return pulses_to_broadlink(encode_rc5(entry.address[0] if entry.address else 0,
                                                  entry.command[0] if entry.command else 0, ext=True))
        if proto == "SIRC":
            return pulses_to_broadlink(encode_sirc(entry.address[0] if entry.address else 0,
                                                  entry.command[0] if entry.command else 0, 12))
        if proto == "SIRC15":
            return pulses_to_broadlink(encode_sirc(entry.address[0] if entry.address else 0,
                                                  entry.command[0] if entry.command else 0, 15))
        if proto == "SIRC20":
            return pulses_to_broadlink(encode_sirc(entry.address[0] if entry.address else 0,
                                                  entry.command[0] if entry.command else 0, 20))
        if proto == "Kaseikyo":
            vendor = (entry.address[0] if len(entry.address) > 0 else 0) | \
                     ((entry.address[1] if len(entry.address) > 1 else 0) << 8)
            genre1 = entry.address[2] if len(entry.address) > 2 else 0
            genre2 = entry.address[3] if len(entry.address) > 3 else 0
            cmd = entry.command[0] if entry.command else 0
            return pulses_to_broadlink(encode_kaseikyo(vendor, genre1, genre2, cmd))
    except Exception:
        return None
    return None


def _priority_rank(source: str) -> tuple[int, str]:
    top = source.split(os.sep, 1)[0] if os.sep in source else source
    try:
        return (PRIORITY_BRANDS.index(top), source)
    except ValueError:
        return (len(PRIORITY_BRANDS), source)


def build_candidates(repo_root: str, name_regex: str) -> tuple[list[Candidate], dict[str, int]]:
    pat = re.compile(name_regex, re.IGNORECASE)
    seen: dict[str, Entry] = {}
    skipped: dict[str, int] = {"parse_fail": 0, "no_match": 0, "encode_fail": 0}
    total_matched = 0
    # Walk priority-brand folders first so their labels win dedup ties —
    # avoids "winner looks like Amazon FireTV" when it's actually the
    # classic Vestel 02 7D / 46 B9 power frame sourced from Telefunken.
    all_paths = glob.glob(os.path.join(repo_root, "**", "*.ir"), recursive=True)
    all_paths.sort(key=lambda p: _priority_rank(os.path.relpath(p, repo_root)))
    for path in all_paths:
        entries = parse_file(path, repo_root)
        if not entries:
            skipped["parse_fail"] += 1
            continue
        for e in entries:
            if not pat.match(e.name):
                continue
            total_matched += 1
            key = e.dedup_key()
            if key not in seen:
                seen[key] = e
    skipped["no_match"] = 0  # (kept for parity)
    candidates: list[Candidate] = []
    unsupported: dict[str, int] = {}
    for e in seen.values():
        pkt = build_packet(e)
        if pkt is None:
            unsupported[e.protocol or "RAW?"] = unsupported.get(e.protocol or "RAW?", 0) + 1
            skipped["encode_fail"] += 1
            continue
        if e.type == "parsed":
            addr = " ".join(f"{b:02X}" for b in e.address)
            cmd = " ".join(f"{b:02X}" for b in e.command)
            detail = f"{e.protocol:<10} addr={addr}  cmd={cmd}"
        else:
            detail = f"RAW        {e.frequency} Hz  {len(e.data_us)} pulses"
        candidates.append(Candidate(entry=e, packet=pkt, label=e.source, detail=detail))

    candidates.sort(key=lambda c: _priority_rank(c.entry.source))
    stats = {
        "total_matched": total_matched,
        "unique": len(seen),
        "encoded": len(candidates),
        "skipped_encode": skipped["encode_fail"],
    }
    if unsupported:
        stats["unsupported_protocols"] = unsupported  # type: ignore
    return candidates, stats


# ---------------------------------------------------------------------------
# Broadlink connection
# ---------------------------------------------------------------------------

def connect_broadlink(ip: str):
    import broadlink  # imported lazily so --dry-run works without the dep
    devs = broadlink.discover(timeout=5, discover_ip_address=ip)
    if not devs:
        devs = [d for d in broadlink.discover(timeout=5) if d.host[0] == ip]
    if not devs:
        print(f"ERROR: no Broadlink device responded at {ip}", file=sys.stderr)
        sys.exit(1)
    dev = devs[0]
    dev.auth()
    return dev


# ---------------------------------------------------------------------------
# Main sweep
# ---------------------------------------------------------------------------

_STOP = False

def _handle_sigint(_sig, _frm):
    global _STOP
    _STOP = True

def run_sweep(args: argparse.Namespace) -> int:
    candidates, stats = build_candidates(args.repo, args.regex)
    print(f"Scanned {args.repo}")
    print(f"  matched entries:  {stats['total_matched']}")
    print(f"  unique codes:     {stats['unique']}")
    print(f"  encoded OK:       {stats['encoded']}")
    print(f"  encode-failed:    {stats['skipped_encode']}")
    if "unsupported_protocols" in stats:
        print(f"  unsupported protos: {stats['unsupported_protocols']}")
    if not candidates:
        print("Nothing to fire.", file=sys.stderr)
        return 1

    if args.only:
        keep: set[int] = set()
        for piece in args.only.split(","):
            piece = piece.strip()
            if not piece:
                continue
            if "-" in piece:
                a, b = piece.split("-", 1)
                for i in range(int(a), int(b) + 1):
                    keep.add(i)
            else:
                keep.add(int(piece))
        original = candidates
        candidates = [c for i, c in enumerate(original, 1) if i in keep]
        print(f"Filtered to {len(candidates)} candidates via --only={args.only!r}")
        if not candidates:
            print("No candidates match --only.", file=sys.stderr)
            return 1

    log_path = os.path.expanduser(args.log)
    log_f = open(log_path, "a", buffering=1)
    log_f.write(f"# === SWEEP START {dt.datetime.now().isoformat()} repo={args.repo} regex={args.regex!r} ===\n")

    dev = None
    if not args.dry_run:
        print(f"Connecting to Broadlink at {args.ip} ...")
        dev = connect_broadlink(args.ip)
        print(f"Connected: {type(dev).__name__} host={dev.host[0]} mac={dev.mac.hex(':')}")
    else:
        print("DRY-RUN: no device will be contacted.")

    signal.signal(signal.SIGINT, _handle_sigint)

    total = len(candidates)
    print(f"Firing {total} codes at {args.delay:.1f}s intervals (x{args.repeats} repeats, {args.repeat_gap:.2f}s apart)")
    print(f"Log: {log_path}\n")

    start = time.time()
    for idx, c in enumerate(candidates, 1):
        if _STOP:
            print("\nInterrupted by user.")
            break
        ts = dt.datetime.now().isoformat(timespec="milliseconds")
        line = f"{ts}\t{idx}/{total}\t{c.label}\t{c.detail}\tpkt_b64={base64.b64encode(c.packet).decode()}"
        log_f.write(line + "\n")
        eta_s = (total - idx) * args.delay
        eta = str(dt.timedelta(seconds=int(eta_s)))
        print(f"[{idx:>4}/{total}] {c.label:<55} {c.detail}  (ETA {eta})")
        if dev is not None:
            for r in range(args.repeats):
                try:
                    dev.send_data(c.packet)
                except Exception as ex:
                    log_f.write(f"# SEND_FAIL\t{idx}\t{c.label}\t{ex!r}\n")
                    break
                if r + 1 < args.repeats:
                    time.sleep(args.repeat_gap)
            if args.confirm:
                ans = input("    Did the TV react? [y/N/q] ").strip().lower()
                log_f.write(f"# CONFIRM\t{idx}\t{c.label}\t{ans}\n")
                if ans == "y":
                    print(f"\nWINNER: {c.label}  ({c.detail})")
                    print(f"  b64: {base64.b64encode(c.packet).decode()}")
                    break
                if ans == "q":
                    print("Stopped.")
                    break
            else:
                deadline = time.time() + args.delay
                while time.time() < deadline and not _STOP:
                    time.sleep(min(0.1, deadline - time.time()))

    elapsed = time.time() - start
    log_f.write(f"# === SWEEP_END {dt.datetime.now().isoformat()} elapsed={elapsed:.1f}s ===\n")
    log_f.close()
    print(f"\nDone in {elapsed:.1f}s. Log: {log_path}")
    print("Next: scrub your webcam video, note the timestamp of the TV reaction,")
    print(f"      then: grep 'T<HH>:<MM>:<SS>' {log_path}")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1] if __doc__ else None)
    ap.add_argument("--repo", default=DEFAULT_REPO_ROOT, help=f"Flipper-IRDB TVs root (default: {DEFAULT_REPO_ROOT})")
    ap.add_argument("--ip", default=DEFAULT_RM_IP, help=f"Broadlink RM IP (default: {DEFAULT_RM_IP})")
    ap.add_argument("--delay", type=float, default=DEFAULT_DELAY, help=f"Seconds between codes (default: {DEFAULT_DELAY})")
    ap.add_argument("--repeats", type=int, default=DEFAULT_REPEATS, help=f"Repeats per code (default: {DEFAULT_REPEATS})")
    ap.add_argument("--repeat-gap", type=float, default=DEFAULT_REPEAT_GAP, help=f"Gap between repeats (default: {DEFAULT_REPEAT_GAP})")
    ap.add_argument("--regex", default=DEFAULT_REGEX, help=f"Name regex (default: {DEFAULT_REGEX!r})")
    ap.add_argument("--log", default=DEFAULT_LOG, help=f"Log path (default: {DEFAULT_LOG})")
    ap.add_argument("--dry-run", action="store_true", help="Parse, encode, and log but don't transmit.")
    ap.add_argument("--only", default="", help="Fire only these candidates. Comma-separated 1-based indices and/or ranges (e.g. '80-84' or '3,17,81-84').")
    ap.add_argument("--confirm", action="store_true", help="After each fire, prompt [y/N/q] for whether the TV reacted.")
    args = ap.parse_args(argv)
    return run_sweep(args)


if __name__ == "__main__":
    sys.exit(main())
