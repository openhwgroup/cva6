#!/usr/bin/env python3
# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
#
# Turns the tracer's `binary` output into a Perfetto trace showing what the
# software did: a flame chart of the call stack, the privilege level over time,
# a track of traps and interrupts, and an IPC counter.
#
#   ./build/Vtest +binary=prog.hex +trace_format=binary +trace_file=trace.bin
#   ./util/trace_to_perfetto.py trace.bin prog.elf -o trace.pftrace
#
# Then open trace.pftrace at https://ui.perfetto.dev.
#
# Everything this needs is already in the binary record, so it runs on a trace
# that has already been taken and changing what is plotted costs a re-run of the
# script. The fixed records parse with no work, they are in execution order, and
# the `class` byte carries what the instruction is, so no RISC-V decoding happens
# here.
#
# The whole file is loaded with numpy in one call and the per record work is
# vectorised, because a trace is one record per retired instruction while the
# points where anything changes are a small fraction of them. The dtype below is
# the one `read_trace.py`'s docstring gives.
#
# Frames are reconstructed from which symbol the pc falls in, which attributes
# the tail calls that are common at -O2 to the callee. The rules, in order:
#
#   - the record after a call (a jump that writes a link register) opens a frame
#   - a symbol already on the stack closes frames until it is on top, which also
#     recovers from returns that were missed
#   - any other change of symbol replaces the top frame, which is the tail call
#     case
#
# Traps open a frame of their own and `mret`/`sret` closes it, so a handler
# nests inside the interrupted function. The frame is named after the cause,
# which comes from the CSR records the tracer writes.

import argparse
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from perfetto_proto import TraceWriter  # noqa: E402
from read_trace import HEADER_SIZE, read_header  # noqa: E402

# Record fields, from read_trace.py's layout
KIND_TRAP = 1
KIND_CSR = 2
CLASS_JUMP = 0x20
FLAG_MISPREDICT = 0x01
FLAG_TRAP_ENTRY = 0x02
FLAG_INTERRUPT = 0x04
FLAG_VIRT = 0x20

# ra and t0 are the ABI's link registers, so a jump writing one of them is a
# call and a jump reading one of them with no destination is a return.
LINK_REGS = (1, 5)

MRET = 0x30200073
SRET = 0x10200073
ECALL = 0x00000073

# The cause registers a handler of each privilege reads: machine mode mcause,
# supervisor mode scause, or vscause when it runs virtualised.
CAUSE_CSRS = {3: (0x342,), 1: (0x142, 0x242)}

EXCEPTION_NAMES = {
    0: "instruction address misaligned", 1: "instruction access fault",
    2: "illegal instruction", 3: "breakpoint", 4: "load address misaligned",
    5: "load access fault", 6: "store address misaligned", 7: "store access fault",
    8: "ecall from U", 9: "ecall from S", 10: "ecall from VS", 11: "ecall from M",
    12: "instruction page fault", 13: "load page fault", 15: "store page fault",
    20: "instruction guest page fault", 21: "load guest page fault",
    22: "virtual instruction", 23: "store guest page fault",
}
INTERRUPT_NAMES = {
    1: "supervisor software", 2: "virtual supervisor software", 3: "machine software",
    5: "supervisor timer", 6: "virtual supervisor timer", 7: "machine timer",
    9: "supervisor external", 10: "virtual supervisor external", 11: "machine external",
    12: "supervisor guest external",
}

# The mode a record ran in: the privilege level with the virtualisation bit
# above it, because the privilege level alone cannot tell HS from VS or U from VU.
MODE_NAMES = {0: "U", 1: "S", 2: "D", 3: "M", 4: "VU", 5: "VS"}


def mode_codes(d):
    return (d["priv"] & 3) | ((d["flags"] & FLAG_VIRT) != 0) * 4

NO_SYMBOL = "<no symbol>"

# The record layout, exactly as documented in read_trace.py.
RECORD_FIELDS = [
    ('cycle', '<u8'), ('time_ns', '<u8'), ('pc', '<u8'), ('rd_wdata', '<u8'),
    ('rs1_rdata', '<u8'), ('rs2_rdata', '<u8'), ('mem_vaddr', '<u8'),
    ('mem_paddr', '<u8'), ('mem_wdata', '<u8'), ('mem_rdata', '<u8'),
    ('insn', '<u4'), ('kind', 'u1'), ('priv', 'u1'), ('flags', 'u1'),
    ('rd_addr', 'u1'), ('rs1_addr', 'u1'), ('rs2_addr', 'u1'),
    ('commit_port', 'u1'), ('mem_rmask', 'u1'), ('mem_wmask', 'u1'),
    ('class', 'u1'), ('csr', '<u2'),
]
BASE_RECORD_SIZE = 96


# ---------------------------------------------------------------------------
# ELF symbols
#
# The symbol table is a little struct work and is read once, so it is parsed
# here. pyelftools is the way in if line level DWARF attribution is ever wanted.
# ---------------------------------------------------------------------------

SHT_SYMTAB = 2
STT_FUNC = 2
STT_NOTYPE = 0
SHF_EXECINSTR = 0x4
SHN_LORESERVE = 0xFF00


def read_symbols(paths):
    """Function symbols from one or more ELF files, as a list of (start, end,
    name) sorted by start. A zero sized symbol runs to the next one."""
    import struct

    syms = []
    for path in paths:
        syms.extend(_read_one_elf(path, struct))
    syms.sort(key=lambda s: s[0])

    out = []
    for i, (addr, size, name) in enumerate(syms):
        end = addr + size
        if size == 0:
            end = syms[i + 1][0] if i + 1 < len(syms) else addr + 4
        out.append((addr, end, name))
    return out


def _read_one_elf(path, struct):
    with open(path, "rb") as handle:
        blob = handle.read()

    if blob[:4] != b"\x7fELF":
        sys.exit(f"error: {path} is not an ELF file")
    if blob[5] != 1:
        sys.exit(f"error: {path} is not little endian, which is all this reads")
    is64 = blob[4] == 2

    if is64:
        shoff = struct.unpack_from("<Q", blob, 0x28)[0]
        shentsize, shnum = struct.unpack_from("<HH", blob, 0x3A)
        sh_fmt, sym_fmt, sym_size = "<IIQQQQIIQQ", "<IBBHQQ", 24
    else:
        shoff = struct.unpack_from("<I", blob, 0x20)[0]
        shentsize, shnum = struct.unpack_from("<HH", blob, 0x2E)
        sh_fmt, sym_fmt, sym_size = "<IIIIIIIIII", "<IIIBBH", 16

    sections = []
    for i in range(shnum):
        sections.append(struct.unpack_from(sh_fmt, blob, shoff + i * shentsize))

    # Anything living in an executable section counts as code, which keeps the
    # handlers in the hand written assembly under sw/tests/ — their labels carry
    # no .type directive, so they arrive as STT_NOTYPE — and drops ABS constants.
    executable = {i for i, s in enumerate(sections) if s[2] & SHF_EXECINSTR}

    out = []
    for sh_name, sh_type, _, _, sh_off, sh_size, sh_link, *_ in sections:
        if sh_type != SHT_SYMTAB:
            continue
        str_off = sections[sh_link][4]
        for off in range(sh_off, sh_off + sh_size, sym_size):
            fields = struct.unpack_from(sym_fmt, blob, off)
            if is64:
                st_name, st_info, _, st_shndx, st_value, st_size = fields
            else:
                st_name, st_value, st_size, st_info, _, st_shndx = fields
            if (st_info & 0xF) not in (STT_FUNC, STT_NOTYPE) or st_value == 0:
                continue
            if st_shndx >= SHN_LORESERVE or st_shndx not in executable:
                continue
            end = blob.index(b"\0", str_off + st_name)
            name = blob[str_off + st_name:end].decode(errors="replace")
            # `$x...`/`$d...` are RISC-V mapping symbols marking ISA and data
            # changes. They sit on top of real labels and would shadow them.
            if name and not name.startswith("$"):
                out.append((st_value, st_size, name))
    return out


def symbol_index(pc, syms):
    """Which symbol each pc falls in, as an index into `syms`, or -1. One
    searchsorted over the whole trace."""
    if not syms:
        return np.full(len(pc), -1, dtype=np.int64)
    starts = np.array([s[0] for s in syms], dtype=np.uint64)
    ends = np.array([s[1] for s in syms], dtype=np.uint64)
    idx = np.searchsorted(starts, pc, side="right").astype(np.int64) - 1
    safe = np.clip(idx, 0, None)
    inside = (idx >= 0) & (pc < ends[safe])
    return np.where(inside, idx, -1)


# ---------------------------------------------------------------------------
# Loading
# ---------------------------------------------------------------------------

def load(path):
    """Header, the retirements and traps, and the CSR writes with, for each,
    the index of the record it comes before. One read."""
    with open(path, "rb") as handle:
        head = read_header(handle)

    fields = list(RECORD_FIELDS)
    extra = head["record_size"] - BASE_RECORD_SIZE
    if extra > 0:
        # a newer writer may use longer records; the fields we know keep their
        # place, exactly as read_trace.py handles it
        fields.append(("_tail", f"V{extra}"))
    elif extra < 0:
        sys.exit(f"error: record size {head['record_size']} is smaller than the "
                 f"{BASE_RECORD_SIZE} bytes this knows about")

    data = np.fromfile(path, dtype=np.dtype(fields), offset=HEADER_SIZE)
    is_csr = data["kind"] == KIND_CSR
    before = np.cumsum(~is_csr)[is_csr]
    return head, data[~is_csr], data[is_csr], before


# ---------------------------------------------------------------------------
# Trap causes
# ---------------------------------------------------------------------------

def cause_name(cause, xlen):
    """`irq machine timer`, `irq 31` or `trap illegal instruction`. The code is
    the low 12 bits: in CLIC mode the bits above it hold the saved interrupt
    level and privilege, and the code is the CLIC interrupt line."""
    code = cause & 0xFFF
    if (cause >> (xlen - 1)) & 1:
        return f"irq {INTERRUPT_NAMES.get(code, code)}"
    return f"trap {EXCEPTION_NAMES.get(code, code)}"


def trap_entries(d, csr, before, xlen):
    """The records that open a trap frame, and the frame's name, as a dict.

    CVA6 flags the first instruction of a handler, except after an ecall, which
    it reports as a retirement; there the record after it opens the frame. The
    cause is the latest write of the cause register the handler's privilege
    reads, from the CSR records. With no such write before it, an exception
    takes the cause of the latest trap record and an interrupt is plain `irq`.
    """
    n = len(d)
    flagged = (d["flags"] & FLAG_TRAP_ENTRY) != 0
    after_ecall = np.zeros(n, dtype=bool)
    after_ecall[1:] = (d["insn"][:-1] == ECALL) & (d["kind"][:-1] != KIND_TRAP)
    entries = np.flatnonzero(flagged | after_ecall)

    names = {}
    for priv, addrs in CAUSE_CSRS.items():
        mine = entries[(d["priv"][entries] & 3) == priv]
        writes = np.flatnonzero(np.isin(csr["csr"], addrs))
        last = np.searchsorted(before[writes], mine, side="right") - 1
        for i, j in zip(mine, last):
            if j >= 0:
                names[int(i)] = cause_name(int(csr["rd_wdata"][writes[j]]), xlen)

    traps = np.flatnonzero(d["kind"] == KIND_TRAP)
    for i in entries:
        if int(i) in names:
            continue
        if flagged[i] and d["flags"][i] & FLAG_INTERRUPT:
            names[int(i)] = "irq"
        elif flagged[i]:
            j = np.searchsorted(traps, i) - 1
            names[int(i)] = (cause_name(int(d["rd_wdata"][traps[j]]), xlen)
                             if j >= 0 else "trap")
        else:
            names[int(i)] = f"trap ecall from {MODE_NAMES.get(int(mode_codes(d)[i - 1]), '?')}"
    return names


# ---------------------------------------------------------------------------
# Frame reconstruction
# ---------------------------------------------------------------------------

class Frames:
    """The call stack as the trace walks over it.

    Only fed the records where something can change: where the pc moves into a
    different symbol, where a trap is flagged, and the record after an `mret` or
    `sret`. Everywhere else the top of the stack already names the current
    symbol and there is nothing to do, which is what makes it cheap to skip the
    rest.
    """

    def __init__(self, names):
        self._names = names
        self.stack = []  # (name, is_trap), innermost last

    def name_of(self, sym):
        return self._names[sym] if sym >= 0 else NO_SYMBOL

    def step(self, ts, sym, trap, prev_insn, prev_is_call):
        """Yields ("push", ts, name) and ("pop", ts) for one record. `trap` names
        the trap frame this record opens, if it opens one."""
        stack = self.stack
        force_push = False

        # Returning from a handler closes the handler's frames and the trap
        # frame that opened them. Only when a trap frame is actually open: these
        # tests also use `sret` to *enter* supervisor mode during setup, and
        # unwinding there would wrongly empty the stack.
        if prev_insn in (MRET, SRET) and any(t for _, t in stack):
            while stack:
                was_trap = stack[-1][1]
                yield ("pop", ts)
                stack.pop()
                if was_trap:
                    break

        # The trap frame opens on the first instruction of the handler, before
        # this record's symbol is placed, so the handler nests inside it.
        if trap:
            stack.append((trap, True))
            yield ("push", ts, trap)
            force_push = True

        name = self.name_of(sym)
        names = [s[0] for s in stack]

        if not stack:
            stack.append((name, False))
            yield ("push", ts, name)
        elif name != names[-1]:
            if force_push or prev_is_call:
                stack.append((name, False))
                yield ("push", ts, name)
            elif name in names:
                while stack and stack[-1][0] != name:
                    yield ("pop", ts)
                    stack.pop()
            else:
                # a tail call, or a transfer we cannot account for: replacing the
                # frame keeps the depth stable
                yield ("pop", ts)
                stack.pop()
                stack.append((name, False))
                yield ("push", ts, name)

    def close(self, ts):
        for _ in self.stack:
            yield ("pop", ts)
        self.stack.clear()


def frame_points(d, sym, traps):
    """Record indices where the frame state machine has to run."""
    n = len(d)
    if n == 0:
        return np.empty(0, dtype=np.int64)

    interesting = np.zeros(n, dtype=bool)
    interesting[0] = True
    interesting[1:] |= sym[1:] != sym[:-1]
    interesting[list(traps)] = True
    ret = (d["insn"] == MRET) | (d["insn"] == SRET)
    interesting[1:] |= ret[:-1]
    return np.flatnonzero(interesting)


def frame_events(d, sym, names, traps, timestamps):
    """Every frame event in the trace, as (record index, kind, ts[, name]).

    The record index is carried so these merge against the other tracks in the
    order a single pass over the records produces.
    """
    frames = Frames(names)
    is_jump = (d["class"] & CLASS_JUMP) != 0
    calls = is_jump & np.isin(d["rd_addr"], LINK_REGS)

    for i in frame_points(d, sym, traps):
        prev_insn = int(d["insn"][i - 1]) if i else 0
        prev_call = bool(calls[i - 1]) if i else False
        ts = int(timestamps[i])
        for ev in frames.step(ts, int(sym[i]), traps.get(int(i)),
                              prev_insn, prev_call):
            yield (int(i),) + ev

    # whatever is still open runs to the end of the trace, not to the last
    # point the stack happened to change
    last = int(timestamps[-1]) if len(d) else 0
    for ev in frames.close(last):
        yield (len(d),) + ev


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def convert(args, head, d, traps, syms, out):
    writer = TraceWriter(out, uuid_base=args.uuid_base)
    root = writer.track(f"CVA6 hart {head['hart_id']}")
    stack_track = writer.track("Call stack", parent=root,
                               description="frames from the pc's symbol")
    mode_track = writer.track("Mode", parent=root)
    trap_track = writer.track("Traps", parent=root)
    ipc_track = writer.counter_track("IPC", parent=root, unit_name="insn/cycle")

    timestamps = d["cycle"] if args.time_unit == "cycle" else d["time_ns"]
    names = [s[2] for s in syms]
    sym = symbol_index(d["pc"], syms)
    n = len(d)

    # Everything that is a simple function of the records is computed over the
    # whole trace at once; only the frame stack needs a walk.
    retired = (d["kind"] != KIND_TRAP)
    n_insn = int(retired.sum())
    mispredicts = int(((d["flags"] & FLAG_MISPREDICT) != 0).sum())

    modes = mode_codes(d)
    mode_changed = np.zeros(n, dtype=bool)
    if n:
        mode_changed[0] = True
        mode_changed[1:] = modes[1:] != modes[:-1]
    mode_points = np.flatnonzero(mode_changed & retired)

    ipc_points, ipc_values = _ipc(d, retired, args.ipc_window)

    # Everything is merged on the record it came from, and within a record the
    # record's own tracks come first, then the frames it opens or closes.
    events = []
    for i, name in traps.items():
        events.append((i, 0, "trap", name, 0))
    for i in mode_points:
        events.append((int(i), 1, "mode", int(modes[i]), 0))
    for i, v in zip(ipc_points, ipc_values):
        events.append((int(i), 2, "ipc", float(v), 0))
    n_frames = 0
    for idx, kind, ts, *rest in frame_events(d, sym, names, traps, timestamps):
        events.append((idx, 3, kind, rest[0] if rest else None, ts))
        n_frames += kind == "push"
    events.sort(key=lambda e: (e[0], e[1]))

    mode_open = False
    for idx, rank, kind, payload, frame_ts in events:
        if rank == 3:
            if kind == "push":
                writer.slice_begin(stack_track, frame_ts, payload)
            else:
                writer.slice_end(stack_track, frame_ts)
            continue
        ts = int(timestamps[idx])
        if kind == "trap":
            writer.instant(trap_track, ts, payload)
        elif kind == "mode":
            if mode_open:
                writer.slice_end(mode_track, ts)
            writer.slice_begin(mode_track, ts, MODE_NAMES.get(payload, "?"))
            mode_open = True
        else:
            writer.counter_float(ipc_track, ts, payload)

    if mode_open and n:
        writer.slice_end(mode_track, int(timestamps[-1]))

    return dict(insn=n_insn, traps=len(traps), frames=n_frames,
                mispredicts=mispredicts)


def _ipc(d, retired, window):
    """IPC sampled every `window` retired instructions, as (indices, values)."""
    idx = np.flatnonzero(retired)
    if window < 1 or len(idx) < window:
        return np.empty(0, dtype=np.int64), np.empty(0)

    n_win = len(idx) // window
    ends = idx[window - 1: n_win * window: window]
    starts = np.concatenate(([idx[0]], ends[:-1]))
    span = d["cycle"][ends].astype(np.int64) - d["cycle"][starts].astype(np.int64)
    good = span > 0
    return ends[good], window / span[good]


def dump_frames(d, traps, syms, timestamps, out):
    """Indented text of the same frames, for checking the nesting by eye."""
    names = [s[2] for s in syms]
    sym = symbol_index(d["pc"], syms)
    depth = 0
    for _, kind, ts, *rest in frame_events(d, sym, names, traps, timestamps):
        if kind == "push":
            # timestamp first at a fixed width, then the indent, so the depth
            # stays readable however wide the timestamp gets
            print(f"{ts:>10}  {'  ' * depth}{rest[0]}", file=out)
            depth += 1
        else:
            depth = max(0, depth - 1)


def main():
    p = argparse.ArgumentParser(
        description="convert a binary tracer trace to a Perfetto trace")
    p.add_argument("trace", help="the tracer's binary output")
    p.add_argument("elf", nargs="*", help="ELF files to take symbols from")
    p.add_argument("-o", "--output", help="where to write the .pftrace")
    p.add_argument("--time-unit", choices=("cycle", "ns"), default="cycle",
                   help="what the Perfetto time axis counts (default: cycle)")
    p.add_argument("--ipc-window", type=int, default=64,
                   help="retired instructions per IPC sample (default: 64)")
    p.add_argument("--uuid-base", type=int, default=1,
                   help="first track uuid, so a second producer's trace can be "
                        "concatenated without colliding (default: 1)")
    p.add_argument("--debug-frames", action="store_true",
                   help="print the frames as indented text instead")
    args = p.parse_args()

    syms = read_symbols(args.elf) if args.elf else []
    if not args.elf:
        print("note: no ELF given, every frame will be " + NO_SYMBOL,
              file=sys.stderr)

    head, d, csr, before = load(args.trace)
    traps = trap_entries(d, csr, before, head["xlen"])

    if args.debug_frames:
        timestamps = d["cycle"] if args.time_unit == "cycle" else d["time_ns"]
        dump_frames(d, traps, syms, timestamps, sys.stdout)
        return 0

    if not args.output:
        sys.exit("error: -o is required unless --debug-frames is given")

    with open(args.output, "wb") as out:
        counts = convert(args, head, d, traps, syms, out)

    rate = (100.0 * counts["mispredicts"] / counts["insn"]) if counts["insn"] else 0.0
    print(f"{counts['insn']} instructions, {counts['traps']} traps, "
          f"{counts['frames']} frames, {counts['mispredicts']} mispredicts "
          f"({rate:.1f}%)", file=sys.stderr)
    print(f"wrote {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
