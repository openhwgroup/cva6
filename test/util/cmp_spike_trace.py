#!/usr/bin/env python3
# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
#
# Compare a spike commit log against one produced by the CVA6 tracer in `spike`
# format, and report the first place they disagree.
#
#   spike --isa=rv64imac_zicsr -l --log-commits prog.elf > spike.log 2>&1
#   ./build/Vtest +binary=prog.hex +trace_format=spike +trace_file=rtl.log
#   ./util/cmp_spike_trace.py spike.log rtl.log
#
# The two runs do not start in the same place -- spike begins at its own reset
# vector while the testbench goes through its boot ROM -- so the logs are
# aligned on the first program counter they have in common, or on --start-pc.

import argparse
import re
import sys

# `core   0: 0x<pc> (0x<insn>) <disassembly>`
INSN_RE = re.compile(r"^core\s+\d+:\s+0x([0-9a-f]+)\s+\(0x([0-9a-f]+)\)\s*(.*)$")
# `core   0: <priv> 0x<pc> (0x<insn>) [x<n> 0x<val>] [mem 0x<addr> [0x<val>]]`
EFF_RE = re.compile(r"^(?:core\s+\d+:\s+)?(\d)\s+0x([0-9a-f]+)\s+\(0x([0-9a-f]+)\)(.*)$")
# a CSR write record, `c768_mstatus 0x...`
CSR_RE = re.compile(r"\bc\d+_\w+\s+0x[0-9a-f]+")
# the fflags record in particular
FFLAGS_RE = re.compile(r"\bc1_fflags\s+0x([0-9a-f]+)")


class Entry:
    __slots__ = ("pc", "insn", "disasm", "priv", "effect", "line")

    def __init__(self, pc, insn, disasm, line):
        self.pc, self.insn, self.disasm, self.line = pc, insn, disasm, line
        self.priv, self.effect = None, ""

    def key(self, with_disasm):
        k = (self.pc, self.insn, self.effect)
        return k + (self.disasm,) if with_disasm and self.disasm else k

    def __str__(self):
        d = f"  {self.disasm}" if self.disasm else ""
        e = f"  [{self.effect}]" if self.effect else "  [no write]"
        return f"0x{self.pc:016x} (0x{self.insn:08x}){d}{e}"


def normalise(effect, with_csrs):
    """Strip the differences that are spelling, not behaviour."""
    if not with_csrs:
        effect = CSR_RE.sub("", effect)
    effect = re.sub(r"\b([xf])\s*(\d+)", r"\1\2", effect)  # `x 5` / `x5 ` -> `x5`
    return " ".join(effect.split())


def drop_repeated_fflags(entries):
    """Spike records fflags on every instruction that raises a flag, and RVFI
    reports a CSR only when its value changes. The flags are sticky, so the two
    differ exactly where a record repeats the value fflags already holds; such
    a record is left out on both sides."""
    current = 0
    for e in entries:
        m = FFLAGS_RE.search(e.effect)
        if not m:
            continue
        value = int(m.group(1), 16)
        if value == current:
            e.effect = " ".join(FFLAGS_RE.sub("", e.effect).split())
        current = value
    return entries


def parse(path, with_csrs):
    """Read a commit log into a list of Entry, in execution order.

    An instruction is normally two lines, but spike drops the disassembly line
    in tight loops and prints only the commit, so an unpaired commit line has to
    stand on its own rather than be discarded.
    """
    out = []
    with open(path, errors="replace") as handle:
        for line in handle:
            line = line.rstrip("\n")
            m = EFF_RE.match(line)
            if m:
                pc, insn = int(m.group(2), 16), int(m.group(3), 16)
                if not (out and out[-1].priv is None and out[-1].pc == pc):
                    out.append(Entry(pc, insn, "", line))   # commit without disassembly
                out[-1].priv = int(m.group(1))
                out[-1].effect = normalise(m.group(4), with_csrs)
                continue
            m = INSN_RE.match(line)
            if m:
                out.append(Entry(int(m.group(1), 16), int(m.group(2), 16),
                                 " ".join(m.group(3).split()), line))
    return out


def align(a, b, start_pc):
    """Index into each list where the comparison should begin."""
    if start_pc is not None:
        ia = next((i for i, e in enumerate(a) if e.pc == start_pc), None)
        ib = next((i for i, e in enumerate(b) if e.pc == start_pc), None)
        if ia is None or ib is None:
            sys.exit(f"error: pc 0x{start_pc:x} does not appear in "
                     f"{'the first log' if ia is None else 'the second log'}")
        return ia, ib, start_pc
    seen = {e.pc for e in b}
    for i, e in enumerate(a):
        if e.pc in seen:
            return i, next(j for j, f in enumerate(b) if f.pc == e.pc), e.pc
    sys.exit("error: the two logs have no program counter in common")


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("spike_log", help="log from spike -l --log-commits")
    p.add_argument("trace_log", help="log from the tracer in spike format")
    p.add_argument("--start-pc", type=lambda v: int(v, 0), default=None,
                   help="align both logs on this pc instead of the first common one")
    p.add_argument("--limit", type=int, default=0,
                   help="stop after this many instructions (0 = no limit)")
    p.add_argument("--max-diffs", type=int, default=10, help="how many differences to print")
    p.add_argument("--ignore-disasm", action="store_true",
                   help="compare behaviour only, leaving the disassembly text out")
    p.add_argument("--ignore-csr", action="store_true",
                   help="leave the CSR write records out of the comparison")
    p.add_argument("-q", "--quiet", action="store_true", help="only report the verdict")
    args = p.parse_args()

    spike = drop_repeated_fflags(parse(args.spike_log, not args.ignore_csr))
    trace = drop_repeated_fflags(parse(args.trace_log, not args.ignore_csr))
    if not spike or not trace:
        sys.exit(f"error: no commit log entries in "
                 f"{args.spike_log if not spike else args.trace_log}")

    ia, ib, pc = align(spike, trace, args.start_pc)
    n = min(len(spike) - ia, len(trace) - ib)
    if args.limit:
        n = min(n, args.limit)
    if not args.quiet:
        print(f"aligned on pc 0x{pc:x}: spike entry {ia}, trace entry {ib}")
        print(f"comparing {n} instructions"
              f" (spike has {len(spike) - ia} from here, trace has {len(trace) - ib})")

    diffs = 0
    for k in range(n):
        a, b = spike[ia + k], trace[ib + k]
        if a.key(not args.ignore_disasm) == b.key(not args.ignore_disasm):
            continue
        diffs += 1
        if not args.quiet and diffs <= args.max_diffs:
            print(f"\n#{k} diverges:")
            print(f"  spike {a}")
            print(f"  trace {b}")
        if diffs > args.max_diffs and not args.quiet:
            print(f"\n... stopping after {args.max_diffs} differences")
            break

    if diffs:
        print(f"DIFFER: {diffs} of {n} instructions")
        return 1
    ignored = [what for what, flag in (("disassembly text", args.ignore_disasm),
                                       ("csr records", args.ignore_csr)) if flag]
    print(f"MATCH: {n} instructions identical"
          f"{' (' + ' and '.join(ignored) + ' ignored)' if ignored else ''}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
