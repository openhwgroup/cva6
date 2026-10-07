#!/usr/bin/env python3
# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
#
# Reference reader for the tracer's `binary` output format, and a converter to
# CSV. The layout is documented here because this file is meant to be the thing
# you copy from when writing your own tool.
#
#   ./build/Vtest +binary=prog.hex +trace_format=binary +trace_file=trace.bin
#   ./util/read_trace.py trace.bin --csv > trace.csv
#
# HEADER, 64 bytes, little endian, once at the start of the file
#
#   off  size  field
#   0    8     magic, "CVA6TRC\0"
#   8    2     version, currently 1
#   10   2     record_size, currently 96
#   12   1     xlen, 32 or 64
#   13   1     vlen, virtual address width in bits
#   14   1     plen, physical address width in bits
#   15   1     hart_id
#   16   48    reserved, zero
#
# RECORD, `record_size` bytes each, one per event, in execution order
#
#   off  size  field        meaning when kind == 1 (trap)    kind == 2 (csr)
#   0    8     cycle
#   8    8     time_ns
#   16   8     pc                                          of the event it goes with
#   24   8     rd_wdata     cause                          value after the write
#   32   8     rs1_rdata    tval
#   40   8     rs2_rdata    unused
#   48   8     mem_vaddr    unused
#   56   8     mem_paddr    unused
#   64   8     mem_wdata    unused
#   72   8     mem_rdata    unused
#   80   4     insn
#   84   1     kind         0 = retirement, 1 = trap, 2 = csr write
#   85   1     priv         0 user, 1 supervisor, 2 debug, 3 machine
#   86   1     flags        bit 0 mispredict, 1 trap entry, 2 interrupt,
#                           3 resolved branch, 4 branch taken, 5 virtualised
#   87   1     rd_addr
#   88   1     rs1_addr
#   89   1     rs2_addr
#   90   1     commit_port
#   91   1     mem_rmask    byte enables of a load
#   92   1     mem_wmask    byte enables of a store
#   93   1     class        what the instruction is:
#                           bit 0 load, 1 store, 2 atomic, 3 csr, 4 branch,
#                           5 jump, 6 compressed
#   94   2     csr          address of the CSR a csr record writes
#
# New fields keep the offsets of the existing ones and take space from
# `reserved`, so a reader that checks `version` and `record_size` keeps working.
# `class` is written by the tracer's own decoder, so counting an instruction mix
# needs no RISC-V decoding here.
#
# A csr record follows the retirement or trap that made the write, with the
# same cycle. A write made in a cycle with neither, such as the entry into an
# interrupt handler, comes ahead of the next retirement or trap, with its own
# cycle and that event's pc.
#
# With numpy the whole file is one call, no parsing:
#
#   import numpy as np
#   rec = np.dtype([('cycle','<u8'), ('time_ns','<u8'), ('pc','<u8'),
#                   ('rd_wdata','<u8'), ('rs1_rdata','<u8'), ('rs2_rdata','<u8'),
#                   ('mem_vaddr','<u8'), ('mem_paddr','<u8'), ('mem_wdata','<u8'),
#                   ('mem_rdata','<u8'), ('insn','<u4'), ('kind','u1'),
#                   ('priv','u1'), ('flags','u1'), ('rd_addr','u1'),
#                   ('rs1_addr','u1'), ('rs2_addr','u1'), ('commit_port','u1'),
#                   ('mem_rmask','u1'), ('mem_wmask','u1'), ('class','u1'),
#                   ('csr','<u2')])
#   data = np.fromfile('trace.bin', dtype=rec, offset=64)
#   mispredicted = data[(data['flags'] & 0x09) == 0x09]   # branch that missed
#   loads        = data[(data['kind'] == 0) & (data['class'] & 0x01 != 0)]  # no decoder needed

import argparse
import struct
import sys

MAGIC = b"CVA6TRC\0"
HEADER_FMT = "<8sHHBBBB48s"
HEADER_SIZE = 64
RECORD_FMT = "<10QIBBBBBBBBBBH"
FIELDS = ("cycle", "time_ns", "pc", "rd_wdata", "rs1_rdata", "rs2_rdata", "mem_vaddr",
          "mem_paddr", "mem_wdata", "mem_rdata", "insn", "kind", "priv", "flags",
          "rd_addr", "rs1_addr", "rs2_addr", "commit_port", "mem_rmask", "mem_wmask",
          "class", "csr")
CLASS_NAMES = ((0x01, "load"), (0x02, "store"), (0x04, "amo"), (0x08, "csr"),
               (0x10, "branch"), (0x20, "jump"), (0x40, "compressed"))
LATEST_VERSION = 1

PRIV = {0: "U", 1: "S", 2: "D", 3: "M"}
VIRT_PRIV = {0: "VU", 1: "VS"}
FLAG_VIRT = 0x20
FLAG_NAMES = ((0x01, "mispredict"), (0x02, "trap-entry"), (0x04, "interrupt"),
              (0x08, "branch"), (0x10, "taken"), (0x20, "virt"))


def read_header(handle):
    raw = handle.read(HEADER_SIZE)
    if len(raw) < HEADER_SIZE:
        sys.exit("error: file is shorter than the header")
    magic, version, record_size, xlen, vlen, plen, hart, _ = struct.unpack(HEADER_FMT, raw)
    if magic != MAGIC:
        sys.exit(f"error: not a cva6 binary trace (magic {magic!r})")
    if version > LATEST_VERSION:
        sys.exit(f"error: version {version} is newer than this reader, which knows up to "
                 f"{LATEST_VERSION}")
    return dict(version=version, record_size=record_size, xlen=xlen, vlen=vlen,
                plen=plen, hart_id=hart)


def records(handle, record_size):
    known = struct.calcsize(RECORD_FMT)
    while True:
        raw = handle.read(record_size)
        if not raw:
            return
        if len(raw) < record_size:
            sys.exit("error: trailing partial record, the file was truncated")
        # a newer writer may use longer records; the fields we know keep their place
        yield dict(zip(FIELDS, struct.unpack(RECORD_FMT, raw[:known])))


def mode_name(record):
    """Privilege level and the virtualisation bit, which U and S alone cannot tell apart."""
    priv = record["priv"] & 3
    if record["flags"] & FLAG_VIRT:
        return VIRT_PRIV.get(priv, "?")
    return PRIV[priv]


def flag_list(flags):
    return ",".join(name for bit, name in FLAG_NAMES if flags & bit)


def class_list(klass):
    return ",".join(name for bit, name in CLASS_NAMES if klass & bit)


def main():
    p = argparse.ArgumentParser(description="read the tracer's binary output format")
    p.add_argument("path")
    p.add_argument("--csv", action="store_true", help="write csv instead of a readable dump")
    p.add_argument("--limit", type=int, default=0, help="stop after this many records")
    p.add_argument("--info", action="store_true", help="print the header and the count only")
    args = p.parse_args()

    with open(args.path, "rb") as handle:
        head = read_header(handle)
        if args.info:
            size = handle.seek(0, 2) - HEADER_SIZE
            print(f"version {head['version']}, record {head['record_size']} bytes, "
                  f"RV{head['xlen']}, vlen {head['vlen']}, plen {head['plen']}, "
                  f"hart {head['hart_id']}")
            print(f"{size // head['record_size']} records ({size} bytes of payload)")
            return 0

        if args.csv:
            print(",".join(FIELDS))
        width = (head["vlen"] + 3) // 4
        for i, r in enumerate(records(handle, head["record_size"])):
            if args.limit and i >= args.limit:
                break
            if args.csv:
                print(",".join(str(r[f]) for f in FIELDS))
            elif r["kind"] == 2:
                print(f"{r['cycle']:10d} {mode_name(r):<2} {r['pc']:0{width}x} "
                      f"CSR 0x{r['csr']:03x}=0x{r['rd_wdata']:x}")
            elif r["kind"] == 1:
                print(f"{r['cycle']:10d} {mode_name(r):<2} {r['pc']:0{width}x} "
                      f"TRAP cause=0x{r['rd_wdata']:x} tval=0x{r['rs1_rdata']:x}")
            else:
                out = (f"{r['cycle']:10d} {mode_name(r):<2} {r['pc']:0{width}x} "
                       f"{r['insn']:08x}")
                if r["rd_addr"]:
                    out += f" x{r['rd_addr']:<2d}=0x{r['rd_wdata']:016x}"
                if r["mem_rmask"]:
                    out += f" ld 0x{r['mem_vaddr']:0{width}x}"
                if r["mem_wmask"]:
                    out += f" st 0x{r['mem_vaddr']:0{width}x}=0x{r['mem_wdata']:016x}"
                tags = [t for t in (class_list(r["class"]), flag_list(r["flags"])) if t]
                if tags:
                    out += f" [{','.join(tags)}]"
                print(out)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:
        # piping into head or grep -m closes the pipe under us, which is normal
        try:
            sys.stdout.close()
        finally:
            sys.exit(0)
    except KeyboardInterrupt:
        sys.exit(130)
