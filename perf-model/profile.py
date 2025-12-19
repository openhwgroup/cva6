from dataclasses import dataclass
import subprocess
import re

import pstats

import flameprof

import isa

re_instr = re.compile(
    r"([a-z]+)\s+0:\s*0x00000000([0-9a-f]+)\s*\(([0-9a-fx]+)\)\s*@\s*([0-9]+)\s*(.*)"
)
re_mem = re.compile(r"mem\s*0x([0-9a-f]+)")

@dataclass
class AsmFunc:
    index: int
    name: str
    size: int
    vma: int
    lma: int
    file_off: int
    align: int

    def start_addr(self):
        return self.vma

    def end_addr(self):
        return self.vma + self.size

    def contains(self, addr):
        return self.start_addr() <= addr and addr <= self.end_addr()

    def load_elf(path):
        objdump = "/shares/common/tools/gcc-13.1.0/bin/riscv-none-elf-objdump"
        out = subprocess.check_output([objdump, "-h", path]).decode("utf-8")
        lines = [l for l in out.split("\n") if ".text." in l]
        return [AsmFunc._from_line(l.split()) for l in lines]

    def _from_line(line):
        return AsmFunc(
                index = int(line[0]),
                name = line[1][6:],
                size = int(line[2], 16),
                vma = int(line[3], 16),
                lma = int(line[4], 16),
                file_off = int(line[5], 16),
                align = int(line[6][3:], 16),
        )

@dataclass
class RvfiInstr:
    def __init__(self, address, cycle, op, line, next_line=None):
        self.address = address
        self.cycle = cycle
        self.op = isa.Instr(op)
        self.line = line
        self.mem_address = None
        if self.op.is_load() or self.op.is_store():
            assert(next_line is not None)
            self.mem_address = int(re_mem.search(next_line).group(1), 16)

    def load_trace(path):
        with open(path, "r", encoding="utf8") as f:
            lines = f.readlines()
        return RvfiInstr._from_lines(lines)

    def _from_lines(lines):
        instrs = []
        for i, l in enumerate(lines):
            line = l.strip()
            found = re_instr.search(line)
            if found:
                instr = RvfiInstr(
                    address = int(found.group(2), 16),
                    cycle = int(found.group(4)),
                    op = int(found.group(3), 16),
                    line = line,
                    next_line = lines[i+1] if i + 1 < len(lines) else None,
                )
                instrs.append(instr)
        return instrs

class CallStack:
    def __init__(self, functions):
        self.stack = []
        self.fns = { f.start_addr(): f for f in functions }

    def run(self, instr):
        addr = instr.address

        f = self.fns.get(addr)
        if f:
            e = RawEvent(stack=self.stack_names(), cycle=instr.cycle)
            self.stack.append(f)
            return e

        if len(self.stack) > 0:
            curr = self.stack[-1]
            if not curr.contains(addr) and any(f.contains(addr) for f in self.fns.values()):
                e = RawEvent(stack=self.stack_names(), cycle=instr.cycle)
                self.stack.pop()
                return e

        return None

    def stack_names(self):
        return [f.name for f in self.stack]

@dataclass
class RawEvent:
    stack: list
    cycle: int

@dataclass
class Event:
    stack: list
    instr: RvfiInstr
    duration: int
    icount: int
    nloads: int
    nstores: int
    dloads: int
    dstores: int
    mem_contig: bool

class MemoryAccesses:
    def __init__(self):
        self.loads = {}
        self.stores = {}

    def load(self, addr):
        if addr in self.loads:
            self.loads[addr] += 1
        else:
            self.loads[addr] = 1

    def store(self, addr):
        if addr in self.stores:
            self.stores[addr] += 1
        else:
            self.stores[addr] = 1

def run_all(fns, instrs):
    events = []
    cs = CallStack(fns)
    cycle = 0
    icount = 0
    mem = MemoryAccesses()

    nloads = nstores = dloads = dstores = mem_contig = 0
    dcycle = maddr = None

    for i, instr in enumerate(instrs):
        if instr.op.is_load():
            nloads += 1
            dloads += instr.cycle - dcycle
            mem.load(instr.mem_address)
        if instr.op.is_store():
            nstores += 1
            dstores += instr.cycle - dcycle
            mem.store(instr.mem_address)
        dcycle = instr.cycle

        if instr.op.is_load() or instr.op.is_store():
            if maddr is not None and instr.mem_address in (maddr + 4, maddr - 4):
                mem_contig += 1
            maddr = instr.mem_address

        event = cs.run(instr)
        if event:
            events.append(Event(
                stack = event.stack,
                instr = instr,
                duration = event.cycle - cycle,
                icount = i - icount,
                nloads = nloads,
                nstores = nstores,
                dloads = dloads,
                dstores = dstores,
                mem_contig = mem_contig
            ))
            cycle = event.cycle
            icount = i

            nloads = nstores = dloads = dstores = mem_contig = 0

    for addr, count in sorted(mem.loads.items(), key=lambda item: item[1], reverse=True)[:10]:
        print(hex(addr), count, "loads")
    for addr, count in sorted(mem.stores.items(), key=lambda item: item[1], reverse=True)[:10]:
        print(hex(addr), count, "stores")
    return events

#def build_situations(events, key):
#    situations = {}
#    for e in events:
#        k = key(e)
#        if k in situations:
#            situations[k] += e.duration
#        else:
#            situations[k] = e.duration
#    return situations

def fake_file(func):
    return ("", 1, func)

class Stat:
    def __init__(self):
        self.cc = 0
        self.nc = 0
        self.tt = 0
        self.ct = 0
        self.icount = 0
        self.nloads = 0
        self.nstores = 0
        self.dloads = 0
        self.dstores = 0
        self.callers = {}

    def ipc(self):
        return self.icount / self.tt if self.tt > 0 else 0.0

    def build(self):
        callers = { fake_file(func): t for func, t in self.callers.items() }
        return (self.cc, self.nc, self.tt, self.ct, callers)

    def add_caller(self, caller, c_cc, c_nc, c_tt, c_ct):
        (cc, nc, tt, ct) = self.callers[caller] if caller in self.callers else \
                           (0, 0, 0, 0)

        cc += c_cc
        nc += c_nc
        tt += c_tt
        ct += c_ct

        self.callers[caller] = (cc, nc, tt, ct)

def put_stat(d, name):
    if not name in d:
        d[name] = Stat()

def build_stats(events):
    stats = {}
    stack = []

    for event in events:
        if len(event.stack) == 0 or len(stack) == 0:
            stack = event.stack
            continue

        # Current function, in the which event.duration has been spent
        func = stack[-1]
        duration = event.duration
        put_stat(stats, func)

        # Spent duration right into func
        stats[func].tt += duration
        stats[func].icount += event.icount
        stats[func].nloads += event.nloads
        stats[func].nstores += event.nstores
        stats[func].dloads += event.dloads
        stats[func].dstores += event.dstores

        # Spent duration in func and its parents
        for f in stack:
            stats[f].ct += duration

        # Spent duration while being called directly by caller
        if len(stack) > 1:
            caller = stack[-2]
            stats[func].add_caller(caller, 0, 0, duration, 0)

        # Each function in the call stack spent duration called by its caller
        for i, callee in enumerate(stack):
            if i > 0:
                caller = stack[i - 1]
                stats[callee].add_caller(caller, 0, 0, 0, duration)

        if len(event.stack) >= len(stack):
            # Make sure it is a call
            assert len(event.stack) <= len(stack) + 1
        else:
            # Make sure it is a ret
            assert len(event.stack) == len(stack) - 1

            callee = func
            caller = event.stack[-1]
            put_stat(stats, caller)

            # The caller called the callee once
            # It is not a prim call if the callee was already in the stack.
            c_cc = 1 if not callee in event.stack else 0
            stats[callee].add_caller(caller, c_cc, 1, 0, 0)
            stats[callee].cc += c_cc
            stats[callee].nc += 1

        stack = event.stack

    return stats

    #{ func: (cc, nc, tt, ct, callers) }
    # func = file_name, line_number, func_name
    # cc = prim_calls = number of calls if not already in call stack (non-recurse calls)?
    # nc = number of calls
    # tt = tottime = time spent in this function alone (not callees)
    # ct = cumtime = time spent in the function plus all functions that this function called
    # callers/clist = { cfunc: t } = { name: (cc, nc, tt, ct) }

def format_stack_change(old_stack, new_stack):
    if len(old_stack) > len(new_stack):
        return f"RET FROM {old_stack[-1]} (in {new_stack})"
    if len(new_stack) > len(old_stack):
        return f"CALL {new_stack[-1]} (in {old_stack})"
    return None

def print_stats(stats):
    for func, stat in stats.items():
        print(f'- {func}:')
        print('    cc:', stat.cc)
        print('    nc:', stat.nc)
        print('    tt:', stat.tt)
        print('    ct:', stat.ct)
        print('    callers:')
        for caller, cstat in stat.callers.items():
            print(f'    - {caller}:')
            print('        cc:', cstat[0])
            print('        nc:', cstat[1])
            print('        tt:', cstat[2])
            print('        ct:', cstat[3])

def render(stats, svg_path):
    stats = { fake_file(func): stat.build() for func, stat in stats.items() }

    with open(svg_path, 'w') as f:
        flameprof.render(stats, f, width=1920)

def filter_events(events, func_name):
    return [e for e in events if func_name not in e.stack]

if __name__ == "__main__":
    #elf_file = "pqc/32.o"
    #trace_file = "pqc/32.log"
    elf_file = "out_2025-03-28/directed_c_tests/main.o"
    trace_file = "out_2025-03-28/veri-testharness_sim/main.hwconfig.log"

    functions = AsmFunc.load_elf(elf_file)
    instructions = RvfiInstr.load_trace(trace_file)

    events = run_all(functions, instructions)

    #for size in ['128', '256']:
    #    events = filter_events(events, f'shake{size}_inc_init')
    #    events = filter_events(events, f'PQCLEAN_DILITHIUM3_CLEAN_dilithium_shake{size}_stream_init')
    #    events = filter_events(events, f'shake{size}_inc_squeeze')
    #    events = filter_events(events, f'shake{size}_inc_absorb')
    #    events = filter_events(events, f'shake{size}_inc_finalize')
    #    events = filter_events(events, f'shake{size}_inc_ctx_release')
    #events = filter_events(events, 'shake256')

    #events = filter_events(events, 'PQCLEAN_DILITHIUM3_CLEAN_montgomery_reduce')

    i_event = 0
    for instr in instructions:
        if i_event < len(events) and events[i_event].instr is instr:
            print(">>>", format_stack_change(events[i_event-1].stack, events[i_event].stack))
            i_event += 1
        print(instr.line)
        #print(instr.next_line)

    stats = build_stats(events)
    duration = sum(map(lambda e: e.duration, events))
    icount = sum(map(lambda e: e.icount, events))
    print("duration:", duration)
    print("icount:", icount)
    print("IPC:", icount / duration)

    ipcs = []
    for func, stat in stats.items():
        ipcs.append((stat.ipc(), func))
    ipcs.sort(reverse=True)
    for ipc, func in ipcs:
        print(f"{ipc:.02f} IPC for {func}")
    render(stats, 'result-base.svg')

    #r = lambda op, d, n, tt: f"{d}/{n}={d/n:.01f} cycles per {op}, {d/tt*100:.01f}% of duration"
    #report = lambda op, d, n, tt: r(op, d, n, tt) if n > 0 else f"no {op}s"

    #mem_usage = lambda s: (s.dloads + s.dstores) / s.tt if s.tt > 0 else 0
    #by_mem_usage = sorted(list(stats.items()), key=lambda s: mem_usage(s[1]), reverse=True)

    #dloads_tot = dstores_tot = nloads_tot = nstores_tot = 0
    #for func, stat in by_mem_usage:
    #    dloads_tot += stat.dloads
    #    dstores_tot += stat.dstores
    #    nloads_tot += stat.nloads
    #    nstores_tot += stat.nstores
    #    if stat.tt > 0:
    #        load_report = report('load', stat.dloads, stat.nloads, stat.tt)
    #        store_report = report('store', stat.dstores, stat.nstores, stat.tt)
    #        mem_report = report('mem', stat.dloads + stat.dstores, stat.nloads + stat.nstores, stat.tt)
    #        print(f"in {func}:")
    #        print(f"    {load_report}")
    #        print(f"    {store_report}")
    #        print(f"    {mem_report}")
    #print(report('load', dloads_tot, nloads_tot, duration))
    #print(report('store', dstores_tot, nstores_tot, duration))
    #print(report('mem', dloads_tot + dstores_tot, nloads_tot + nstores_tot, duration))

    #situations = build_situations(events, lambda e: ' '.join(e.stack))
    #leaves = build_situations(events, lambda e: e.stack[-1] if len(e.stack) > 0 else "")
    #limited = build_situations(events, lambda e: ' '.join(e.stack[:5]) if len(e.stack) > 0 else "")

    #for s in [situations, leaves, limited]:
    #    items = list(s.items())
    #    items.sort(key=lambda t: t[0], reverse=False)
    #    for stack, duration in items:
    #        print(stack, duration)
    #    total = sum(s.values())
    #    print(total)
