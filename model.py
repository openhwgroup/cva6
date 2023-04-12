# Copyright 2022 Thales DIS design services SAS
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

import sys
import re

from dataclasses import dataclass
from enum import Enum
from collections import defaultdict

from matplotlib import pyplot as plt

from isa import Instr

EventKind = Enum('EventKind', [
    'WAW', 'WAR', 'RAW',
    'BMISS', 'BHIT',
    'STRUCT',
    'issue', 'done', 'commit',
])

class Event:
    """Represents an event on an instruction"""
    def __init__(self, kind, cycle):
        self.kind = kind
        self.cycle = cycle

    def __repr__(self):
        return f"@{self.cycle}: {self.kind}"

class Instruction(Instr):
    """Represents a RISC-V instruction with annotations"""

    def __init__(self, line, address, hex_code, mnemo):
        Instr.__init__(self, int(hex_code, base=16))
        self.line = line
        self.address = int(address, base=16)
        self.hex_code = hex_code
        self.mnemo = mnemo
        self.events = []

    def mnemo_name(self):
        """The name of the instruction (fisrt word of the mnemo)"""
        return self.mnemo.split()[0]

    def next_addr(self):
        """Address of next instruction"""
        return self.address + self.size()

    def __repr__(self):
        return self.mnemo

@dataclass
class Entry:
    """A scoreboard entry"""
    instr: Instruction
    cycles_since_issue = 0
    done: bool = False

    def __repr__(self):
        status = "DONE" if self.done else "WIP "
        addr = f"0x{self.instr.address:08X}"
        return f"{status} {addr}:`{self.instr}` for {self.cycles_since_issue}"

@dataclass
class LastIssue:
    """To store the last issued instruction"""
    instr: Instruction
    issue_cycle: int

class IqLen:
    """Model of the instruction queue with only a size counter"""
    def __init__(self, fetch_size, debug=False):
        self.len = fetch_size
        self.fetch_size = fetch_size
        self.debug = debug

    def fetch(self):
        """Fetch bytes"""
        self.len += self.fetch_size
        self._debug(f"fetched {self.fetch_size}, got {self.len}")

    def flush(self):
        """Flush instruction queue (bmiss or exception)"""
        self.len = 0
        self._debug(f"flushed, got {self.len}")

    def jump(self):
        """Loose a fetch cycle and truncate (jump, branch hit taken)"""
        self.len -= self.fetch_size
        self._debug(f"jumping, removed {self.fetch_size}, got {self.len}")
        self._truncate()
        self._debug(f"jumped, got {self.len}")

    def has(self, instr):
        """Does the instruction queue have this instruction?"""
        length = self.len
        if self._is_crossword(instr):
            length -= 2
        self._debug(f"comparing {length} to {instr.size()} ({instr})")
        return length >= instr.size()

    def remove(self, instr):
        """Remove instruction from queue"""
        self.len -= instr.size()
        self._debug(f"removed {instr.size()}, got {self.len}")
        self._truncate(instr.is_compressed() == (instr.address & 2 == 0))
        if instr.is_jump():
            self.jump()

    def _addr_index(self, addr):
        return addr & (self.fetch_size - 1)

    def _instr_index(self, instr):
        return self._addr_index(instr.address)

    def _is_crossword(self, instr):
        is_last_c_index = self._instr_index(instr) == self.fetch_size - 2
        return is_last_c_index and not instr.is_compressed()

    def _truncate(self, mid_word=False):
        index = 2 if mid_word else 0
        occupancy = self._addr_index(self.len)
        self._debug(f"truncating, index={index}, occupancy={occupancy}")
        to_remove = occupancy - index
        if to_remove < 0:
            to_remove += self.fetch_size
        self.len -= to_remove
        self._debug(f"truncated, removed {to_remove}, got {self.len}")

    def _debug(self, message):
        if self.debug:
            print(f"iq: {message}")

class Model:
    """Models the scheduling of CVA6"""

    re_csrr_minstret = re.compile(r"^csrr\s+\w\w,\s*minstret$")
    re_instr = re.compile(
        r"([a-z]+)\s+0:\s*0x00000000([0-9a-f]+)\s*\(([0-9a-fx]+)\)\s*@\s*([0-9]+)\s*(.*)"
    )

    def __init__(self, debug=False, issue=1, commit=2, sb_len=8, fetch_size=None, has_forwarding=True, has_renaming=True):
        self.instr_queue = []
        self.scoreboard = []
        self.last_issued = None
        self.retired = []
        self.sb_len = sb_len
        self.debug = debug
        self.iqlen = IqLen(fetch_size or 4 * issue, debug)
        self.issue_width = issue
        self.commit_width = commit
        self.has_forwarding = has_forwarding
        self.has_renaming = has_renaming
        self.log = []

    def log_event_on(self, instr, kind, cycle):
        """Log an event on the instruction"""
        event = Event(kind, cycle)
        instr.events.append(event)
        self.log.append((event, instr))

    def predict_branch(self, branch_instr):
        """Predict if branch is taken or not"""
        return branch_instr.offset() >> 31 != 0

    def predict_regjump(self, regjump_instr):
        """Predict destination address of indirect jump"""
        return 0 # always miss

    def predict_pc(self, last):
        """Predict next program counter depending on last issued instruction"""
        if last.is_branch():
            offset = last.offset()
            if offset >> 31:
                offset -= 1 << 32
            taken = self.predict_branch(last)
            return last.address + (offset if taken else last.size())
        if last.is_regjump():
            return self.predict_regjump(last)
        return None

    def manage_last_branch(self, instr, cycle):
        """Flush IQ if branch miss, jump if branch hit"""
        if self.last_issued is not None:
            last = self.last_issued.instr
            pred = self.predict_pc(last)
            if pred is not None:
                bmiss = pred != instr.address
                resolved = cycle >= self.last_issued.issue_cycle + 6
                if bmiss and not resolved:
                    self.iqlen.flush()
                branch = EventKind.BMISS if bmiss else EventKind.BHIT
                if branch not in [e.kind for e in instr.events]:
                    self.log_event_on(instr, branch, cycle)
                    taken = instr.address != last.next_addr()
                    if taken and not bmiss:
                        # last (not instr) was like a jump
                        self.iqlen.jump()

    def find_data_hazards(self, instr, cycle):
        """Detect and log data hazards"""
        found = False
        for entry in self.scoreboard:
            if instr.has_WAW_from(entry.instr) and not self.has_renaming:
                self.log_event_on(instr, EventKind.WAW, cycle)
                found = True
            if instr.has_WAR_from(entry.instr) and not self.has_renaming:
                self.log_event_on(instr, EventKind.WAR, cycle)
                found = True
            can_forward = self.has_forwarding and entry.done
            if instr.has_RAW_from(entry.instr) and not can_forward:
                self.log_event_on(instr, EventKind.RAW, cycle)
                found = True
        return found

    def find_structural_hazard(self, instr, cycle):
        """Detect and long structural hazards"""
        found = False
        for entry in self.scoreboard:
            if not entry.done:
                if entry.instr.is_muldiv() and not instr.is_muldiv():
                    found = True
        if found:
            self.log_event_on(instr, EventKind.STRUCT, cycle)
        return found

    def try_issue(self, cycle):
        """Try to issue an instruction"""
        if len(self.instr_queue) == 0 or len(self.scoreboard) >= self.sb_len:
            return
        can_issue = True
        instr = self.instr_queue[0]
        if self.find_data_hazards(instr, cycle):
            can_issue = False
        if self.find_structural_hazard(instr, cycle):
            can_issue = False
        self.manage_last_branch(instr, cycle)
        if not self.iqlen.has(instr):
            can_issue = False
        if can_issue:
            self.iqlen.remove(instr)
            instr = self.instr_queue.pop(0)
            self.log_event_on(instr, EventKind.issue, cycle)
            entry = Entry(instr)
            self.scoreboard.append(entry)
            self.last_issued = LastIssue(instr, cycle)

    def try_execute(self, cycle):
        """Try to execute instructions"""
        for entry in self.scoreboard:
            entry.cycles_since_issue += 1
            instr = entry.instr
            duration = 1
            if instr.is_load() or instr.is_store():
                duration = 2
            if instr.is_muldiv():
                duration = 2
            if entry.cycles_since_issue == duration:
                self.log_event_on(instr, EventKind.done, cycle)
                entry.done = True

    def try_commit(self, cycle):
        """Try to commit an instruction"""
        if len(self.scoreboard) == 0:
            return
        entry = self.scoreboard[0]
        if entry.done:
            instr = self.scoreboard.pop(0).instr
            self.log_event_on(instr, EventKind.commit, cycle)
            self.retired.append(instr)

    def run_cycle(self, cycle):
        """Runs a cycle"""
        for _ in range(self.commit_width):
            self.try_commit(cycle)
        self.try_execute(cycle)
        for _ in range(self.issue_width):
            self.try_issue(cycle)
        self.iqlen.fetch()

    def load_file(self, path):
        """Fill a model from a trace file"""
        accepting = False
        with open(path, "r", encoding="utf8") as file:
            for line in [l.strip() for l in file]:
                found = Model.re_instr.search(line)
                if found:
                    address = found.group(2)
                    hex_code = found.group(3)
                    mnemo = found.group(5)
                    instr = Instruction(line, address, hex_code, mnemo)
                    if Model.re_csrr_minstret.search(instr.mnemo):
                        accepting = not accepting
                        continue
                    if accepting:
                        self.instr_queue.append(instr)

    def run(self, cycles=None):
        """Run until completion"""
        cycle = 0
        while len(self.instr_queue) > 0 or len(self.scoreboard) > 0:
            self.run_cycle(cycle)
            if self.debug:
                print(f"Scoreboard @{cycle}")
                for entry in self.scoreboard:
                    print(f"    {entry}")
                print(f"iqlen = {self.iqlen.len}")
                print()
            cycle += 1

            if cycles is not None and cycle > cycles:
                break
        return cycle

def write_trace(output_file, instructions):
    """Write cycle-annotated trace"""
    pattern = re.compile(r"@\s*[0-9]+")

    lines = []
    for instr in instructions:
        commit_event = instr.events[-1]
        assert commit_event.kind == EventKind.commit
        cycle = commit_event.cycle
        annotated = re.sub(pattern, f"@ {cycle}", instr.line)
        lines.append(f"{annotated}\n")

    with open(output_file, 'w') as f:
        f.writelines(lines)

def print_data(name, value, ts=24, sep='='):
    "Prints 'name = data' with alignment of the '='"

    spaces = ' ' * (ts - len(name))
    print(f"{name}{spaces} {sep} {value}")

def display_scores(scores):
    """Display a 3D graph of scores against commit/issue-wide"""
    bars = []
    for x, l in enumerate(scores):
        for y, z in enumerate(l):
            bars.append((x, y, z))

    x, y, z, dx, dy, dz = [], [], [], [], [], []
    for bx, by, bz in bars:
        x.append(bx)
        y.append(by)
        z.append(0)
        dx.append(.5)
        dy.append(.5)
        dz.append(bz)

    fig = plt.figure()
    ax1 = fig.add_subplot(111, projection='3d')
    ax1.bar3d(x, y, z, dx, dy, dz)
    ax1.set_xlabel("issue")
    ax1.set_ylabel("commit")
    ax1.set_zlabel("CoreMark/MHz")
    plt.show()

def issue_commit_graph(input_file, n = 3):
    """Plot the issue/commit graph"""

    r = range(n + 1)
    scores = [[0 for _ in r] for _ in r]

    if input_file is None:
        scores = [[0, 0, 0, 0, 0, 0], [0, 3.1986181969389222, 3.198628428130018, 3.198628428130018, 3.198628428130018, 3.198628428130018], [0, 3.543071346827711, 4.802635686464732, 4.802658751885043, 4.802658751885043, 4.802658751885043], [0, 3.54315922248914, 5.142472192081621, 5.241831915417801, 5.241831915417801, 5.241831915417801], [0, 3.54315922248914, 5.327565355908003, 5.507457096909215, 5.522970032364604, 5.522970032364604], [0, 3.54315922248914, 5.334158349824773, 5.525472427892585, 5.530055853564121, 5.530086435250983]] # pylint: disable=line-too-long
    else:
        r = range(1, n + 1)
        for issue in r:
            for commit in r:
                print("running", issue, commit)
                model = Model(issue=issue, commit=commit)
                model.load_file(input_file)
                cycle_number = model.run()
                score = 1000000 / cycle_number
                scores[issue][commit] = score
        print(scores)
    display_scores(scores)

def main(input_file: str):
    """Entry point"""

    model = Model(debug=True)
    model.load_file(input_file)
    cycle_number = model.run()

    write_trace('annotated.log', model.retired)

    ecount = defaultdict(lambda: 0)
    for (e, i) in model.log:
        ecount[e.kind] += 1

    n_instr = len(model.retired)
    print_data("cycle number", cycle_number)
    print_data("Coremark/MHz", 1000000 / cycle_number)
    print_data("instruction number", n_instr)
    for ek, count in ecount.items():
        print_data(f"{ek}/instr", f"{100 * count / n_instr:.2f}%")

if __name__ == "__main__":
    main(sys.argv[1])
