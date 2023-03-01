# Copyright 2022 Thales DIS design services SAS
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

import sys
import re

from dataclasses import dataclass
from enum import Enum

from matplotlib import pyplot as plt

from isa import Instr

EventKind = Enum('EventKind', ['WAW', 'WAR', 'RAW', 'issue', 'done', 'commit'])

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
        self.address = address
        self.hex_code = hex_code
        self.mnemo = mnemo
        self.events = []

    def mnemo_name(self):
        """The name of the instruction (fisrt word of the mnemo)"""
        return self.mnemo.split()[0]

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
        return f"{status} `{self.instr}` for {self.cycles_since_issue}"

class Model:
    """Models the scheduling of CVA6"""

    re_csrr_minstret = re.compile(r"^csrr\s+\w\w,\s*minstret$")
    re_instr = re.compile(
        r"([a-z]+)\s+0:\s*0x00000000([0-9a-f]+)\s*\(([0-9a-fx]+)\)\s*@\s*([0-9]+)\s*(.*)"
    )

    def __init__(self, issue=1, commit=2, sb_len=16, has_forwarding=True, has_renaming=True):
        self.instr_queue = []
        self.scoreboard = []
        self.retired = []
        self.sb_len = sb_len
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

    def try_issue(self, cycle):
        """Try to issue an instruction"""
        if len(self.instr_queue) == 0 or len(self.scoreboard) >= self.sb_len:
            return
        can_issue = True
        instr = self.instr_queue[0]
        for entry in self.scoreboard:
            if instr.has_WAW_from(entry.instr) and not self.has_renaming:
                self.log_event_on(instr, EventKind.WAW, cycle)
                can_issue = False
            if instr.has_WAR_from(entry.instr) and not self.has_renaming:
                self.log_event_on(instr, EventKind.WAR, cycle)
                can_issue = False
            can_forward = self.has_forwarding and entry.done
            if instr.has_RAW_from(entry.instr) and not can_forward:
                self.log_event_on(instr, EventKind.RAW, cycle)
                can_issue = False
        if can_issue:
            instr = self.instr_queue.pop(0)
            self.log_event_on(instr, EventKind.issue, cycle)
            entry = Entry(instr)
            self.scoreboard.append(entry)

    def try_execute(self, cycle):
        """Try to execute instructions"""
        for entry in self.scoreboard:
            entry.cycles_since_issue += 1
            name = entry.instr.mnemo_name()
            is_load = (name.startswith('l') or name.startswith('fl')) and not "".endswith('i')
            duration = 2 if is_load else 1
            if entry.cycles_since_issue == duration:
                self.log_event_on(entry.instr, EventKind.done, cycle)
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

    def run(self, cycles=None, debug=False):
        """Run until completion"""
        cycle = 0
        while len(self.instr_queue) > 0 or len(self.scoreboard) > 0:
            self.run_cycle(cycle)
            if debug:
                print(f"Scoreboard @{cycle}")
                for entry in self.scoreboard:
                    print(f"    {entry}")
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

def issue_commit_graph(input_file, n = 6):
    """Plot the issue/commit graph"""

    # TODO really use it
    r = range(1, n + 1)
    scores = [[0 for _ in range(n + 1)] for _ in range(n + 1)]

    if input_file is None:
        scores = [[0, 0, 0, 0, 0, 0, 0], [0, 2.6888804039773917, 2.726957887589342, 2.726957887589342, 2.726957887589342, 2.726957887589342, 2.726957887589342], [0, 2.8583351912512076, 3.5010450619509923, 3.522007262378975, 3.522007262378975, 3.522007262378975, 3.522007262378975], [0, 2.8583351912512076, 3.5867233847191238, 3.7285746777579334, 3.734074173649385, 3.7406390507754343, 3.7406390507754343], [0, 2.8583351912512076, 3.59096083339019, 3.7392682999790603, 3.788912127549938, 3.7957866767887647, 3.7957866767887647], [0, 2.8583351912512076, 3.59096083339019, 3.7404851409227775, 3.7900896735216754, 3.8142607581224683, 3.8143189533508792], [0, 2.8583351912512076, 3.59096083339019, 3.740541106676492, 3.7906643518343026, 3.8143189533508792, 3.818805324942145]] # pylint: disable=line-too-long
    else:
        for issue in r:
            for commit in r:
                model = Model(issue, commit)
                model.load_file(input_file)
                cycle_number = model.run()
                scores[issue][commit] = 1000000 / cycle_number
        print(scores)
    display_scores(scores)

def main(input_file: str):
    """Entry point"""

    debug = False
    model = Model()
    model.load_file(input_file)
    cycle_number = model.run(debug=debug)

    write_trace('annotated.log', model.retired)

    nWAW, nWAR, nRAW = 0, 0, 0
    for (e, i) in model.log:
        if debug:
            print_data(f"{e}", f"{i}", sep='on')
        if e.kind == EventKind.WAW:
            nWAW += 1
        if e.kind == EventKind.WAR:
            nWAR += 1
        if e.kind == EventKind.RAW:
            nRAW += 1

    n_instr = len(model.retired)
    print_data("cycle number", cycle_number)
    print_data("Coremark/MHz", 1000000 / cycle_number)
    print_data("instruction number", n_instr)
    print_data("WAW/instr", nWAW / n_instr)
    print_data("WAR/instr", nWAR / n_instr)
    print_data("RAW/instr", nRAW / n_instr)

if __name__ == "__main__":
    main(sys.argv[1])
