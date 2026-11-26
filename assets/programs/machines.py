#!/usr/bin/env python3
"""Quadruple Turing machines (M. Davis's presentation, chapter 3 of the manual).

A quadruple (q, s, a, q2) reads: "in state q, if the head reads the symbol s,
perform the action a, then go to state q2". The action a is
  - a symbol (it is written in the scanned cell),
  - 'L' (the head moves one cell left) or 'R' (one cell right).
The machine halts when no quadruple begins with (current state, scanned symbol).

Input and output conventions (those of the manual):
  - the integer x is written on the tape as x+1 strokes "1";
  - arguments are separated by a blank B;
  - the machine starts in state q0, with the head on the first stroke;
  - the result is the total number of strokes on the tape when it halts.

Command-line use:
    python3 machines.py file.tm 2 3          runs the machine on (2, 3)
    python3 machines.py file.tm 2 3 --trace  prints every instantaneous description
A .tm file holds one quadruple per line, for example "q0 1 B q1";
whatever follows a "#" is a comment.

MIT licence. Frédéric Prost and Claude.
"""
import sys

BLANK = "B"
STROKE = "1"


class InconsistentMachine(ValueError):
    """Two quadruples begin with the same pair (state, symbol)."""


class Machine:
    """A quadruple Turing machine.

    >>> m = Machine.from_text("q0 1 B q1\\nq1 B R q2\\nq2 1 R q2\\nq2 B R q3\\nq3 1 B q4")
    >>> m.compute(2, 3)
    5
    """

    def __init__(self, quadruples, initial_state="q0"):
        self.quadruples = [tuple(q) for q in quadruples]
        self.initial_state = initial_state
        self.table = {}
        for q in self.quadruples:
            if len(q) != 4:
                raise ValueError("malformed quadruple: %r" % (q,))
            key = (q[0], q[1])
            if key in self.table and self.table[key] != q:
                raise InconsistentMachine("two quadruples begin with %s %s" % key)
            self.table[key] = q

    # ---------------------------------------------------------------- reading
    @classmethod
    def from_text(cls, text, initial_state="q0"):
        """Reads quadruples, one per line (or separated by ";")."""
        quads = []
        for line in text.replace(";", "\n").splitlines():
            line = line.split("#", 1)[0].replace("(", " ").replace(")", " ").replace(",", " ").strip()
            if line:
                pieces = line.split()
                if len(pieces) != 4:
                    raise ValueError("malformed quadruple: \"%s\"" % line)
                quads.append(tuple(pieces))
        return cls(quads, initial_state)

    @classmethod
    def from_file(cls, path):
        with open(path, encoding="utf-8") as f:
            return cls.from_text(f.read())

    def to_text(self):
        return "\n".join(" ".join(q) for q in self.quadruples) + "\n"

    def states(self):
        e = {self.initial_state}
        for q in self.quadruples:
            e.add(q[0])
            e.add(q[3])
        return e

    def symbols(self):
        s = {BLANK, STROKE}
        for q in self.quadruples:
            s.add(q[1])
            if q[2] not in ("L", "R"):
                s.add(q[2])
        return s

    def __len__(self):
        return len(self.quadruples)

    # ---------------------------------------------------------------- running
    def initial_configuration(self, *args):
        return Configuration(initial_tape(args), 0, self.initial_state)

    def step(self, c):
        """Performs one step on the configuration c (modified in place).
        Returns False if the machine has halted."""
        read = c.tape.get(c.position, BLANK)
        q = self.table.get((c.state, read))
        if q is None:
            return False
        action = q[2]
        if action == "L":
            c.position -= 1
        elif action == "R":
            c.position += 1
        elif action == BLANK:
            c.tape.pop(c.position, None)
        else:
            c.tape[c.position] = action
        c.state = q[3]
        c.steps += 1
        return True

    def run(self, *args, max_steps=10**8, trace=None):
        """Runs the machine. Returns the final configuration.
        Raises TimeOut if the machine has not halted after max_steps steps."""
        c = self.initial_configuration(*args)
        if trace is not None:
            trace(c)
        while self.step(c):
            if trace is not None:
                trace(c)
            if c.steps >= max_steps:
                raise TimeOut(c)
        return c

    def compute(self, *args, max_steps=10**8):
        """Value Psi_Z(args): the number of strokes when the machine halts."""
        return self.run(*args, max_steps=max_steps).number_of_strokes()

    def full_computation(self, *args, max_steps=10**6):
        """The list of instantaneous descriptions of the computation (a "computation" in the sense of chapter 3)."""
        lines = []
        self.run(*args, max_steps=max_steps, trace=lambda c: lines.append(c.description()))
        return lines


class TimeOut(RuntimeError):
    def __init__(self, configuration):
        super().__init__("no halt after %d steps" % configuration.steps)
        self.configuration = configuration


def initial_tape(args):
    """Tape q0 1^{x1+1} B 1^{x2+1} B ... as a dictionary {position: symbol}."""
    tape, pos = {}, 0
    for j, x in enumerate(args):
        if j > 0:
            pos += 1
        for _ in range(x + 1):
            tape[pos] = STROKE
            pos += 1
    return tape


class Configuration:
    """Tape (dictionary of the non-blank cells), head position, state, number of steps."""

    def __init__(self, tape, position, state):
        self.tape, self.position, self.state, self.steps = dict(tape), position, state, 0

    def number_of_strokes(self):
        return sum(1 for s in self.tape.values() if s == STROKE)

    def description(self):
        """Instantaneous description "γ q S δ": the state is written just before the scanned cell."""
        keys = list(self.tape) + [self.position]
        lo, hi = min(keys), max(keys)
        words = []
        for i in range(lo, hi + 1):
            if i == self.position:
                words.append(self.state)
            words.append(self.tape.get(i, BLANK))
        return " ".join(words)


def quintuples_to_quadruples(quintuples):
    """Translates a quintuple machine (q, s, written, move L/R, q2) into a quadruple machine:
    each quintuple becomes two quadruples, through a fresh intermediate state (chapter 3, variants)."""
    quads, k = [], 0
    for q, s, written, move, q2 in quintuples:
        k += 1
        mid = "%s_%s_%d" % (q, s, k)
        quads.append((q, s, written, mid))
        # in the intermediate state, the scanned symbol is necessarily the one just written
        quads.append((mid, written, move, q2))
    return Machine(quads, quintuples[0][0] if quintuples else "q0")


def _main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    m = Machine.from_file(argv[1])
    trace = "--trace" in argv
    args = [int(a) for a in argv[2:] if not a.startswith("--")]
    if trace:
        for line in m.full_computation(*args):
            print(line)
    c = m.run(*args)
    print("halted after %d steps, %d strokes: result %d" % (c.steps, c.number_of_strokes(), c.number_of_strokes()))
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
