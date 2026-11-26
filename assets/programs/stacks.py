"""stacks.py: two-stack automata, and the translation of a Turing machine into a two-stack automaton.

A two-stack automaton has a finite set of states and two stacks G (left) and D (right).
At each step, it looks at its state and at the tops of the two stacks (EMPTY if a stack is empty),
then it may pop each of the two stacks, push a word on each, and change state.
If it has no transition for what it sees, it halts.

Simulating a tape (chapter "Other models"): the stack D holds the scanned cell (on top)
and all the cells to its right; the stack G holds the cells to the left of the head, the nearest
on top. An empty stack reads as infinitely many blanks.

    python3 stacks.py                    # translates addition and compares the two runs
    python3 stacks.py examples/addition.tm 2 3 --trace

MIT licence. Authors: Frédéric Prost and Claude.
"""
import sys

from machines import Machine, BLANK, STROKE, initial_tape

EMPTY = "⊥"


class TwoStackAutomaton:
    """Transitions: (state, top of G, top of D) -> (pop G, pop D, word pushed on G,
    word pushed on D, new state). The pushed words are tuples, the last element on top."""

    def __init__(self, transitions, initial_state):
        self.transitions = dict(transitions)
        self.initial_state = initial_state

    def __len__(self):
        return len(self.transitions)

    def step(self, state, G, D):
        """Performs one step (G and D are lists, top at the end). Returns the new state, or None when halted."""
        key = (state, G[-1] if G else EMPTY, D[-1] if D else EMPTY)
        t = self.transitions.get(key)
        if t is None:
            return None
        pop_g, pop_d, push_g, push_d, following = t
        if pop_g:
            G.pop()
        if pop_d:
            D.pop()
        G.extend(push_g)
        D.extend(push_d)
        return following

    def run(self, G, D, max_steps=10**7, trace=None):
        state, n = self.initial_state, 0
        while True:
            if trace:
                trace(state, G, D)
            new = self.step(state, G, D)
            if new is None:
                return state, G, D, n
            state, n = new, n + 1
            if n >= max_steps:
                raise RuntimeError("no halt after %d steps" % n)


def from_turing(machine):
    """Translates a quadruple Turing machine into a two-stack automaton that makes one step
    for each step of the machine. The blank is never pushed needlessly: an empty stack stands for blanks."""
    tops = sorted(machine.symbols()) + [EMPTY]
    trans = {}
    for (q, s, action, q2) in machine.quadruples:
        read_d = [s, EMPTY] if s == BLANK else [s]        # on D, a blank may be an empty stack
        for d in read_d:
            pops_d = d != EMPTY
            for g in tops:
                if action == "R":
                    # the scanned cell goes onto G; the next cell becomes the top of D
                    push_g = () if (s == BLANK and g == EMPTY) else (s,)
                    trans[(q, g, d)] = (False, pops_d, push_g, (), q2)
                elif action == "L":
                    # the top of G (or a blank) comes back onto D, above the scanned cell
                    push_d = ((s,) if pops_d or s != BLANK else ()) + (g if g != EMPTY else BLANK,)
                    trans[(q, g, d)] = (g != EMPTY, pops_d, (), push_d, q2)
                else:
                    # writing: the top of D is replaced
                    trans[(q, g, d)] = (False, pops_d, (), (action,), q2)
    return TwoStackAutomaton(trans, machine.initial_state)


def initial_stacks(*args):
    """The initial tape q0 1^{x1+1} B ...: G empty, D holds the tape, the first cell on top."""
    tape = initial_tape(args)
    n = max(tape) + 1 if tape else 0
    return [], [tape.get(i, BLANK) for i in reversed(range(n))]


def tape_from_stacks(G, D):
    """Rebuilds (dictionary of the non-blank cells, head position = 0)."""
    tape = {}
    for i, s in enumerate(reversed(D)):
        if s != BLANK:
            tape[i] = s
    for i, s in enumerate(reversed(G)):
        if s != BLANK:
            tape[-1 - i] = s
    return tape


def compare(machine, *args, max_steps=10**6):
    """Runs the machine and the automaton side by side and checks, step by step, that the tape and the state
    are the same. Returns (number of steps, number of strokes)."""
    auto = from_turing(machine)
    c = machine.initial_configuration(*args)
    G, D = initial_stacks(*args)
    state = auto.initial_state
    while True:
        tape = {i - c.position: s for i, s in c.tape.items() if s != BLANK}
        assert tape == tape_from_stacks(G, D), "different tapes at step %d" % c.steps
        assert state == c.state
        machine_goes_on = machine.step(c)
        new = auto.step(state, G, D)
        assert (new is None) == (not machine_goes_on), "different halts at step %d" % c.steps
        if new is None:
            return c.steps, c.number_of_strokes()
        state = new
        if c.steps > max_steps:
            raise RuntimeError("too long")


def show(state, G, D):
    left = " ".join(G) if G else ""
    right = " ".join(reversed(D)) if D else ""
    print("  %-6s G = [%s|   |%s] = D" % (state, left, right))


def _main(argv):
    trace = "--trace" in argv
    argv = [a for a in argv if a != "--trace"]
    if len(argv) >= 2:
        machine = Machine.from_file(argv[1])
        args = [int(a) for a in argv[2:]]
    else:
        import os
        machine = Machine.from_file(os.path.join(os.path.dirname(os.path.abspath(__file__)), "examples", "addition.tm"))
        args = [2, 3]
    auto = from_turing(machine)
    print("Turing machine: %d quadruples; two-stack automaton: %d transitions." % (len(machine), len(auto)))
    if trace:
        G, D = initial_stacks(*args)
        auto.run(G, D, trace=show)
    steps, strokes = compare(machine, *args)
    print("Input %s: the two runs agree for %d steps; result %d strokes, that is %d." % (args, steps, strokes, strokes))


if __name__ == "__main__":
    _main(sys.argv)
