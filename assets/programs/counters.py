"""counters.py: counter machines, and the translation of a Turing machine into a two-counter machine.

A counter machine has counters (natural numbers) and a numbered program:
    ("INC", r, j)      add 1 to counter r, go to instruction j;
    ("DEC", r, j, k)   if r > 0, subtract 1 and go to j; otherwise go to k;
    ("STOP",)          halt.

The translation is done in two stages (chapter "Other models"):

 1. Turing machine -> three counters g, d, t. The tape is seen as two numbers written
    in base b (b = number of symbols, the blank being the digit 0): d holds the scanned cell
    (units digit) and the cells to its right, g the cells to the left of the head (the nearest
    in the units). Reading the cell means computing the remainder of d by b; moving right means removing
    this digit from d and adding it to g; t is an auxiliary counter for multiplying and dividing by b.
 2. Three counters -> two counters A, B: (g, d, t) is stored in the single number 2^g 3^d 5^t
    (counter A), B serving as an auxiliary; INC and DEC become multiplications and divisions.

A two-counter machine makes an astronomical number of steps (each INC of stage 1 multiplies A
by 3, one instruction after another). The interpreter below therefore runs the small loops
in one go ("speed-up"): the result is exactly that of the step-by-step run, and the
number of steps shown is the true number of steps of the machine.

    python3 counters.py                     # addition 2 + 1, on three then on two counters
    python3 counters.py examples/successor.tm 4

MIT licence. Authors: Frédéric Prost and Claude.
"""
import sys

from machines import Machine, BLANK, STROKE, initial_tape


# --------------------------------------------------------------------------- interpreter
class CounterMachine:
    def __init__(self, program, counters):
        self.program = program
        self.counters = list(counters)
        self._cycles = {}

    def __len__(self):
        return len(self.program)

    def _cycle(self, i):
        """If the instruction i = DEC(X, ...) begins a "simple" loop (following the successes:
        only DECs of the same counter X and INCs of other counters, back to i),
        returns (number of DECs per round, changes of the other counters, length of the round)."""
        if i in self._cycles:
            return self._cycles[i]
        X = self.program[i][1]
        j, ndec, delta, length, res = i, 0, {}, 0, None
        for _ in range(200):
            ins = self.program[j]
            length += 1
            if ins[0] == "DEC" and ins[1] == X:
                ndec += 1
                j = ins[2]
            elif ins[0] == "INC" and ins[1] != X:
                delta[ins[1]] = delta.get(ins[1], 0) + 1
                j = ins[2]
            else:
                break
            if j == i:
                res = (ndec, delta, length)
                break
        self._cycles[i] = res
        return res

    def run(self, values, max_real_steps=10**7, speed_up=True):
        """Returns (final values, number of steps of the machine, number of iterations of the interpreter)."""
        v = list(values)
        i, steps, iterations = 0, 0, 0
        while True:
            iterations += 1
            if iterations > max_real_steps:
                raise RuntimeError("too long")
            ins = self.program[i]
            if ins[0] == "STOP":
                return v, steps, iterations
            if ins[0] == "INC":
                v[ins[1]] += 1
                i = ins[2]
                steps += 1
                continue
            X = ins[1]
            if speed_up:
                cyc = self._cycle(i)
                if cyc is not None and v[X] >= cyc[0]:
                    rounds = v[X] // cyc[0]
                    v[X] -= rounds * cyc[0]
                    for r, dv in cyc[1].items():
                        v[r] += rounds * dv
                    steps += rounds * cyc[2]
                    continue
            if v[X] > 0:
                v[X] -= 1
                i = ins[2]
            else:
                i = ins[3]
            steps += 1


class Assembler:
    """Writes a program with labels: each instruction gets a number, jumps are resolved at the end."""

    def __init__(self):
        self.code, self.labels, self.n = [], {}, 0

    def fresh(self, prefix="e"):
        self.n += 1
        return "%s%d" % (prefix, self.n)

    def here(self, label):
        self.labels[label] = len(self.code)

    def inc(self, r, following):
        self.code.append(["INC", r, following])

    def dec(self, r, if_yes, if_no):
        self.code.append(["DEC", r, if_yes, if_no])

    def stop(self):
        self.code.append(["STOP"])

    def assemble(self):
        def res(x):
            return self.labels[x] if isinstance(x, str) else x
        prog = []
        for ins in self.code:
            if ins[0] == "INC":
                prog.append(("INC", ins[1], res(ins[2])))
            elif ins[0] == "DEC":
                prog.append(("DEC", ins[1], res(ins[2]), res(ins[3])))
            else:
                prog.append(("STOP",))
        return prog

    # ---- fragments: each begins at the given label and jumps to "end"
    def transfer(self, src, dst, factor, start, end):
        """dst += factor * src ; src := 0."""
        self.here(start)
        body = [self.fresh() for _ in range(factor)]
        self.dec(src, body[0] if factor else start, end)
        for k, e in enumerate(body):
            self.here(e)
            self.inc(dst, body[k + 1] if k + 1 < factor else start)

    def add(self, r, n, start, end):
        """r += n (n constant)."""
        if n == 0:
            self.here(start)
            self.dec_zero(end)
            return
        lab = [start] + [self.fresh() for _ in range(n - 1)] + [end]
        for k in range(n):
            self.here(lab[k])
            self.inc(r, lab[k + 1])

    def dec_zero(self, end):
        # "go to end": a jump is simulated by an instruction on a reserved counter, always zero
        self.dec(Z, end, end)

    def divide(self, src, quot, b, start, exits):
        """quot += src // b ; src := 0 ; jumps to exits[remainder]."""
        stages = [start] + [self.fresh() for _ in range(b)]
        for k in range(b):
            self.here(stages[k])
            self.dec(src, stages[k + 1], exits[k])
        self.here(stages[b])
        self.inc(quot, start)


G, D, T, Z = 0, 1, 2, 3          # counters of stage 1 (Z: counter always zero, for the jumps)


def symbol_codes(machine):
    """The blank is 0 (infinitely many blanks = unwritten zeros), the stroke 1, the others 2, 3, ..."""
    others = sorted(machine.symbols() - {BLANK, STROKE})
    codes = {BLANK: 0, STROKE: 1}
    for k, s in enumerate(others):
        codes[s] = k + 2
    return codes


def three_counters(machine):
    """Translates a Turing machine into a counter machine with counters g, d, t (plus Z, always zero).
    Returns (program, codes of the symbols, base b)."""
    codes = symbol_codes(machine)
    b = max(2, len(codes))
    symb = {c: s for s, c in codes.items()}
    a = Assembler()
    states = sorted(machine.states())
    start = {q: "read_" + q for q in states}
    a.dec_zero(start[machine.initial_state])                  # instruction 0: go to the initial state
    for q in states:
        # read: t := d // b, d := 0, and the remainder r = scanned cell is known
        exits = [a.fresh("read") for _ in range(b)]
        a.divide(D, T, b, start[q], exits)
        for r in range(b):
            s = symb.get(r, BLANK)
            rule = machine.table.get((q, s))
            a.here(exits[r])
            e1, e2, e3, e4 = (a.fresh() for _ in range(4))
            if rule is None:
                # halt: d = b*t + r is restored, then STOP
                a.dec_zero(e1)
                a.transfer(T, D, b, e1, e2)
                halt = a.fresh("halt")
                a.add(D, r, e2, halt)
                a.here(halt)
                a.stop()
                continue
            action, q2 = rule[2], rule[3]
            a.dec_zero(e1)
            if action == "R":
                # g := b*g + r (going through d, which is 0), then d := t
                a.transfer(G, D, b, e1, e2)
                a.add(D, r, e2, e3)
                a.transfer(D, G, 1, e3, e4)
                a.transfer(T, D, 1, e4, start[q2])
            elif action == "L":
                # d := b*t + r ; t := g // b ; g := t ; d := b*d + (remainder of g)
                e5 = a.fresh()
                a.transfer(T, D, b, e1, e2)
                a.add(D, r, e2, e3)
                rg = [a.fresh("g") for _ in range(b)]
                a.divide(G, T, b, e3, rg)
                for r2 in range(b):
                    f1, f2, f3, f4 = (a.fresh() for _ in range(4))
                    a.here(rg[r2])
                    a.dec_zero(f1)
                    a.transfer(T, G, 1, f1, f2)
                    a.transfer(D, T, b, f2, f3)
                    a.add(T, r2, f3, f4)
                    a.transfer(T, D, 1, f4, start[q2])
            else:
                # write: d := b*t + code(action)
                a.transfer(T, D, b, e1, e2)
                a.add(D, codes[action], e2, start[q2])
    return a.assemble(), codes, b


def initial_values(codes, b, args):
    tape = initial_tape(args)
    d = sum(codes[s] * b ** i for i, s in tape.items())
    return [0, d, 0, 0]


def tape_from_counters(g, d, b, codes):
    symb = {c: s for s, c in codes.items()}
    tape, i = {}, 0
    while d:
        d, r = divmod(d, b)
        if r:
            tape[i] = symb[r]
        i += 1
    i = -1
    while g:
        g, r = divmod(g, b)
        if r:
            tape[i] = symb[r]
        i -= 1
    return tape


# --------------------------------------------------------------------------- stage 2
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
A, B = 0, 1


def two_counters(program, k):
    """Translates a program with k counters into a program with two counters A, B:
    the content (c_0, ..., c_{k-1}) is stored in A = 2^c0 3^c1 5^c2 ..., B being 0 between two fragments."""
    a = Assembler()
    st = ["i%d" % n for n in range(len(program))]
    for n, ins in enumerate(program):
        if ins[0] == "STOP":
            a.here(st[n])
            a.stop()
            continue
        if ins[0] == "DEC" and ins[2] == ins[3]:
            # plain jump: B is 0, so DEC(B) always fails
            a.here(st[n])
            a.dec(B, st[ins[2]], st[ins[2]])
            continue
        p = PRIMES[ins[1]]
        if ins[0] == "INC":
            # A := p*A: A is emptied into B multiplying by p, then B into A
            m = a.fresh()
            a.transfer(A, B, p, st[n], m)
            a.transfer(B, A, 1, m, st[ins[2]])
            continue
        # DEC: B := A // p; the remainder rho is known from the instruction where the division stops
        rems = [a.fresh("rho") for _ in range(p)]
        a.divide(A, B, p, st[n], rems)
        # remainder 0: the counter was > 0; A := A / p, then success
        a.transfer(B, A, 1, rems[0], st[ins[2]])
        for r in range(1, p):
            # remainder r > 0: the counter was 0; A = p*B + r is rebuilt, then failure
            e = a.fresh()
            a.add(A, r, rems[r], e)
            a.transfer(B, A, p, e, st[ins[3]])
    return a.assemble()


# --------------------------------------------------------------------------- checking
def two_counters_from_turing(machine):
    prog3, codes, b = three_counters(machine)
    prog2 = two_counters(prog3, 4)
    return prog3, prog2, codes, b


def compare(machine, *args, two=True):
    """Runs the Turing machine, the three-counter machine and the two-counter machine,
    and checks that the final tape is the same. Returns a dictionary of measurements."""
    c = machine.run(*args)
    expected = {i - c.position: s for i, s in c.tape.items() if s != BLANK}
    prog3, codes, b = three_counters(machine)
    v0 = initial_values(codes, b, args)
    m3 = CounterMachine(prog3, v0)
    v3, steps3, _ = m3.run(v0)
    assert v3[T] == 0 and v3[Z] == 0
    assert tape_from_counters(v3[G], v3[D], b, codes) == expected, "three counters: different tape"
    res = {"turing_steps": c.steps, "strokes": c.number_of_strokes(), "instr3": len(prog3), "steps3": steps3,
           "base": b, "start3": v0}
    if two:
        prog2 = two_counters(prog3, 4)
        a0 = 2 ** v0[G] * 3 ** v0[D] * 5 ** v0[T] * 7 ** v0[Z]
        v2, steps2, it2 = CounterMachine(prog2, [a0, 0]).run([a0, 0])
        assert v2[1] == 0
        A_final, e = v2[0], [0, 0, 0, 0]
        for k, p in enumerate(PRIMES[:4]):
            while A_final % p == 0:
                A_final //= p
                e[k] += 1
        assert A_final == 1 and e == v3, "two counters: different content"
        res.update({"instr2": len(prog2), "steps2": steps2, "iterations2": it2, "start2": a0})
    return res


def _main(argv):
    import os
    if len(argv) >= 2:
        machine = Machine.from_file(argv[1])
        args = [int(x) for x in argv[2:]]
    else:
        machine = Machine.from_file(os.path.join(os.path.dirname(os.path.abspath(__file__)), "examples", "addition.tm"))
        args = [2, 1]
    r = compare(machine, *args)
    print("Turing machine: %d quadruples, %d steps, result %d." % (len(machine), r["turing_steps"], r["strokes"]))
    print("Three counters (base %d): %d instructions; start (g, d, t) = (%d, %d, %d); %d steps."
          % (r["base"], r["instr3"], r["start3"][0], r["start3"][1], r["start3"][2], r["steps3"]))
    p2 = str(r["steps2"])
    print("Two counters: %d instructions; start A = 2^%d 3^%d (%d digits); %s steps (%d digits)."
          % (r["instr2"], r["start3"][0], r["start3"][1], len(str(r["start2"])), p2 if len(p2) < 30 else p2[:12] + "…", len(p2)))
    print("The three runs give the same final tape.")


if __name__ == "__main__":
    _main(sys.argv)
