#!/usr/bin/env python3
"""Compiler: recursive functions -> Turing machines (chapter "Equivalence" of the manual).

The program follows the proof of the theorem "every recursive function is Turing-computable"
to the letter. We fix a STACK DISCIPLINE:
  - the tape holds blocks of strokes separated by ONE blank: 1^{a1+1} B 1^{a2+1} B ... B 1^{ar+1};
  - E denotes the cell two cells after the last stroke (where a new block would begin).
A machine PUSHES f if, started at E on a tape whose last n blocks code x1..xn,
it comes back to E with one more block, which codes f(x1..xn), without touching the earlier blocks
(and never comes back if f(x) is undefined).

We build, by induction on the term, a machine that pushes f, out of auxiliary machines
(the "macros"): go_to_E, go_to_block, push, copy, shift, delete, incr, decr, zero.
Each macro receives the state where it begins and returns the state where it ends; chaining two macros
means giving the exit state of the first as the entry state of the second.

Usage:
    python3 compiler.py add 2 3                    compiles, runs, compares with the evaluation
    python3 compiler.py "rho[C(0,1), sigma[mult, sigma[S, A(2,1)], A(2,2)]]" 3
    python3 compiler.py mult 2 3 --output mult.tm  writes the machine to a file
    python3 compiler.py mult --output mult.tm      compiles only
    python3 machines.py mult.tm 2 3                then runs it, independently

MIT licence. Frédéric Prost and Claude.
"""
import sys

from machines import Machine, BLANK as B, STROKE as I
from recursive import Const, Succ, Proj, Comp, Rec, Mu, Named, read_term, evaluate, Diverges, unfold

X = "X"                    # auxiliary mark used by the copy
SYMBOLS = (B, I, X)


class Assembler:
    """Accumulates quadruples and makes up fresh state names."""

    def __init__(self, comment=False):
        self.quads = []
        self.n = 0
        self.comment = comment

    def fresh(self, prefix="s"):
        self.n += 1
        return "%s%d" % (prefix, self.n)

    def q(self, state, read, action, following):
        self.quads.append((state, read, action, following))

    def link(self, a, b):
        """Go from state a to state b without changing anything: a s s b for each symbol s."""
        for s in SYMBOLS:
            self.q(a, s, s, b)

    # ------------------------------------------------------------ moves
    def go_to_E(self, e):
        """End: from a cell of the content (stroke, X or separator), go to E.
        We move right until two consecutive blanks are found; the head stops on the second."""
        b, s = self.fresh("end"), self.fresh("end")
        self.q(e, I, "R", e)
        self.q(e, X, "R", e)
        self.q(e, B, "R", b)
        self.q(b, I, "R", e)
        self.q(b, X, "R", e)
        self.q(b, B, B, s)
        return s

    def go_to_block(self, e, j):
        """Block_j: from E, go to the first stroke of the j-th block counted from the end."""
        c = self.fresh("block")
        self.q(e, B, "L", c)                    # on the separator after the last block
        for t in range(1, j + 1):
            l = self.fresh("block")
            self.q(c, B, "L", l)                # on the last stroke of the block
            self.q(l, I, "L", l)                # we go back up the block
            if t < j:
                c = self.fresh("block")
                self.q(l, B, B, c)              # separator: next block (to the left)
            else:
                s = self.fresh("block")
                self.q(l, B, "R", s)            # we come back to the first stroke
                return s

    # ------------------------------------------------------------ stack operations
    def push(self, e, m):
        """Push_m: write m+1 strokes from E on, then go to the new E."""
        cur = e
        for _ in range(m + 1):
            w, nx = self.fresh("push"), self.fresh("push")
            self.q(cur, B, I, w)
            self.q(w, I, "R", nx)
            cur = nx
        s = self.fresh("push")
        self.q(cur, B, "R", s)
        return s

    def copy(self, e, j):
        """Copy_j: push a copy of the j-th block from the end.
        For each stroke of the source: replace it with X, go to the end, write a stroke there,
        come back to the X, put the stroke back, move on to the next stroke."""
        s = self.go_to_block(e, j)
        c1 = self.fresh("copy")
        self.q(s, I, X, c1)                      # first stroke marked
        e1 = self.go_to_E(c1)
        r = self.fresh("copy")
        self.q(e1, B, I, r)                      # first stroke of the copy, written at E
        self.q(r, I, "L", r)                     # back towards the mark
        self.q(r, B, "L", r)
        r1, r2 = self.fresh("copy"), self.fresh("copy")
        self.q(r, X, I, r1)                      # restore the marked stroke
        self.q(r1, I, "R", r2)                   # next stroke of the source
        d = self.fresh("copy")
        self.q(r2, I, X, d)                      # one more stroke: mark it
        e2 = self.go_to_E(d)                     # E is two cells after the copy in progress
        e3 = self.fresh("copy")
        self.q(e2, B, "L", e3)                   # we step back one cell to extend the copy
        self.q(e3, B, I, r)
        f = self.fresh("copy")
        self.q(r2, B, B, f)                      # end of the source
        return self.go_to_E(f)

    def shift(self, g, k):
        """Shift_k: the head is on a hole (two blanks) followed by k blocks;
        shift these k blocks one cell to the left (the hole is filled)."""
        cur = g
        for _ in range(k):
            a, b, c, d = self.fresh("shift"), self.fresh("shift"), self.fresh("shift"), self.fresh("shift")
            self.q(cur, B, "R", a)
            self.q(a, B, I, b)                   # write a stroke in the hole
            self.q(b, I, "R", b)                 # cross the block
            self.q(b, B, "L", c)
            self.q(c, I, B, d)                   # erase its last stroke: it has moved back one cell
            cur = d
        s = self.fresh("shift")
        self.q(cur, B, "R", s)
        return s

    def decr(self, e, j):
        """Decr_j: remove one stroke from the j-th block (which codes an integer > 0)."""
        s = self.go_to_block(e, j)
        p = self.fresh("decr")
        self.link(s, p)
        self.q(p, I, "R", p)                     # go to the last stroke of the block
        p2, z = self.fresh("decr"), self.fresh("decr")
        self.q(p, B, "L", p2)
        self.q(p2, I, B, z)                      # erase it: a hole of two blanks appears
        return self.shift(z, j - 1)              # glue back the j-1 blocks that follow

    def delete(self, e, j):
        """Delete_j: delete the j-th block from the end, stroke by stroke, gluing back what follows."""
        loop = e
        s = self.go_to_block(loop, j)
        p = self.fresh("del")
        self.link(s, p)
        self.q(p, I, "R", p)
        p2, z = self.fresh("del"), self.fresh("del")
        self.q(p, B, "L", p2)
        self.q(p2, I, B, z)                      # erase the last stroke of the block
        p4 = self.fresh("del")
        self.q(z, B, "L", p4)                    # is there a stroke left to the left?
        z2 = self.fresh("del")
        self.q(p4, I, "R", z2)                   # yes: come back, glue back what follows, start again
        back = self.shift(z2, j - 1)
        self.link(back, loop)
        w = self.fresh("del")
        self.q(p4, B, B, w)                      # no: the block is empty, a hole remains
        if j == 1:
            s1 = self.fresh("del")
            self.q(w, B, "R", s1)
            return s1
        z3 = self.fresh("del")
        self.q(w, B, "R", z3)
        e1 = self.shift(z3, j - 1)               # first shift
        s2 = self.go_to_block(e1, j - 1)         # beginning of the block after the hole
        g1, g = self.fresh("del"), self.fresh("del")
        self.q(s2, I, "L", g1)
        self.q(g1, B, "L", g)
        return self.shift(g, j - 1)              # second shift: the extra separator disappears

    def incr(self, e):
        """Incr: add one stroke to the last block."""
        t, u, v, s = self.fresh("inc"), self.fresh("inc"), self.fresh("inc"), self.fresh("inc")
        self.q(e, B, "L", t)
        self.q(t, B, I, u)
        self.q(u, I, "R", v)
        self.q(v, B, "R", s)
        return s

    def zero(self, e, j):
        """Zero?_j: returns (state if the j-th block codes 0, state otherwise), both at E."""
        s = self.go_to_block(e, j)
        a, z, nz = self.fresh("zero"), self.fresh("zero"), self.fresh("zero")
        self.q(s, I, "R", a)
        self.q(a, B, B, z)                       # a single stroke: the block codes 0
        self.q(a, I, I, nz)
        return self.go_to_E(z), self.go_to_E(nz)

    # ------------------------------------------------------------ the compilation itself
    def compile(self, e, f):
        """Machine that pushes f, starting in e; returns its exit state."""
        while isinstance(f, Named):
            f = f.term
        if isinstance(f, Const):                 # m^(k): Push_m
            return self.push(e, f.m)
        if isinstance(f, Succ):                  # S: Copy_1 then Incr
            return self.incr(self.copy(e, 1))
        if isinstance(f, Proj):                  # A^(k)_i: Copy_{k-i+1}
            return self.copy(e, f.k - f.i + 1)
        if isinstance(f, Comp):                  # sigma[g, h1..hk]
            m, k, cur = f.arity(), len(f.hs), e
            for j, h in enumerate(f.hs, start=1):
                for _ in range(m):               # copy of the m arguments (y1..y_{j-1} are above)
                    cur = self.copy(cur, m + j - 1)
                cur = self.compile(cur, h)       # pushes y_j = h_j(x)
                for _ in range(m):               # deletes the copies, below y_j
                    cur = self.delete(cur, 2)
            cur = self.compile(cur, f.g)         # pushes g(y1..yk)
            for _ in range(k):
                cur = self.delete(cur, 2)        # deletes y1..yk
            return cur
        if isinstance(f, Rec):                   # rho[g, h]; stack: y, x2..xk
            kk, cur = f.arity(), e
            cur = self.copy(cur, kk)             # c := y
            cur = self.push(cur, 0)              # i := 0
            for _ in range(kk - 1):
                cur = self.copy(cur, kk + 1)     # copies of x2..xk
            cur = self.compile(cur, f.g)         # a := g(x)
            for _ in range(kk - 1):
                cur = self.delete(cur, 2)
            loop = cur                           # stack: ..., c, i, a
            done, go_on = self.zero(loop, 3)
            end = self.delete(self.delete(done, 3), 2)   # c = 0: a remains
            cur = self.decr(go_on, 3)            # c := c - 1
            cur = self.copy(cur, 2)              # i
            cur = self.copy(cur, 2)              # a
            for _ in range(kk - 1):
                cur = self.copy(cur, kk + 4)     # x2..xk
            cur = self.compile(cur, f.h)         # r := h(i, a, x)
            for _ in range(kk + 1):
                cur = self.delete(cur, 2)        # deletes the copies
            cur = self.copy(cur, 3)              # i
            cur = self.incr(cur)                 # i + 1
            cur = self.copy(cur, 2)              # r
            for _ in range(3):
                cur = self.delete(cur, 3)        # deletes the old i, the old a, and the duplicate r
            self.link(cur, loop)                 # back to the head of the loop
            return end
        if isinstance(f, Mu):                    # mu[g]; stack: x1..xn
            n, cur = f.arity(), self.push(e, 0)  # z := 0
            loop = cur
            for _ in range(n + 1):
                cur = self.copy(cur, n + 1)      # copies of x1..xn, z
            cur = self.compile(cur, f.g)         # r := g(x, z)
            for _ in range(n + 1):
                cur = self.delete(cur, 2)
            yes, no = self.zero(cur, 1)
            end = self.delete(yes, 1)            # r = 0: z is the result
            again = self.incr(self.delete(no, 1))   # otherwise z := z + 1
            self.link(again, loop)
            return end
        raise TypeError("unknown term: %r" % (f,))


def compile(f, rename=True):
    """Turing machine Z_f, in the format of chapter 3: Psi_{Z_f} = f.

    The machine goes to E, pushes f(x), deletes the n arguments, and removes one stroke from the result
    (f(x) strokes then remain, the output convention)."""
    a = Assembler()
    e = a.go_to_E("q0")
    e = a.compile(e, f)
    for _ in range(f.arity()):
        e = a.delete(e, 2)
    t, u, x = a.fresh("last"), a.fresh("last"), a.fresh("last")
    a.q(e, B, "L", t)
    a.q(t, B, "L", u)
    a.q(u, I, B, x)
    quads = a.quads
    if rename:                                   # q0, q1, q2... in order of appearance
        names = {"q0": "q0"}
        for qd in quads:
            for s in (qd[0], qd[3]):
                if s not in names:
                    names[s] = "q%d" % len(names)
        quads = [(names[a_], s, act, names[b_]) for a_, s, act, b_ in quads]
    return Machine(quads)


def _main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    output = None
    if "--output" in argv:
        k = argv.index("--output")
        output = argv[k + 1]
        argv = argv[:k] + argv[k + 2:]
    f = read_term(argv[1])
    args = [int(a) for a in argv[2:]]
    m = compile(f)
    print("term     :", unfold(f))
    print("machine  : %d quadruples, %d states" % (len(m), len(m.states())))
    if output:
        with open(output, "w", encoding="utf-8") as fh:
            fh.write("# Machine compiled from %s\n" % unfold(f))
            fh.write(m.to_text())
        print("written to", output)
    if args or f.arity() == 0:
        c = m.run(*args, max_steps=10**9)
        print("run      : %d steps, result %d" % (c.steps, c.number_of_strokes()))
        try:
            print("direct evaluation of the term:", evaluate(f, args))
        except Diverges:
            print("direct evaluation of the term: no answer")
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
