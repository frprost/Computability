#!/usr/bin/env python3
"""Translation: Turing machine -> recursive function (chapter "Equivalence", converse direction).

For a given machine Z, we build EXPLICITLY a term f_Z, made only of constants,
successor, projections, substitution, primitive recursion and ONE minimization, such that
f_Z(x1..xn) = Psi_Z(x1..xn) (same domain of definition). This is Kleene's normal form,
with a more economical coding than the prime-power coding of the manual
(both work: what matters is that each stage be primitive recursive).

Coding a configuration (tape, position, state) by ONE integer:
  - the symbols are numbered 0 (= B), 1 (= stroke), 2, ...; b is the number of symbols;
  - d codes the right part of the tape, from the scanned cell on, in base b, the scanned cell being
    the units digit: d = s0 + s1·b + s2·b² + ...
  - g codes the left part, the cell just left of the head being the units digit;
  - the state q_i is coded by its number i;
  - the configuration is the Cantor pair <g, <i, d>>.
A tape carries only finitely many non-blank symbols: g and d are integers.

The functions built (all primitive recursive except the last one):
  scanned(c)     = d mod b                      scanned symbol
  step(c)        = next configuration (c itself if no quadruple applies)
  halt(c)        = 1 if no quadruple applies, 0 otherwise
  iter(t, c)     = step applied t times to c    (primitive recursion on t)
  init(x1..xn)   = initial configuration q0 1^{x1+1} B ... B 1^{xn+1}
  strokes(t, c)  = number of strokes on the tape coded by c (reading at most L digits)
  time(x)        = mu t [ halt(iter(t, init(x))) = 1 ]      the only minimization
  f_Z(x)         = strokes(time(x), iter(time(x), init(x)))

Usage:
    python3 turing_to_recursive.py file.tm 2 3      builds f_Z, evaluates it, compares with Z
    python3 turing_to_recursive.py --example        on the addition machine of chapter 3

MIT licence. Frédéric Prost and Claude.
"""
import sys

import recursive as r
from recursive import App, function, recursion, minimization
from machines import Machine, BLANK, STROKE


def total(terms):
    """Sum written as a balanced tree of additions (logarithmic depth)."""
    if len(terms) == 1:
        return terms[0]
    m = len(terms) // 2
    return App(r.add, total(terms[:m]), total(terms[m:]))


def cases(conditions_values, default):
    """Definition by disjoint cases: sum of the [condition]·value, plus [no condition]·default.
    (One could write cond(c1, v1, cond(c2, v2, ...)); the sum avoids too deep a nesting.)"""
    conds = [c for c, _ in conditions_values]
    none_ = App(r.neg, total(conds)) if conds else 1
    return total([App(r.mult, c, v) for c, v in conditions_values] + [App(r.mult, none_, default)])


class Translation:
    """All the terms associated with a machine Z."""

    def __init__(self, machine, arity=1):
        self.machine = machine
        self.n = arity
        syms = [BLANK, STROKE] + sorted(machine.symbols() - {BLANK, STROKE})
        states = [machine.initial_state] + sorted(machine.states() - {machine.initial_state})
        self.sym = {s: k for k, s in enumerate(syms)}
        self.state = {q: k for k, q in enumerate(states)}
        self.b = b = len(syms)
        self.symbols, self.states = syms, states

        # --- decoding a configuration c = <g, <i, d>>
        G = r.left
        D = r.right
        self.cg = function(1, lambda c: App(G, c))
        self.ci = function(1, lambda c: App(G, App(D, c)))
        self.cd = function(1, lambda c: App(D, App(D, c)))
        cg, ci, cd = self.cg, self.ci, self.cd
        self.scanned = function(1, lambda c: App(r.rem, App(cd, c), b), "scanned")
        scanned = self.scanned

        def conf(g, i, d):
            return App(r.pair, g, App(r.pair, i, d))

        # --- one computation step: definition by cases, one case per quadruple
        def new(c, quad):
            q, s, a, q2 = quad
            i2 = self.state[q2]
            if a == "R":     # the scanned cell moves to the left part
                return conf(App(r.add, App(r.mult, App(cg, c), b), App(scanned, c)), i2, App(r.quot, App(cd, c), b))
            if a == "L":     # the cell to the left becomes the scanned cell
                return conf(App(r.quot, App(cg, c), b), i2, App(r.add, App(r.mult, App(cd, c), b), App(r.rem, App(cg, c), b)))
            # writing: the units digit of d goes from sym[s] to sym[a]
            return conf(App(cg, c), i2, App(r.add, App(r.monus, App(cd, c), self.sym[s]), self.sym[a]))

        def applies(c, quad):
            return App(r.conj, App(r.eq, App(ci, c), self.state[quad[0]]), App(r.eq, App(scanned, c), self.sym[quad[1]]))

        quads = machine.quadruples
        self.step = function(1, lambda c: cases([(applies(c, qd), new(c, qd)) for qd in quads], c), "step")
        no_quad = lambda c: cases([(applies(c, qd), 0) for qd in quads], 1)
        self.halt = function(1, no_quad, "halt")
        step = self.step
        self.iter = recursion(2, lambda c: c, lambda t, acc, c: App(step, acc), "iter")

        # --- initial configuration: rep(x) = 1 + b + ... + b^x codes 1^{x+1}
        self.rep = recursion(1, lambda: 1, lambda y, acc: App(r.add, App(r.mult, acc, b), 1), "rep")
        rep = self.rep
        n = arity

        def d_init(*xs):
            # d = rep(x1) + b^{x1+2} (rep(x2) + b^{x2+2} ( ... rep(xn)))
            e = App(rep, xs[-1])
            for x in reversed(xs[:-1]):
                e = App(r.add, App(rep, x), App(r.mult, App(r.power, b, App(r.add, x, 2)), e))
            return e
        self.init = function(n, lambda *xs: conf(0, 0, d_init(*xs)), "init")

        # --- reading the result: count the digits equal to 1 (at most L digits)
        # digits(L, m) = pair(m', nb) after L rounds of: m' := m' div b ; nb := nb + [m' mod b = 1]
        one = self.sym[STROKE]
        self.count = recursion(2, lambda m: App(r.pair, m, 0),
                               lambda k, p, m: App(r.pair, App(r.quot, App(r.left, p), b),
                                                   App(r.add, App(r.right, p), App(r.eq, App(r.rem, App(r.left, p), b), one))),
                               "count")
        count = self.count
        nb = lambda L, m: App(r.right, App(count, L, m))
        # useful length: t + the sum of the (x_i + 2) bounds the number of cells visited
        self.strokes = function(n + 2, lambda t, c, *xs: App(r.add, nb(self.length(t, xs), App(cg, c)), nb(self.length(t, xs), App(cd, c))), "strokes")

        init, iter_, halt = self.init, self.iter, self.halt
        self.time = minimization(n, lambda *a: App(r.neg, App(halt, App(iter_, a[-1], App(init, *a[:-1])))), "time")
        time = self.time
        self.f = function(n, lambda *xs: App(self.strokes, App(time, *xs), App(iter_, App(time, *xs), App(init, *xs)), *xs), "f_Z")

    def length(self, t, xs):
        e = t
        for x in xs:
            e = App(r.add, e, App(r.add, x, 2))
        return e

    def code_configuration(self, conf):
        """Code <g, <i, d>> of a configuration of the simulator (to check step by step)."""
        b, p = self.b, conf.position
        d = g = 0
        keys = [k for k, v in conf.tape.items() if v != BLANK]
        hi = max(keys + [p])
        lo = min(keys + [p])
        for k in range(hi, p - 1, -1):
            d = d * b + self.sym[conf.tape.get(k, BLANK)]
        for k in range(lo, p):
            g = g * b + self.sym[conf.tape.get(k, BLANK)]
        return r.cantor(g, r.cantor(self.state[conf.state], d))


def check(machine, args, fast=True, max_steps=2000):
    """Checks, step by step, that step follows the simulator exactly, then evaluates f_Z."""
    T = Translation(machine, len(args))
    c = machine.initial_configuration(*args)
    code = r.evaluate(T.init, args, fast)
    assert code == T.code_configuration(c), "initial configuration"
    while machine.step(c):
        code = r.evaluate(T.step, (code,), fast)
        assert code == T.code_configuration(c), "step %d" % c.steps
        if c.steps > max_steps:
            raise RuntimeError("too long for a check")
    assert r.evaluate(T.halt, (code,), fast) == 1
    return T, r.evaluate(T.f, args, fast), c.number_of_strokes()


ADDITION = """q0 1 B q1
q1 B R q2
q2 1 R q2
q2 B R q3
q3 1 B q4"""


def _main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    if argv[1] == "--example":
        m, args = Machine.from_text(ADDITION), [2, 3]
    else:
        m, args = Machine.from_file(argv[1]), [int(a) for a in argv[2:]]
    T, v, expected = check(m, args)
    print("machine          : %d quadruples, %d symbols, %d states" % (len(m), T.b, len(T.states)))
    print("term f_Z         : %d building blocks (fully unfolded)" % r.size(T.f))
    print("  of which step  : %d building blocks; minimizations: 1" % r.size(T.step))
    print("step follows the simulator step by step: yes")
    print("f_Z%s = %d   (the machine gives %d)" % (tuple(args), v, expected))
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
