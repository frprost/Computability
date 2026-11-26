#!/usr/bin/env python3
"""A universal function, then a universal Turing machine, built from end to end.

1. Every machine Z is coded by an integer code(Z) (Cantor pairs, see below).
2. We write ONE recursive term U(e, x), made only of the building blocks C, S, A, sigma, rho, mu,
   such that U(code(Z), x) = Psi_Z(x) for every machine Z (same domain of definition).
   It is the same construction as in turing_to_recursive.py, but the machine is no longer
   fixed: its table of quadruples is read from the argument e. The chapter "Universality" of the
   manual gives the proof; this file carries it out.
3. We compile U with compiler.py: we obtain a universal Turing machine U_TM,
   such that U_TM, started on (code(Z), x), computes Psi_Z(x).

Coding a machine with b symbols (0 = B, 1 = stroke, 2, ...) and k states (0 = q0, 1, ...):
  action        : 0 = L, 1 = R, 2 + j = write the symbol j
  table         : an integer written in base N = (b+2)·k + 1; its digit of rank i·b + s is
                  0 if no quadruple begins with (q_i, s), and action·k + i2 + 1 for (q_i, s, action, q_i2)
  machine       : <b, <k, table>>
(A coding by lists of nested Cantor pairs would also do in theory, but its
numbers double in length with each quadruple: 3 million binary digits for 16
quadruples. The table in base N has a length proportional to the number of quadruples.)

Usage:
    python3 universal.py                      demonstration: U simulates several machines
    python3 universal.py --machine            compiles U into a Turing machine (about 1 min 30) and gives its size
    python3 universal.py --machine --write    ... and writes it to universal.tm (about 680 MB)
    python3 universal.py file.tm 3            code(Z) then U(code(Z), 3)

MIT licence. Frédéric Prost and Claude.
"""
import sys

import recursive as r
from recursive import App, function, recursion, minimization
from machines import Machine, BLANK, STROKE
from turing_to_recursive import cases

G, D = r.left, r.right


def conf(g, i, d):
    return App(r.pair, g, App(r.pair, i, d))


# --- reading the code of the machine: e = <b, <k, table>>
nb_symbols = function(1, lambda e: App(G, e), "nb_symbols")
nb_states = function(1, lambda e: App(G, App(D, e)), "nb_states")
table = function(1, lambda e: App(D, App(D, e)), "table")
# base of the table: N = (b + 2)·k + 1 (an entry is 0, or action·k + i2 + 1)
base = function(1, lambda e: App(r.add, App(r.mult, App(r.add, App(nb_symbols, e), 2), App(nb_states, e)), 1), "base")
# configuration <g, <i, d>>
cg = function(1, lambda c: App(G, c), "cg")
ci = function(1, lambda c: App(G, App(D, c)), "ci")
cd = function(1, lambda c: App(D, App(D, c)), "cd")
scanned = function(2, lambda e, c: App(r.rem, App(cd, c), App(nb_symbols, e)), "scanned")

# --- the table entry for (state i, symbol s): the digit of rank i·b + s of the table, in base N.
lookup = function(3, lambda e, i, s: App(r.rem,
                                         App(r.quot, App(table, e),
                                             App(r.power, App(base, e), App(r.add, App(r.mult, i, App(nb_symbols, e)), s))),
                                         App(base, e)), "lookup")


def _step(e, c):
    b = App(nb_symbols, e)
    res = App(lookup, e, App(ci, c), App(scanned, e, c))
    act = App(r.quot, App(r.pred, res), App(nb_states, e))
    i2 = App(r.rem, App(r.pred, res), App(nb_states, e))
    g, d, s = App(cg, c), App(cd, c), App(scanned, e, c)
    left_ = conf(App(r.quot, g, b), i2, App(r.add, App(r.mult, d, b), App(r.rem, g, b)))
    right_ = conf(App(r.add, App(r.mult, g, b), s), i2, App(r.quot, d, b))
    write = conf(g, i2, App(r.add, App(r.monus, d, s), App(r.monus, act, 2)))
    found = App(r.sg, res)
    return cases([(App(r.conj, found, App(r.eq, act, 0)), left_),
                  (App(r.conj, found, App(r.eq, act, 1)), right_),
                  (App(r.conj, found, App(r.less, 1, act)), write)], c)


stepU = function(2, _step, "stepU")
haltU = function(2, lambda e, c: App(r.sgbar, App(lookup, e, App(ci, c), App(scanned, e, c))), "haltU")
iterU = recursion(3, lambda e, c: c, lambda t, acc, e, c: App(stepU, e, acc), "iterU")
# rep(x, b) = 1 + b + ... + b^x: the tape 1^{x+1}
repU = recursion(2, lambda b: 1, lambda y, acc, b: App(r.add, App(r.mult, acc, b), 1), "repU")
initU = function(2, lambda e, x: conf(0, 0, App(repU, x, App(nb_symbols, e))), "initU")
countU = recursion(3, lambda m, b: App(r.pair, m, 0),
                   lambda k, p, m, b: App(r.pair, App(r.quot, App(G, p), b),
                                          App(r.add, App(D, p), App(r.eq, App(r.rem, App(G, p), b), 1))),
                   "countU")
strokesU = function(4, lambda e, t, c, x: App(r.add,
                                              App(D, App(countU, App(r.add, t, App(r.add, x, 2)), App(cg, c), App(nb_symbols, e))),
                                              App(D, App(countU, App(r.add, t, App(r.add, x, 2)), App(cd, c), App(nb_symbols, e)))),
                    "strokesU")
timeU = minimization(2, lambda e, x, t: App(r.neg, App(haltU, e, App(iterU, t, e, App(initU, e, x)))), "timeU")
U = function(2, lambda e, x: App(strokesU, e, App(timeU, e, x), App(iterU, App(timeU, e, x), e, App(initU, e, x)), x), "U")


def code_machine(m):
    """The integer code(Z) = <b, <k, table>> of a machine of the simulator."""
    syms = [BLANK, STROKE] + sorted(m.symbols() - {BLANK, STROKE})
    states = [m.initial_state] + sorted(m.states() - {m.initial_state})
    ns = {s: k for k, s in enumerate(syms)}
    ne = {q: k for k, q in enumerate(states)}
    b, k = len(syms), len(states)
    N = (b + 2) * k + 1
    tab = 0
    for q, s, a, q2 in m.quadruples:
        act = 0 if a == "L" else 1 if a == "R" else 2 + ns[a]
        tab += (act * k + ne[q2] + 1) * N ** (ne[q] * b + ns[s])
    return r.cantor(b, r.cantor(k, tab))


EXAMPLES = {
    "identity (erases a stroke)": "q0 1 B q1",
    "successor": "q0 B B q0",
    "round trip (identity, 7 quadruples)": "q0 1 R q0\nq0 B 1 q1\nq1 1 L q1\nq1 B R q2\nq2 1 B q3\nq3 B R q4\nq4 1 B q5",
    "predecessor": "q0 1 B q1\nq1 B R q2\nq2 1 B q3",
}


def _main(argv):
    if len(argv) >= 2 and argv[1] == "--machine":
        from compiler import compile
        print("term U: %d building blocks once unfolded, a single unbounded minimization" % r.size(U))
        m = compile(U)
        print("universal machine: %d quadruples, %d states, symbols B, 1, X" % (len(m), len(m.states())))
        if "--write" in argv:   # about 680 MB
            with open("universal.tm", "w", encoding="utf-8") as f:
                f.write("# Universal Turing machine obtained by compiling the term U of universal.py\n")
                f.write("# Input: code(Z), x  (two blocks of strokes).  Output: Psi_Z(x) strokes.\n")
                f.write(m.to_text())
            print("written to universal.tm")
        else:
            print("(add --write to write it to universal.tm: about 680 MB)")
        return 0
    if len(argv) >= 3:
        m = Machine.from_file(argv[1])
        x = int(argv[2])
        e = code_machine(m)
        print("code(Z) =", e)
        print("U(code(Z), %d) = %d   (the machine gives %d)" % (x, U(e, x), m.compute(x)))
        return 0
    print("term U: %d building blocks once unfolded\n" % r.size(U))
    for name, text in EXAMPLES.items():
        m = Machine.from_text(text)
        e = code_machine(m)
        for x in range(4):
            v = U(e, x)
            assert v == m.compute(x), (name, x)
        print("%-36s code = %s..." % (name, str(e)[:40]))
        print("%-36s U(code, x) for x = 0..3: %s" % ("", [U(e, x) for x in range(4)]))
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
