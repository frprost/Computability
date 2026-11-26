#!/usr/bin/env python3
"""The s-m-n theorem and the recursion theorem, carried out (chapter "s-m-n and recursion" of the manual).

1. s-m-n on Turing machines. From a machine Z that computes f(a, y) and an integer a,
   smn(Z, a) builds a machine that computes y -> f(a, y): it writes the block of a in front of
   its input, comes back to its first stroke, then runs Z. The construction is itself
   a computation (a function of a), which is the whole content of the theorem.

2. Fixed point (Kleene's recursion theorem) on Python programs. fixed_point(body)
   returns the text of a program that has, in the variable SELF, its own complete
   text, then runs body. With body = "print(SELF, end='')" we get a program that
   prints its own text (a "quine"). The construction is that of the proof: a
   template applied to its own description, like s(e, e) in the proof.

    python3 recursion.py                 demonstrations
    python3 recursion.py --quine         prints a quine (to save and run)

MIT licence. Frédéric Prost and Claude.
"""
import io
import contextlib
import sys

from machines import Machine, BLANK as B, STROKE as I


# ------------------------------------------------------------------ s-m-n
def smn(machine, a):
    """Machine that, on input y, computes what `machine` computes on (a, y)."""
    ren = {q: "z_" + q for q in machine.states()}
    quads = []
    # from the first stroke of y: step back onto the separator, then one more cell
    quads.append(("q0", I, "L", "w0"))
    quads.append(("w0", B, "L", "w1"))
    # write a+1 strokes towards the left
    for t in range(1, a + 2):
        quads.append(("w%d" % t, B, I, "v%d" % t))
        quads.append(("v%d" % t, I, "L", "w%d" % (t + 1)))
    # one cell too far: come back to the first stroke of the block of a, and start the machine
    quads.append(("w%d" % (a + 2), B, "R", ren[machine.initial_state]))
    quads += [(ren[q], s, act, ren[q2]) for q, s, act, q2 in machine.quadruples]
    return Machine(quads, "q0")


# ------------------------------------------------------------------ fixed point
MARK = "@" + "@"


def fixed_point(body):
    """Text P of a Python program that, when run, puts its own text in SELF and then runs body.

    Template T = "_T = @@ ; SELF = _T.replace(mark, repr(_T)) ; body".
    P = T with @@ replaced by repr(T). When it runs, _T equals T, so SELF equals P."""
    if MARK in body:
        raise ValueError("the body must not contain the mark")
    template = "_T = %s\nSELF = _T.replace('@' + '@', repr(_T))\n%s\n" % (MARK, body)
    return template.replace(MARK, repr(template))


def run(source, **variables):
    """Runs the text of a program and returns what it prints."""
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        exec(source, dict(variables))
    return output.getvalue()


def _demonstration():
    from compiler import compile
    from recursive import add, mult
    print("1. s-m-n on Turing machines")
    for f, name in ((add, "add"), (mult, "mult")):
        Z = compile(f)
        for a in (0, 2, 3):
            Za = smn(Z, a)
            vals = [Za.compute(y) for y in range(4)]
            expected = [f(a, y) for y in range(4)]
            assert vals == expected
            print("   %s(%d, y) for y = 0..3: %s   (machine of %d quadruples, %d more than Z)"
                  % (name, a, vals, len(Za), len(Za) - len(Z)))
    print()
    print("2. A quine: a program that prints its own text")
    q = fixed_point("print(SELF, end='')")
    print("   " + q.replace("\n", "\n   "))
    assert run(q) == q
    print("   checked: its output is exactly its text.")
    print()
    print("3. A program that uses its own text: it prints its length and its number of lines")
    p = fixed_point("print(len(SELF), SELF.count(chr(10)))")
    print("   output:", run(p).strip(), "  actual length:", len(p), p.count("\n"))


if __name__ == "__main__":
    if "--quine" in sys.argv:
        print(fixed_point("print(SELF, end='')"), end="")
    else:
        _demonstration()
