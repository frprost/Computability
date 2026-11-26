#!/usr/bin/env python3
"""The halting problem: the diagonal argument, run (chapter "Undecidability" of the manual).

We are given a candidate "decider": a Python function decide(source, x) that claims to
answer True if the program with text `source` halts on input x, False otherwise.
paradox(decide) builds the program D that
    - obtains its own text (recursion theorem: see recursion.py),
    - asks the decider "does D halt on its own text?",
    - does the opposite: loops forever if the answer is yes, halts if it is no.
Whatever the candidate, it is wrong about D. The program observes this for several
candidates, including one that simulates the program for a fixed number of steps.

A "never-ending" run cannot be watched to its end: we run it with a
budget of steps and observe that it has not halted. For D, the text of the program
shows directly that it loops ("while True: pass").

    python3 halting.py

MIT licence. Frédéric Prost and Claude.
"""
import sys
import textwrap

from recursion import fixed_point


class BudgetExhausted(Exception):
    pass


def launch(source, x, budget=200000):
    """Runs the function program(x) defined by `source`, with at most `budget` lines executed.
    Returns ("halts", value) or ("no halt within the budget", None)."""
    env = {}
    exec(source, env)
    counter = [0]

    def trace(frame, event, arg):
        if event == "line":
            counter[0] += 1
            if counter[0] > budget:
                raise BudgetExhausted()
        return trace

    old = sys.gettrace()
    sys.settrace(trace)
    try:
        v = env["program"](x)
        return "halts", v
    except BudgetExhausted:
        return "no halt within the budget", None
    finally:
        sys.settrace(old)


def paradox(decider_source):
    """Text of the diagonal program D associated with the decider (given by its text, which defines decide)."""
    body = decider_source + textwrap.dedent("""
        def program(x):
            if decide(SELF, SELF):
                while True:
                    pass
            return 0
        """)
    return fixed_point(body)


CANDIDATES = {
    "always answers yes": "def decide(source, x):\n    return True\n",
    "always answers no": "def decide(source, x):\n    return False\n",
    "looks for the word 'while' in the text": "def decide(source, x):\n    return 'while' not in source\n",
    "simulates 1000 lines and concludes": textwrap.dedent("""\
        def decide(source, x):
            # Runs the program for at most 1000 lines (nested simulations included):
            # if it has halted, answer yes; otherwise, answer no.
            import sys
            outer = not hasattr(sys, "_decide_budget")
            if outer:
                sys._decide_budget = [0]
            n = sys._decide_budget
            env = {}
            exec(source, env)
            class Stop(Exception):
                pass
            def t(f, e, a):
                if e == "line":
                    n[0] += 1
                    if n[0] > 1000:
                        raise Stop()
                return t
            old = sys.gettrace()
            sys.settrace(t)
            try:
                env["program"](x)
                return True
            except Stop:
                return False
            finally:
                sys.settrace(old)
                if outer:
                    del sys._decide_budget
        """),
}


def _main():
    for name, dec in CANDIDATES.items():
        D = paradox(dec)
        env = {}
        exec(D, env)
        answer = env["decide"](D, D)
        status, _ = launch(D, D)
        print("Candidate \"%s\"" % name)
        print("   it claims that D %s on its own text" % ("halts" if answer else "does not halt"))
        print("   in fact, D: %s" % status)
        right = (answer and status == "halts") or (not answer and status != "halts")
        print("   the candidate is wrong: %s\n" % ("no" if right else "yes"))
        assert not right
    print("No candidate escapes its diagonal program: this is Turing's theorem (1936).")


if __name__ == "__main__":
    _main()
