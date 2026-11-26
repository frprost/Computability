#!/usr/bin/env python3
"""Checks everything the programs claim.   python3 tests.py   (about ten seconds)

MIT licence. Frédéric Prost and Claude.
"""
import itertools
import os
import time

import recursive as r
from machines import Machine
from compiler import compile
import turing_to_recursive as ttr
import universal as uni
import lambda_calculus as lam
from recursion import smn, fixed_point, run

HERE = os.path.dirname(os.path.abspath(__file__))
failures = []


def check(name, condition):
    if not condition:
        failures.append(name)
        print("  FAILURE:", name)


def grid(k, n):
    return itertools.product(range(n), repeat=k)


def section(title):
    print(title)
    return time.time()


t = section("1. Library: each native version agrees with its term")
for name, f in r.LIB.items():
    if f.native is None:
        continue
    for a in grid(f.arity(), 5 if f.arity() < 3 else 4):
        check("%s%s" % (name, a), r.evaluate(f, a) == r.evaluate(f, a, fast=True))
print("   %d functions, %.1f s" % (sum(1 for f in r.LIB.values() if f.native), time.time() - t))

t = section("2. Compiler recursive functions -> Turing machines")
for name in ["add", "mult", "pred", "monus", "sg", "sgbar", "power", "fact", "eq", "less", "div", "tri", "pair"]:
    f = r.LIB[name]
    m = compile(f)
    for a in grid(f.arity(), 4 if f.arity() == 1 else 3):
        if name == "div" and a[1] == 0:
            continue
        check("compiled %s%s" % (name, a), m.compute(*a) == r.evaluate(f, a, fast=True))
    print("   %-7s %6d quadruples: as expected" % (name, len(m)))
m = compile(r.div)
try:
    m.run(3, 0, max_steps=200000)
    check("div(3, 0) must not halt", False)
except Exception:
    pass
print("   div(3, 0): the machine does not halt (as the function is undefined)   %.1f s" % (time.time() - t))

t = section("3. Turing machines -> recursive functions (normal form)")
for file, args in [("addition", [(0, 0), (2, 3), (1, 4)]), ("successor", [(0,), (3,)]),
                   ("predecessor", [(0,), (4,)]), ("proper_subtraction", [(2, 4), (5, 2)]),
                   ("projection_2_of_3", [(1, 2, 3)]), ("sign", [(0,), (3,)])]:
    M = Machine.from_file(os.path.join(HERE, "examples", file + ".tm"))
    for a in args:
        T, v, expected = ttr.check(M, list(a))
        check("f_Z %s%s" % (file, a), v == expected)
    print("   %-20s agrees step by step" % file)
print("   %.1f s" % (time.time() - t))

t = section("4. Universal function U(code(Z), x)")
for name, text in uni.EXAMPLES.items():
    M = Machine.from_text(text)
    e = uni.code_machine(M)
    for x in range(4):
        check("U %s %d" % (name, x), uni.U(e, x) == M.compute(x))
M = Machine.from_file(os.path.join(HERE, "examples", "zero_test.tm"))
e = uni.code_machine(M)
for x in range(3):
    check("U zero_test %d" % x, uni.U(e, x) == M.compute(x))
print("   %d machines, %.1f s" % (len(uni.EXAMPLES) + 1, time.time() - t))

t = section("5. Compiler recursive functions -> λ-calculus")
for name, args in [("add", (2, 3)), ("mult", (2, 3)), ("pred", (3,)), ("monus", (5, 2)), ("eq", (2, 2)),
                   ("eq", (1, 2)), ("div", (7, 2)), ("fact", (3,))]:
    v, n = lam.compute(r.LIB[name], *args)
    check("λ %s%s" % (name, args), v == r.evaluate(r.LIB[name], args, fast=True))
print("   as expected, %.1f s" % (time.time() - t))

t = section("6. s-m-n, quine, halting")
Z = compile(r.mult)
for a in range(3):
    Za = smn(Z, a)
    check("smn mult %d" % a, [Za.compute(y) for y in range(4)] == [a * y for y in range(4)])
q = fixed_point("print(SELF, end='')")
check("quine", run(q) == q)
import halting
for name, dec in halting.CANDIDATES.items():
    D = halting.paradox(dec)
    env = {}
    exec(D, env)
    ans = env["decide"](D, D)
    status, _ = halting.launch(D, D)
    check("halting " + name, ans != (status == "halts"))
print("   as expected, %.1f s" % (time.time() - t))

t = section("7. Two stacks, two counters, Post dominoes, logic")
import glob
import stacks
import counters
import post
import post_logic
for f in sorted(glob.glob(os.path.join(HERE, "examples", "*.tm"))):
    M = Machine.from_file(f)
    name = os.path.basename(f)[:-3]
    for a in [(0,), (2,), (1, 1), (2, 1)]:
        try:
            M.run(*a, max_steps=3000)
        except Exception:
            continue
        stacks.compare(M, *a)
        counters.compare(M, *a, two=(name != "multiplication"))
        d, names = post.modified_dominoes(M, *a)
        s = post.solution_from_computation(M, d, names, *a)
        check("modified post %s %s" % (name, a), post.is_solution(d, s, first=0))
        check("post %s %s" % (name, a), post.is_solution(post.to_ordinary(d), post.ordinary_solution(s, len(d))))
D3 = [(("a",), ("b", "a", "a")), (("a", "b"), ("a", "a")), (("b", "b", "a"), ("b", "b"))]
sol = post.search(D3)
check("Post search", post.is_solution(D3, sol))
f = post_logic.deduction(D3, sol)
check("Floyd deduction", f[-1][0] == f[-1][1])
check("model of words", post.is_solution(D3, post_logic.model_of_words(D3, 8)))
print("   11 machines, %.1f s" % (time.time() - t))

print()
print("Everything as expected." if not failures else "%d failures." % len(failures))
raise SystemExit(1 if failures else 0)
