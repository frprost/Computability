#!/usr/bin/env python3
"""Recursive functions: the terms of chapter 4 of the manual, their evaluation, a library.

A term is built with exactly the building blocks of the definition:
    C(k, m)            constant m of arity k        (x1..xk) -> m
    S                  successor                    x -> x+1
    A(k, i)            projection (argument choice) (x1..xk) -> xi
    sigma(g, h1..hk)   substitution                 x -> g(h1(x), ..., hk(x))
    rho(g, h)          primitive recursion          f(0,x)=g(x), f(y+1,x)=h(y, f(y,x), x)
    mu(g)              minimization                 x -> the least y such that g(x, y) = 0

The same syntax can be written as text and read with read_term:
    rho[A(1,1), sigma[S, A(3,2)]]        (addition)
One may also write ρ, σ, μ and use the names of the library (add, mult, ...).

Speed-up. The functions of the library are terms Named(name, term, native):
the term is the real definition, native is a Python function that computes the same thing
faster. evaluate(t, args) uses the term; evaluate(t, args, fast=True) uses native
for the named subterms. The file tests.py checks that the two agree.

    python3 recursive.py "rho[A(1,1), sigma[S, A(3,2)]]" 2 3     -> 5
    python3 recursive.py mult 4 5                                 -> 20
    python3 recursive.py --list                                   library

MIT licence. Frédéric Prost and Claude.
"""
import re
import sys


class Diverges(RuntimeError):
    """Raised when a minimization exceeds the set limit (the function may be undefined there)."""


class Term:
    def __call__(self, *args, fast=True):
        return evaluate(self, args, fast=fast)


class Const(Term):
    def __init__(self, k, m):
        self.k, self.m = k, m

    def arity(self):
        return self.k

    def __str__(self):
        return "C(%d,%d)" % (self.k, self.m)


class Succ(Term):
    def arity(self):
        return 1

    def __str__(self):
        return "S"


class Proj(Term):
    def __init__(self, k, i):
        if not 1 <= i <= k:
            raise ValueError("projection A(%d,%d) impossible" % (k, i))
        self.k, self.i = k, i

    def arity(self):
        return self.k

    def __str__(self):
        return "A(%d,%d)" % (self.k, self.i)


class Comp(Term):
    def __init__(self, g, *hs):
        if not hs:
            raise ValueError("sigma needs at least one inner function")
        m = hs[0].arity()
        if any(h.arity() != m for h in hs):
            raise ValueError("sigma: the inner functions do not all have the same arity")
        if g.arity() != len(hs):
            raise ValueError("sigma: %s has arity %d but receives %d arguments" % (g, g.arity(), len(hs)))
        self.g, self.hs = g, hs

    def arity(self):
        return self.hs[0].arity()

    def __str__(self):
        return "sigma[%s]" % ", ".join(str(t) for t in (self.g,) + self.hs)


class Rec(Term):
    def __init__(self, g, h):
        if h.arity() != g.arity() + 2:
            raise ValueError("rho: h must have the arity of g plus 2")
        self.g, self.h = g, h

    def arity(self):
        return self.g.arity() + 1

    def __str__(self):
        return "rho[%s, %s]" % (self.g, self.h)


class Mu(Term):
    def __init__(self, g):
        if g.arity() < 1:
            raise ValueError("mu: g must have at least one argument")
        self.g = g

    def arity(self):
        return self.g.arity() - 1

    def __str__(self):
        return "mu[%s]" % self.g


class Named(Term):
    """A term with a name and (optionally) a faster native version."""

    def __init__(self, name, term, native=None):
        self.name, self.term, self.native = name, term, native

    def arity(self):
        return self.term.arity()

    def __str__(self):
        return self.name


S = Succ()


def C(k, m):
    return Const(k, m)


def A(k, i):
    return Proj(k, i)


def sigma(g, *hs):
    return Comp(g, *hs)


def rho(g, h):
    return Rec(g, h)


def mu(g):
    return Mu(g)


# ------------------------------------------------------------------ evaluation
MU_LIMIT = [10**6]


def evaluate(t, args, fast=False):
    """Value of t at args. For a minimization, raises Diverges beyond MU_LIMIT[0] attempts."""
    args = tuple(args)
    if len(args) != t.arity():
        raise ValueError("%s has arity %d, receives %d arguments" % (t, t.arity(), len(args)))
    return _ev(t, args, fast)


def _ev(t, args, fast):
    while isinstance(t, Named):
        if fast and t.native is not None:
            return t.native(*args)
        t = t.term
    if isinstance(t, Const):
        return t.m
    if isinstance(t, Succ):
        return args[0] + 1
    if isinstance(t, Proj):
        return args[t.i - 1]
    if isinstance(t, Comp):
        return _ev(t.g, tuple(_ev(h, args, fast) for h in t.hs), fast)
    if isinstance(t, Rec):
        y, rest = args[0], args[1:]
        acc = _ev(t.g, rest, fast)
        for i in range(y):                     # the "for" loop: y rounds, known in advance
            acc = _ev(t.h, (i, acc) + rest, fast)
        return acc
    if isinstance(t, Mu):
        z = 0
        while True:                            # the "while" loop: number of rounds unknown
            if _ev(t.g, args + (z,), fast) == 0:
                return z
            z += 1
            if z > MU_LIMIT[0]:
                raise Diverges("minimization without an answer after %d attempts" % MU_LIMIT[0])
    raise TypeError("unknown term: %r" % (t,))


def unfold(t):
    """The term without any name: only C, S, A, sigma, rho, mu."""
    if isinstance(t, Named):
        return unfold(t.term)
    if isinstance(t, Comp):
        return Comp(unfold(t.g), *[unfold(h) for h in t.hs])
    if isinstance(t, Rec):
        return Rec(unfold(t.g), unfold(t.h))
    if isinstance(t, Mu):
        return Mu(unfold(t.g))
    return t


def size(t):
    """Number of building blocks of the fully unfolded term (shared subterms count at each use)."""
    memo = {}

    def go(u):
        if id(u) in memo:
            return memo[id(u)]
        if isinstance(u, Named):
            r = go(u.term)
        elif isinstance(u, Comp):
            r = 1 + go(u.g) + sum(go(h) for h in u.hs)
        elif isinstance(u, Rec):
            r = 1 + go(u.g) + go(u.h)
        elif isinstance(u, Mu):
            r = 1 + go(u.g)
        else:
            r = 1
        memo[id(u)] = r
        return r
    return go(t)


def is_primitive(t):
    """True if the term does not use mu (it then defines a total function)."""
    if isinstance(t, Named):
        return is_primitive(t.term)
    if isinstance(t, Mu):
        return False
    if isinstance(t, Comp):
        return is_primitive(t.g) and all(is_primitive(h) for h in t.hs)
    if isinstance(t, Rec):
        return is_primitive(t.g) and is_primitive(t.h)
    return True


# ------------------------------------------------------------------ library
LIB = {}


def define(name, term, native=None):
    t = Named(name, term, native)
    LIB[name] = t
    return t


def P(k, i):
    return A(k, i)


# Basic operations (chapter 4, "Addition, multiplication, ...")
add = define("add", rho(A(1, 1), sigma(S, A(3, 2))), lambda x, y: x + y)
mult = define("mult", rho(C(1, 0), sigma(add, A(3, 3), A(3, 2))), lambda x, y: x * y)
pred = define("pred", rho(C(0, 0), A(2, 1)), lambda x: max(x - 1, 0))
# minus_inv(y, x) = x ∸ y (recursion on the first argument), then the arguments are swapped
minus_inv = define("minus_inv", rho(A(1, 1), sigma(pred, A(3, 2))), lambda y, x: max(x - y, 0))
monus = define("monus", sigma(minus_inv, A(2, 2), A(2, 1)), lambda x, y: max(x - y, 0))
sg = define("sg", rho(C(0, 0), C(2, 1)), lambda x: 1 if x else 0)
sgbar = define("sgbar", rho(C(0, 1), C(2, 0)), lambda x: 0 if x else 1)
power_inv = define("power_inv", rho(C(1, 1), sigma(mult, A(3, 3), A(3, 2))), lambda y, x: x ** y)
power = define("power", sigma(power_inv, A(2, 2), A(2, 1)), lambda x, y: x ** y)
fact = define("fact", rho(C(0, 1), sigma(mult, sigma(S, A(2, 1)), A(2, 2))),
              lambda x: __import__("math").factorial(x))
# distance |x - y| and equality
dist = define("dist", sigma(add, monus, sigma(monus, A(2, 2), A(2, 1))), lambda x, y: abs(x - y))
eq = define("eq", sigma(sgbar, dist), lambda x, y: 1 if x == y else 0)
# strictly less: x < y  iff  y ∸ x > 0
less = define("less", sigma(sg, sigma(monus, A(2, 2), A(2, 1))), lambda x, y: 1 if x < y else 0)
# connectives on the truth values 0/1
conj = define("conj", mult, lambda a, b: a * b)
neg = define("neg", sgbar, lambda a: 0 if a else 1)
disj = define("disj", sigma(sg, add), lambda a, b: 1 if (a or b) else 0)
# cond(c, a, b) = a if c ≠ 0, b otherwise: a·sg(c) + b·sgbar(c)
cond = define("cond", sigma(add, sigma(mult, A(3, 2), sigma(sg, A(3, 1))), sigma(mult, A(3, 3), sigma(sgbar, A(3, 1)))),
              lambda c, a, b: a if c else b)
# quotient and remainder. quot_inv(y, x): recursion on y of the implicit pair:
#   q(0, x) = 0 ; q(y+1, x) = q(y, x) + [ (y+1) is a multiple of x ]   -> q(y, x) = y div x  (x > 0)
# remainder: r(0,x) = 0 ; r(y+1,x) = if (r(y,x)+1 = x) then 0 else r(y,x)+1
rem_inv = define("rem_inv",
                 rho(C(1, 0), sigma(cond, sigma(eq, sigma(S, A(3, 2)), A(3, 3)), C(3, 0), sigma(S, A(3, 2)))),
                 lambda y, x: y % x if x else y)
quot_inv = define("quot_inv",
                  rho(C(1, 0), sigma(add, A(3, 2), sigma(eq, sigma(S, sigma(rem_inv, A(3, 1), A(3, 3))), A(3, 3)))),
                  lambda y, x: y // x if x else 0)
rem = define("rem", sigma(rem_inv, A(2, 1), A(2, 2)), lambda x, y: x % y if y else x)
quot = define("quot", sigma(quot_inv, A(2, 1), A(2, 2)), lambda x, y: x // y if y else 0)
# quotient by minimization (unbounded: undefined for y = 0), as in the manual
div = define("div", mu(sigma(sgbar, sigma(monus, sigma(mult, sigma(S, A(3, 3)), A(3, 2)), A(3, 1)))),
             None)
# the nowhere-defined function
empty = define("empty", mu(C(2, 1)), None)

# Cantor pairs: <x, y> = (x+y)(x+y+1)/2 + x   (chapter 4, "Cantor coding of pairs")
# tri(n) = n(n+1)/2 ; tri(0) = 0, tri(n+1) = tri(n) + n + 1
tri = define("tri", rho(C(0, 0), sigma(add, A(2, 2), sigma(S, A(2, 1)))), lambda n: n * (n + 1) // 2)
pair = define("pair", sigma(add, sigma(tri, add), A(2, 1)), lambda x, y: (x + y) * (x + y + 1) // 2 + x)


def _tri_root(z):
    """The largest n such that tri(n) <= z."""
    from math import isqrt
    return (isqrt(8 * z + 1) - 1) // 2


# diag(z) = the largest n such that tri(n) <= z (that is x + y), obtained by recursion:
# diag(0) = 0 ; diag(z+1) = diag(z) + [tri(diag(z)+1) = z+1]
diag = define("diag", rho(C(0, 0), sigma(add, A(2, 2), sigma(eq, sigma(tri, sigma(S, A(2, 2))), sigma(S, A(2, 1))))),
              _tri_root)
# left(z) = pi_1(z) = z ∸ tri(diag(z)) ; right(z) = pi_2(z) = diag(z) ∸ left(z)
left = define("left", sigma(monus, A(1, 1), sigma(tri, diag)),
              lambda z: z - _tri_root(z) * (_tri_root(z) + 1) // 2)
right = define("right", sigma(monus, diag, left),
               lambda z: _tri_root(z) - (z - _tri_root(z) * (_tri_root(z) + 1) // 2))


def cantor(x, y):
    return (x + y) * (x + y + 1) // 2 + x


def uncantor(z):
    n = _tri_root(z)
    x = z - n * (n + 1) // 2
    return x, n - x


# ------------------------------------------------------------------ convenient writing: general substitution
# The proposition "general substitution" of chapter 4 says that one may write
#     f(x, y) = g(y, h(x, x), 3)
# without going explicitly through the projections: they are added mechanically.
# `function` performs exactly this translation:
#     f = function(2, lambda x, y: App(g, y, App(h, x, x), 3))
# gives the term sigma[g, A(2,2), sigma[h, A(2,1), A(2,1)], C(2,3)].

class Expr:
    def __call__(self, *a):
        raise TypeError("an expression cannot be applied")


class Var(Expr):
    def __init__(self, i):
        self.i = i


class App(Expr):
    def __init__(self, f, *args):
        if f.arity() != len(args):
            raise ValueError("%s expects %d arguments, receives %d" % (f, f.arity(), len(args)))
        self.f, self.args = f, args


def _translate(e, k):
    if isinstance(e, int):
        return C(k, e)
    if isinstance(e, Var):
        return A(k, e.i)
    if isinstance(e, App):
        if e.f.arity() == 0:
            raise ValueError("applying a function of arity 0: write its value")
        return Comp(e.f, *[_translate(a, k) for a in e.args])
    raise TypeError("unknown expression: %r" % (e,))


def function(k, body, name=None, native=None):
    """The term of arity k defined by body(x1, ..., xk) (an expression made of App, variables and integers)."""
    e = body(*[Var(i) for i in range(1, k + 1)])
    if isinstance(e, Var) and k >= 1:
        t = A(k, e.i)
    else:
        t = _translate(e, k)
    return define(name, t, native) if name else t


def recursion(k, base, step, name=None, native=None):
    """f(0, x2..xk) = base(x2..xk) ; f(y+1, x2..xk) = step(y, f(y, x), x2..xk).
    base and step are Python functions that return expressions."""
    g = function(k - 1, base) if k > 1 else C(0, base())
    h = function(k + 1, step)
    t = rho(g, h)
    return define(name, t, native) if name else t


def minimization(k, body, name=None, native=None):
    """f(x1..xk) = the least z such that body(x1..xk, z) = 0."""
    t = mu(function(k + 1, body))
    return define(name, t, native) if name else t


# ------------------------------------------------------------------ reading a term written as text
_TOKENS = re.compile(r"\s*(?:(\d+)|([A-Za-zÀ-ÿσρμ_][A-Za-z0-9À-ÿ_]*)|(.))")


def read_term(text, definitions=None):
    """Reads a term written as in the manual: rho[A(1,1), sigma[S, A(3,2)]].
    The names of the library and those of `definitions` are recognized."""
    env = dict(LIB)
    if definitions:
        env.update(definitions)
    tokens = [m.group(1) or m.group(2) or m.group(3) for m in _TOKENS.finditer(text) if (m.group(0).strip())]
    pos = [0]

    def peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def take(expected=None):
        j = peek()
        if expected is not None and j != expected:
            raise SyntaxError("expected \"%s\", found \"%s\"" % (expected, j))
        pos[0] += 1
        return j

    def integer():
        j = take()
        if not j or not j.isdigit():
            raise SyntaxError("integer expected, found \"%s\"" % j)
        return int(j)

    def term():
        j = take()
        if j in ("S",):
            return S
        if j in ("C", "A"):
            take("(")
            a = integer()
            take(",")
            b = integer()
            take(")")
            return C(a, b) if j == "C" else A(a, b)
        if j in ("sigma", "σ", "rho", "ρ", "mu", "μ"):
            take("[")
            ts = [term()]
            while peek() == ",":
                take(",")
                ts.append(term())
            take("]")
            if j in ("sigma", "σ"):
                return Comp(ts[0], *ts[1:])
            if j in ("rho", "ρ"):
                if len(ts) != 2:
                    raise SyntaxError("rho takes two terms")
                return Rec(*ts)
            if len(ts) != 1:
                raise SyntaxError("mu takes one term")
            return Mu(ts[0])
        if j in env:
            return env[j]
        raise SyntaxError("unknown symbol \"%s\"" % j)

    t = term()
    if peek() is not None:
        raise SyntaxError("extra text after the term: \"%s\"" % peek())
    return t


def read_program(text):
    """Reads lines "name = term"; the last line without "=" is the term to compute."""
    defs, last = {}, None
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if "=" in line:
            name, body = [s.strip() for s in line.split("=", 1)]
            defs[name] = Named(name, read_term(body, defs))
            last = defs[name]
        else:
            last = read_term(line, defs)
    return defs, last


def _main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    if argv[1] == "--list":
        for name, t in LIB.items():
            print("%-10s arity %d   %s" % (name, t.arity(), t.term))
        return 0
    t = read_term(argv[1])
    args = [int(a) for a in argv[2:]]
    print("term       :", unfold(t))
    print("arity      :", t.arity(), "   size:", size(t), "building blocks")
    print("value      :", evaluate(t, args))
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
