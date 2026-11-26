#!/usr/bin/env python3
"""λ-calculus: normal-order reduction, Church numerals, and a compiler
recursive functions -> λ-terms (chapters "λ-calculus" and "Equivalence" of the manual).

Syntax (the same as the reducer built into the pages):
    λx.M  or  \\x.M        abstraction; λx y.M abbreviates λx.λy.M
    M N                    application (to the left: M N P = (M N) P)
    0, 1, 2, ...           Church numerals: n = λf x.f (f (... (f x)))
    NAME = term            definition (one per line), usable afterwards

The compiler follows the proof of the theorem "recursive functions are λ-definable":
    C(k,m)       -> λx1..xk. m
    S            -> λn f x. f (n f x)
    A(k,i)       -> λx1..xk. xi
    sigma[g,h..] -> λx. G (H1 x) ... (Hk x)
    rho[g,h]     -> λy x. snd (y (λp. pair (S (fst p)) (H (fst p) (snd p) x)) (pair 0 (G x)))
    mu[g]        -> λx. Θ (λr m. zero? (G x m) m (r (S m))) 0        (Θ: Turing's combinator)

Usage:
    python3 lambda_calculus.py "(λm n f.m (n f)) 2 3"          reduces the term: 6
    python3 lambda_calculus.py --file program.lam
    python3 lambda_calculus.py --compile mult 2 3              recursive function -> λ-term, reduced

MIT licence. Frédéric Prost and Claude.
"""
import re
import sys

sys.setrecursionlimit(100000)

# ------------------------------------------------------------------ named terms
# ('v', name) | ('l', name, body) | ('a', function, argument)


def V(n):
    return ("v", n)


def L(names, body):
    for n in reversed(names.split()):
        body = ("l", n, body)
    return body


def Ap(*ts):
    t = ts[0]
    for u in ts[1:]:
        t = ("a", t, u)
    return t


def church(n):
    body = V("x")
    for _ in range(n):
        body = Ap(V("f"), body)
    return L("f x", body)


# ------------------------------------------------------------------ reading
def _tokens(s):
    for m in re.finditer(r"\s*(λ|\\|\(|\)|\.|[A-Za-z0-9_'?+*\-]+)", s):
        yield m.group(1)


def read(s, defs=None):
    defs = defs or {}
    toks = list(_tokens(s))
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def term():
        if peek() in ("λ", "\\"):
            pos[0] += 1
            names = []
            while peek() not in (".", None):
                names.append(toks[pos[0]])
                pos[0] += 1
            if peek() != "." or not names:
                raise SyntaxError("malformed abstraction")
            pos[0] += 1
            return L(" ".join(names), term())
        t = atom()
        while peek() not in (None, ")"):
            if peek() in ("λ", "\\"):
                return Ap(t, term())
            t = Ap(t, atom())
        return t

    def atom():
        j = peek()
        pos[0] += 1
        if j == "(":
            t = term()
            if peek() != ")":
                raise SyntaxError("unclosed parenthesis")
            pos[0] += 1
            return t
        if j is None or j in (")", "."):
            raise SyntaxError("term expected")
        if j.isdigit():
            return church(int(j))
        if j in defs:
            return defs[j]
        return V(j)

    t = term()
    if peek() is not None:
        raise SyntaxError("extra text: %s" % peek())
    return t


def read_program(text):
    defs, t = {}, None
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r"^([A-Za-z0-9_'?+*\-]+)\s*=\s*(.*)$", line)
        if m:
            defs[m.group(1)] = read(m.group(2), defs)
        else:
            t = read(line, defs)
    return t


# ------------------------------------------------------------------ de Bruijn indices
# ('V', k) | ('L', body) | ('A', f, x)

def to_db(t, env=()):
    if t[0] == "v":
        if t[1] in env:
            return ("V", env.index(t[1]))
        raise ValueError("free variable: %s" % t[1])
    if t[0] == "l":
        return ("L", to_db(t[2], (t[1],) + env))
    return ("A", to_db(t[1], env), to_db(t[2], env))


def shift(t, d, c=0):
    if t[0] == "V":
        return ("V", t[1] + d) if t[1] >= c else t
    if t[0] == "L":
        return ("L", shift(t[1], d, c + 1))
    return ("A", shift(t[1], d, c), shift(t[2], d, c))


def substitute(t, j, s):
    if t[0] == "V":
        if t[1] == j:
            return shift(s, j)
        return ("V", t[1] - 1) if t[1] > j else t
    if t[0] == "L":
        return ("L", substitute(t[1], j + 1, s))
    return ("A", substitute(t[1], j, s), substitute(t[2], j, s))


def normal_step(t):
    """One leftmost-outermost reduction step; None if t is normal."""
    if t[0] == "A":
        if t[1][0] == "L":
            return substitute(t[1][1], 0, t[2])
        f = normal_step(t[1])
        if f is not None:
            return ("A", f, t[2])
        x = normal_step(t[2])
        return None if x is None else ("A", t[1], x)
    if t[0] == "L":
        b = normal_step(t[1])
        return None if b is None else ("L", b)
    return None


def normalize(t, max_steps=10**6):
    """Normal form by the normal strategy (which always finds it if it exists).
    Returns (normal form, number of steps); raises RuntimeError beyond max_steps."""
    if t[0] in ("v", "l", "a"):
        t = to_db(t)
    n = 0
    while True:
        u = normal_step(t)
        if u is None:
            return t, n
        t, n = u, n + 1
        if n >= max_steps:
            raise RuntimeError("no normal form after %d steps" % max_steps)


def integer(t):
    """The integer n if t is (in de Bruijn form) the Church numeral λf.λx.f^n x, otherwise None."""
    if t[0] != "L" or t[1][0] != "L":
        return None
    c, n = t[1][1], 0
    while c[0] == "A" and c[1] == ("V", 1):
        c, n = c[2], n + 1
    return n if c == ("V", 0) else None


def show(t, names=None, depth=0):
    """Readable writing of a term in de Bruijn form."""
    if t[0] == "V":
        return names[-1 - t[1]] if names and t[1] < len(names) else "#%d" % t[1]
    names = names or []
    if t[0] == "L":
        x = "x%d" % (len(names))
        return "λ%s.%s" % (x, show(t[1], names + [x]))
    f = show(t[1], names)
    a = show(t[2], names)
    if t[1][0] == "L":
        f = "(%s)" % f
    if t[2][0] != "V":
        a = "(%s)" % a
    return "%s %s" % (f, a)


# ------------------------------------------------------------------ library and compiler
PRELUDE = """tt = λx y.x
ff = λx y.y
S = λn f x.f (n f x)
zero? = λn.n (λz.ff) tt
pair = λa b s.s a b
fst = λp.p tt
snd = λp.p ff
Θ = (λx y.y (x x y)) (λx y.y (x x y))
"""
_P = {}
for _l in PRELUDE.splitlines():
    _n, _c = _l.split(" = ")
    _P[_n] = read(_c, _P)

_counter = [0]


def _vars(k, prefix="x"):
    _counter[0] += 1
    return ["%s%d_%d" % (prefix, i, _counter[0]) for i in range(1, k + 1)]


def compile(f):
    """(Named) λ-term that λ-defines the recursive function f."""
    from recursive import Const, Succ, Proj, Comp, Rec, Mu, Named
    while isinstance(f, Named):
        f = f.term
    if isinstance(f, Const):
        xs = _vars(f.k)
        return L(" ".join(xs), church(f.m)) if xs else church(f.m)
    if isinstance(f, Succ):
        return _P["S"]
    if isinstance(f, Proj):
        xs = _vars(f.k)
        return L(" ".join(xs), V(xs[f.i - 1]))
    if isinstance(f, Comp):
        xs = _vars(f.arity())
        G = compile(f.g)
        args = [Ap(compile(h), *[V(x) for x in xs]) for h in f.hs]
        return L(" ".join(xs), Ap(G, *args))
    if isinstance(f, Rec):
        G, H = compile(f.g), compile(f.h)
        y = _vars(1, "y")[0]
        xs = _vars(f.arity() - 1)
        p = _vars(1, "p")[0]
        fst, snd, pair, S = _P["fst"], _P["snd"], _P["pair"], _P["S"]
        X = [V(x) for x in xs]
        step = L(p, Ap(pair, Ap(S, Ap(fst, V(p))), Ap(H, Ap(fst, V(p)), Ap(snd, V(p)), *X)))
        start = Ap(pair, church(0), Ap(G, *X) if X else G)
        return L(" ".join([y] + xs), Ap(snd, Ap(V(y), step, start)))
    if isinstance(f, Mu):
        G = compile(f.g)
        xs = _vars(f.arity())
        rr, m = _vars(1, "r")[0], _vars(1, "m")[0]
        X = [V(x) for x in xs]
        W = L("%s %s" % (rr, m), Ap(_P["zero?"], Ap(G, *(X + [V(m)])), V(m), Ap(V(rr), Ap(_P["S"], V(m)))))
        body = Ap(_P["Θ"], W, church(0))
        return L(" ".join(xs), body) if xs else body
    raise TypeError("unknown term")


def compute(f, *args, max_steps=10**6):
    """Reduces (compile(f)) n1 ... nk and reads the integer obtained."""
    t = Ap(compile(f), *[church(a) for a in args])
    nf, n = normalize(t, max_steps)
    return integer(nf), n


def _main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    if argv[1] == "--compile":
        from recursive import read_term
        f = read_term(argv[2])
        args = [int(a) for a in argv[3:]]
        v, n = compute(f, *args)
        print("value: %s   (%d β-reduction steps)" % (v, n))
        return 0
    if argv[1] == "--file":
        with open(argv[2], encoding="utf-8") as fh:
            t = read_program(PRELUDE + fh.read())
    else:
        t = read_program(PRELUDE + argv[1])
    nf, n = normalize(t)
    e = integer(nf)
    print("normal form: %s" % show(nf))
    print("(%d steps)%s" % (n, "   Church numeral: %d" % e if e is not None else ""))
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
