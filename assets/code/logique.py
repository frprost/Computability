"""Logic and computation: experiments (chapter "Logic and types").

1. Monadic logic: deciding the satisfiability of a sentence that uses only
   unary predicates P1..Pk, by trying all structures with at most 2^k elements.
2. Simply typed λ-calculus and System T: the Ackermann function written with
   Gödel's recursor, at higher order, and compared with Péter's definition.
3. System F: the same function with polymorphic Church numerals only, without
   a recursor, by iterating at type Nat -> Nat.

Formulas: ('P', i, 'x') atom; ('non', A) not; ('et', A, B) and; ('ou', A, B) or;
('imp', A, B) implies; ('ex', 'x', A) exists; ('tout', 'x', A) for all.
"""
from itertools import product


def vrai(f, dom, interp, env):
    op = f[0]
    if op == 'P':
        return env[f[2]] in interp[f[1]]
    if op == 'non':
        return not vrai(f[1], dom, interp, env)
    if op == 'et':
        return vrai(f[1], dom, interp, env) and vrai(f[2], dom, interp, env)
    if op == 'ou':
        return vrai(f[1], dom, interp, env) or vrai(f[2], dom, interp, env)
    if op == 'imp':
        return (not vrai(f[1], dom, interp, env)) or vrai(f[2], dom, interp, env)
    if op == 'ex':
        return any(vrai(f[2], dom, interp, {**env, f[1]: d}) for d in dom)
    if op == 'tout':
        return all(vrai(f[2], dom, interp, {**env, f[1]: d}) for d in dom)
    raise ValueError(op)


def predicats(f):
    if f[0] == 'P':
        return {f[1]}
    return set().union(*(predicats(g) for g in f[1:] if isinstance(g, tuple)))


def satisfaisable(f):
    """Looks for a model of size 1..2^k (k predicates): sufficient by the theorem."""
    ps = sorted(predicats(f))
    k = len(ps)
    for m in range(1, 2 ** k + 1):
        dom = range(m)
        for choix in product(product([False, True], repeat=m), repeat=k):
            interp = {p: {d for d in dom if choix[i][d]} for i, p in enumerate(ps)}
            if vrai(f, dom, interp, {}):
                return m, interp
    return None


def valide(f):
    return satisfaisable(('non', f)) is None


# System T, simulated in Python: R a g n with R a g 0 = a, R a g (n+1) = g n (R a g n)
def R(a, g, n):
    acc = a
    for k in range(n):
        acc = g(k, acc)
    return acc


def iter_(n, f, a):              # f^n(a) = R a (λk.f) n
    return R(a, lambda k, acc: f(acc), n)


succ = lambda n: n + 1
# ack m = R succ (λk.λf.λn. iter (n+1) f 1) m   (recursion at type Nat -> Nat)
ack = lambda m: R(succ, lambda k, f: (lambda n: iter_(n + 1, f, 1)), m)


def peter(m, n):
    if m == 0:
        return n + 1
    if n == 0:
        return peter(m - 1, 1)
    return peter(m - 1, peter(m, n - 1))


# System F, simulated in Python: polymorphic Church numerals Nat = ∀α.(α→α)→α→α.
# Types are erased; only the iteration built into the numerals is used.
def church(n):
    return lambda f: lambda x: x if n == 0 else f(church(n - 1)(f)(x))


def entier(c):
    return c(lambda k: k + 1)(0)


S_F = lambda n: lambda f: lambda x: f(n(f)(x))          # S : Nat → Nat
UN = church(1)
# H : (Nat→Nat) → Nat → Nat,  H f n = (S n) [Nat] f 1   (f iterated n+1 times on 1)
H = lambda f: lambda n: S_F(n)(f)(UN)
# ack : Nat → Nat → Nat,  ack m = m [Nat→Nat] H S   (iteration at type Nat→Nat)
ack_F = lambda m: m(H)(S_F)


if __name__ == "__main__":
    P, Q, Rr = 1, 2, 3
    syllogisme = ('imp', ('et', ('tout', 'x', ('imp', ('P', P, 'x'), ('P', Q, 'x'))),
                                ('tout', 'x', ('imp', ('P', Q, 'x'), ('P', Rr, 'x')))),
                  ('tout', 'x', ('imp', ('P', P, 'x'), ('P', Rr, 'x'))))
    deux = ('et', ('ex', 'x', ('P', P, 'x')), ('ex', 'x', ('non', ('P', P, 'x'))))
    faux_ami = ('imp', ('et', ('ex', 'x', ('P', P, 'x')), ('ex', 'x', ('P', Q, 'x'))),
                ('ex', 'x', ('et', ('P', P, 'x'), ('P', Q, 'x'))))
    print("1. monadic logic")
    print("   syllogism (Barbara) valid:", valide(syllogisme))
    print("   \"a P and a non-P\": model", satisfaisable(deux), "; valid:", valide(deux))
    print("   \"a P and a Q, hence a P and Q\" valid:", valide(faux_ami),
          "; countermodel:", satisfaisable(('non', faux_ami)))
    print("2. Ackermann in System T")
    ok = all(ack(m)(n) == peter(m, n) for m in range(4) for n in range(5))
    print("   agrees with Péter's definition for m < 4, n < 5:", ok, "; ack(3)(3) =", ack(3)(3))
    print("3. Ackermann in System F (Church numerals, no recursor)")
    okF = all(entier(ack_F(church(m))(church(n))) == peter(m, n) for m in range(4) for n in range(4))
    print("   agrees with Péter for m < 4, n < 4:", okF, "; ack 3 3 =", entier(ack_F(church(3))(church(3))))
