"""Deciding Presburger arithmetic with automata (chapter "Decidable theories").

A tuple of integers is written in binary, least significant bit first: the k-th letter
of the word is the tuple of the k-th bits. Each formula becomes a deterministic finite automaton
that recognizes exactly the encodings of the tuples satisfying it (trailing zeros included).

Formulas: ('eq', {x: a, y: b, ...}, c) for a*x + b*y + ... = c (integer coefficients);
('le', {...}, c) for a*x + ... <= c; ('non', A) not; ('et', A, B) and; ('ou', A, B) or;
('imp', A, B) implies; ('ex', x, A) exists; ('tout', x, A) for all.
"""
from itertools import product


class AFD:
    """Complete deterministic automaton over the alphabet {0,1}^len(vars)."""
    def __init__(self, vars_, init, delta, acc):
        self.vars, self.init, self.delta, self.acc = tuple(vars_), init, delta, acc

    def lettres(self):
        return list(product((0, 1), repeat=len(self.vars)))


def explorer(vars_, init, pas, accepte):
    """Builds the reachable automaton from a transition function."""
    lettres = list(product((0, 1), repeat=len(vars_)))
    delta, acc, a_voir = {}, set(), [init]
    vus = {init}
    while a_voir:
        q = a_voir.pop()
        if accepte(q):
            acc.add(q)
        for l in lettres:
            r = pas(q, l)
            delta[q, l] = r
            if r not in vus:
                vus.add(r)
                a_voir.append(r)
    return AFD(vars_, init, delta, acc)


def atome(coefs, c, egal):
    vars_ = sorted(coefs)
    a = [coefs[v] for v in vars_]

    def pas(q, l):
        if q is None:
            return None
        s = q - sum(ai * bi for ai, bi in zip(a, l))
        if egal:
            return s // 2 if s % 2 == 0 else None     # None: sink state
        return s // 2                                  # floor

    def accepte(q):
        return q is not None and (q == 0 if egal else q >= 0)
    return explorer(vars_, c, pas, accepte)


def etendre(A, vars_):
    """Same automaton, read on more tracks (the extra tracks are ignored)."""
    pos = [vars_.index(v) for v in A.vars]
    return explorer(vars_, A.init,
                    lambda q, l: A.delta[q, tuple(l[i] for i in pos)],
                    lambda q: q in A.acc)


def produit(A, B, op):
    vars_ = sorted(set(A.vars) | set(B.vars))
    A, B = etendre(A, vars_), etendre(B, vars_)
    return explorer(vars_, (A.init, B.init),
                    lambda q, l: (A.delta[q[0], l], B.delta[q[1], l]),
                    lambda q: op(q[0] in A.acc, q[1] in B.acc))


def complement(A):
    return AFD(A.vars, A.init, A.delta, set(q for q, _ in A.delta) - A.acc | ({A.init} - A.acc))


def projeter(A, x):
    """Automaton for ∃x A: erase track x (subset construction), then also accept
    the sets from which zero letters lead to acceptance (the witness x may
    have more bits than the other variables)."""
    if x not in A.vars:
        return A
    i = A.vars.index(x)
    vars_ = A.vars[:i] + A.vars[i + 1:]

    def pas(S, l):
        return frozenset(A.delta[q, l[:i] + (b,) + l[i:]] for q in S for b in (0, 1))
    B = explorer(vars_, frozenset([A.init]), pas, lambda S: bool(S & A.acc))
    zero = tuple(0 for _ in vars_)
    acc, change = set(B.acc), True
    while change:
        change = False
        for (S, l), T in B.delta.items():
            if l == zero and T in acc and S not in acc:
                acc.add(S)
                change = True
    B.acc = acc
    return B


def automate(f):
    op = f[0]
    if op in ('eq', 'le'):
        return atome({v: a for v, a in f[1].items() if a}, f[2], op == 'eq')
    if op == 'non':
        return complement(automate(f[1]))
    if op == 'et':
        return produit(automate(f[1]), automate(f[2]), lambda a, b: a and b)
    if op == 'ou':
        return produit(automate(f[1]), automate(f[2]), lambda a, b: a or b)
    if op == 'imp':
        return produit(automate(f[1]), automate(f[2]), lambda a, b: (not a) or b)
    if op == 'ex':
        return projeter(automate(f[2]), f[1])
    if op == 'tout':
        return complement(projeter(complement(automate(f[2])), f[1]))
    raise ValueError(op)


def vrai(enonce):
    A = automate(enonce)
    assert A.vars == (), "the sentence has free variables"
    return A.init in A.acc


def accepte(A, valeurs):
    """Does the automaton accept the binary encoding of the tuple (in the order of A.vars)?"""
    q, n = A.init, max([v.bit_length() for v in valeurs] + [0])
    for k in range(n):
        q = A.delta[q, tuple((v >> k) & 1 for v in valeurs)]
    return q in A.acc


if __name__ == "__main__":
    import random
    # 1. check the automata for atoms and connectives against direct computation
    random.seed(1)
    for _ in range(300):
        a, b, c, d = (random.randint(-3, 3) for _ in range(4))
        f = ('ou', ('eq', {'x': a, 'y': b}, c), ('non', ('le', {'x': b, 'y': d}, a)))
        A = automate(f)
        for x in range(12):
            for y in range(12):
                env = {'x': x, 'y': y}
                attendu = (a * x + b * y == c) or not (b * x + d * y <= a)
                assert accepte(A, [env[v] for v in A.vars]) == attendu
    print("1. automata for quantifier-free formulas: agree with direct computation")
    # 2. a few sentences
    pair_ou_impair = ('tout', 'x', ('ex', 'y', ('ou', ('eq', {'x': 1, 'y': -2}, 0),
                                                 ('eq', {'x': 1, 'y': -2}, 1))))
    print("2. every integer is even or odd:", vrai(pair_ou_impair))

    def monnaie(s):           # every n >= s can be written 3a + 5b
        return ('tout', 'n', ('imp', ('le', {'n': -1}, -s),
                              ('ex', 'a', ('ex', 'b', ('eq', {'n': 1, 'a': -3, 'b': -5}, 0)))))
    print("   every n >= 8 can be written 3a+5b:", vrai(monnaie(8)), "; every n >= 7:", vrai(monnaie(7)))
    print("   there is x with 2x = 5:", vrai(('ex', 'x', ('eq', {'x': 2}, 5))))
    print("   no largest integer:", vrai(('tout', 'x', ('ex', 'y', ('le', {'x': 1, 'y': -1}, -1)))))
    # 3. a sanity check: 3 | x and 5 | x  <=>  15 | x
    div = lambda m, v, w: ('ex', w, ('eq', {v: 1, w: -m}, 0))
    print("3. (3 | x and 5 | x) <=> 15 | x:", vrai(('tout', 'x', ('et',
          ('imp', ('et', div(3, 'x', 'u'), div(5, 'x', 'v')), div(15, 'x', 'w')),
          ('imp', div(15, 'x', 'w'), ('et', div(3, 'x', 'u'), div(5, 'x', 'v')))))))
    A = automate(('ex', 'y', ('eq', {'x': 1, 'y': -3}, 0)))
    print("   automaton for the multiples of 3:", len({q for q, _ in A.delta}), "states")
