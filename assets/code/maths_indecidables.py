"""Three reductions from the chapter "The undecidable in ordinary mathematics".

1. A FRACTRAN program becomes a generalized Collatz function (Conway, 1972).
2. An instance of Post's problem becomes a set of 3x3 integer matrices.
3. A Turing machine becomes a set of Wang tiles with an origin tile.
"""
from fractions import Fraction
from math import lcm
from itertools import product as prod


# 1. FRACTRAN -> generalized Collatz -------------------------------------------
def collatz_de_fractran(fracs):
    """Returns (M, coef): g(n) = coef(n % M) * n, where coef(r) = 1 if no fraction
    applies (fixed point). The choice of the fraction depends only on n mod M. The table
    of the M values of coef is finite; it is computed on demand, since M can be large."""
    M = lcm(*(f.denominator for f in fracs))

    def coef(r):
        for f in fracs:
            if r % f.denominator == 0:     # f.den divides n  <=>  f.den divides n mod M (since f.den | M)
                return f
        return Fraction(1)
    return M, coef


def fractran(fracs, n, pas_max=10**6):
    for _ in range(pas_max):
        for f in fracs:
            if (n * f).denominator == 1:
                n = int(n * f)
                break
        else:
            return n
    return None


def iterer_collatz(M, table, n, pas_max=10**6):
    for _ in range(pas_max):
        m = int(table(n % M) * n)
        if m == n:
            return n
        n = m
    return None


# 2. Post's problem -> matrices   -------------------------------------------------
def sigma(w):                       # word over {a,b} -> integer in base 3, digits 1 and 2
    v = 0
    for c in w:
        v = 3 * v + (1 if c == 'a' else 2)
    return v


def matrice(u, v):
    return [[3 ** len(u), 0, sigma(u)], [0, 3 ** len(v), sigma(v)], [0, 0, 1]]


def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


# 3. Turing machine -> Wang tiles        ------------------------------------------
def tuiles(delta, q0, blanc='0'):
    """delta[(q, s)] = (q2, s2, 'G' (left) or 'D' (right)). Tile = (bottom, top, left, right).
    One row = one instant; the vertical colour is the content of the cell
    (a symbol, or a pair (state, symbol) under the head). The symbols of cell 0 are
    marked (suffix ^) and its tiles have left colour '|': no head can
    appear from the left edge."""
    symboles = {s for (_, s) in delta} | {s2 for (_, s2, _) in delta.values()} | {blanc}
    etats = {q for (q, _) in delta} | {q2 for (q2, _, _) in delta.values()}
    T = set()
    for s in symboles:
        m = s + '^'
        T.add((s, s, '-', '-'))                          # cell away from the head
        T.add((m, m, '|', '-'))
        for q in etats:
            T.add((s, (q, s), q + '>', '-'))             # the head arrives from the left
            T.add((s, (q, s), '-', '<' + q))             # the head arrives from the right
            T.add((m, (q, m), '|', '<' + q))
    for (q, s), (q2, s2, d) in delta.items():
        if d == 'D':
            T.add(((q, s), s2, '-', q2 + '>'))
            T.add(((q, s + '^'), s2 + '^', '|', q2 + '>'))
        else:
            T.add(((q, s), s2, '<' + q2, '-'))           # in cell 0: no tile (exit on the left)
    origine = ('*', (q0, blanc + '^'), '|', 'i')          # row 0: the initial configuration
    T.add(origine)
    T.add(('*', blanc, 'i', 'i'))
    return T, origine


def pave_carre(T, origine, n):
    """Searches (by backtracking, without knowing the machine) for a tiling of the n x n square
    with the origin tile at the bottom left. The edges are free: no constraint outside the square."""
    grille = {}
    cases = [(x, y) for y in range(n) for x in range(n)]

    def ok(t, x, y):
        if (x, y) == (0, 0):
            return t == origine
        if y == 0 and t[0] != '*':
            return False
        if y > 0 and grille[x, y - 1][1] != t[0]:
            return False
        if x > 0 and grille[x - 1, y][3] != t[2]:
            return False
        return True

    def essayer(i):
        if i == len(cases):
            return True
        x, y = cases[i]
        for t in T:
            if ok(t, x, y):
                grille[x, y] = t
                if essayer(i + 1):
                    return True
        return False
    return essayer(0)


if __name__ == "__main__":
    # 1. addition in FRACTRAN: 2^a 3^b -> 3^(a+b)
    add = [Fraction(3, 2)]
    M, table = collatz_de_fractran(add)
    print("1. FRACTRAN [3/2]: g(n) =", ", ".join(f"{table(r)}·n if n ≡ {r} mod {M}" for r in range(M)))
    ok = all(fractran(add, 2**a * 3**b) == iterer_collatz(M, table, 2**a * 3**b) == 3**(a + b)
             for a in range(6) for b in range(6))
    prime = [Fraction(*p) for p in [(17, 91), (78, 85), (19, 51), (23, 38), (29, 33), (77, 29), (95, 23),
             (77, 19), (1, 17), (11, 13), (13, 11), (15, 14), (15, 2), (55, 1)]]
    M2, t2 = collatz_de_fractran(prime)
    n, a, b, puiss = 2, 2, 2, []
    for _ in range(20000):            # PRIMEGAME, via the associated Collatz function
        n = int(t2(n % M2) * n)
        if n & (n - 1) == 0:
            puiss.append(n.bit_length() - 1)
    print("   addition: FRACTRAN and Collatz agree for a, b < 6:", ok)
    print("   PRIMEGAME seen as a Collatz function (modulo", M2, "): powers of 2 reached:", puiss[:6])
    # 2. Post instance (a/baa, ab/aa, bba/bb), solution 3,2,3,1
    dom = [('a', 'baa'), ('ab', 'aa'), ('bba', 'bb')]
    sol = [3, 2, 3, 1]
    P = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    for i in reversed(sol):            # the product M_{i_m} ... M_{i_1} reads the words in order
        P = mul(P, matrice(*dom[i - 1]))
    print("2. Post: u =", ''.join(dom[i - 1][0] for i in sol), " v =", ''.join(dom[i - 1][1] for i in sol),
          "; entries (1,3) and (2,3) of the product:", P[0][2], P[1][2])
    # 3. tiles: a machine that halts after 3 steps, one that goes right forever
    arret = {('A', '0'): ('B', '1', 'D'), ('B', '0'): ('C', '1', 'D'), ('C', '0'): ('H', '1', 'D')}
    boucle = {('A', '0'): ('A', '1', 'D')}
    for nom, d in [("halts in 3 steps", arret), ("does not halt", boucle)]:
        T, o = tuiles(d, 'A')
        print(f"3. machine that {nom}:", len(T), "tiles; tileable squares:",
              [k for k in range(1, 8) if pave_carre(T, o, k)])
