"""Diophantine equations: three experiments (chapter "Diophantine equations").

1. The least solution of x^2 - d y^2 = 1 (continued fractions): its size jumps
   from one d to the next, which illustrates the absence of a computable bound on solutions.
2. Putnam's trick: the positive values of a(1 - P(a, y)^2) form the
   Diophantine set defined by P; trial with the numbers that are not squares.
3. Reduction to degree 4: the example 5x^3y^2 - 7z - 6w^2x + 9 = 0, turned into a
   system of equations of degree at most 2, checked on a grid of values.
"""
from itertools import product
from math import isqrt


def pell(d):
    """Least solution (x, y), y >= 1, of x^2 - d y^2 = 1, d not a square."""
    a0 = isqrt(d)
    m, q, a = 0, 1, a0
    p0, p1, q0, q1 = 1, a0, 0, 1
    while p1 * p1 - d * q1 * q1 != 1:
        m = q * a - m
        q = (d - m * m) // q
        a = (a0 + m) // q
        p0, p1 = p1, a * p1 + p0
        q0, q1 = q1, a * q1 + q0
    return p1, q1


def putnam_non_carres(borne):
    """Non-squares: a = z^2 + x + 1 and (z+1)^2 = a + y + 1. Positive values of a(1 - P^2)."""
    valeurs = set()
    for a, z, x, y in product(range(borne), repeat=4):
        P = (a - z * z - x - 1) ** 2 + ((z + 1) ** 2 - a - y - 1) ** 2
        Q = a * (1 - P * P)
        if Q > 0:
            valeurs.add(Q)
    return sorted(valeurs)


def systeme_degre_2(x, y, z, w):
    """Does the auxiliary system of the example have a solution extending (x, y, z, w)?
    The auxiliary variables are determined by the equations, so we compute them."""
    p1 = 5 * x; p2 = p1 * x; p3 = p2 * x; p4 = p3 * y; p5 = p4 * y   # 5x^3y^2
    q1 = 7 * z
    r1 = 6 * w; r2 = r1 * w; r3 = r2 * x                              # 6w^2x
    t1 = p5 + 9; t2 = q1 + r3
    return t1 == t2


if __name__ == "__main__":
    print("1. least solution of x^2 - d y^2 = 1")
    for d in (13, 60, 61, 62, 109):
        x, y = pell(d)
        assert x * x - d * y * y == 1
        print(f"   d = {d:3d}: x = {x}, y = {y}")
    print("2. positive values of the Putnam polynomial (unknowns < 12):", putnam_non_carres(12)[:15], "...")
    accord = all(systeme_degre_2(*v) == (5 * v[0]**3 * v[1]**2 - 7 * v[2] - 6 * v[3]**2 * v[0] + 9 == 0)
                 for v in product(range(8), repeat=4))
    print("3. degree-2 system and original equation: same set of solutions on [0,8)^4:", accord)
