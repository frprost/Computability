"""Experiments of the chapter "Randomness, approximation and quantum computing".

1. Miller-Rabin test: number of "strong liars" for each odd composite < 5000.
2. Schwartz-Zippel lemma: testing a polynomial identity at a random point.
3. MAX-3SAT: a random assignment satisfies 7/8 of the clauses on average.
4. Deutsch's algorithm, Grover and Shor, simulated exactly on a state vector.
No external library: Python's complex numbers suffice.
"""
import cmath
import math
import random
from fractions import Fraction


# 1. Miller-Rabin ---------------------------------------------------------------
def temoin(a, n):
    """True if a proves that n (odd > 2) is composite."""
    d, s = n - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    x = pow(a, d, n)
    if x in (1, n - 1):
        return False
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return False
    return True


def miller_rabin(n, k=20):
    if n < 4:
        return n in (2, 3)
    if n % 2 == 0:
        return False
    return not any(temoin(random.randrange(2, n - 1), n) for _ in range(k))


def premier(n):
    return n > 1 and all(n % p for p in range(2, math.isqrt(n) + 1))


# 2. Schwartz-Zippel --------------------------------------------------------------
def identite_probable(P, Q, nvars, degre, essais=20, S=10**6):
    """Tests P = Q (polynomials given as functions) at random points of {0..S-1}^n.
    If P != Q, each trial is wrong with probability at most degre/S."""
    for _ in range(essais):
        x = [random.randrange(S) for _ in range(nvars)]
        if P(*x) != Q(*x):
            return False
    return True


# 3. MAX-3SAT -----------------------------------------------------------------------
def formule_aleatoire(n, m):
    return [[random.choice([1, -1]) * v for v in random.sample(range(1, n + 1), 3)] for _ in range(m)]


def fraction_satisfaite(F, val):
    return sum(any((l > 0) == val[abs(l)] for l in c) for c in F) / len(F)


# 4. Quantum simulation: a state is the list of the 2^n amplitudes ------------------
def hadamard(etat, q):
    r = 1 / math.sqrt(2)
    nouv = etat[:]
    for i in range(len(etat)):
        if not (i >> q) & 1:
            a, b = etat[i], etat[i | 1 << q]
            nouv[i], nouv[i | 1 << q] = r * (a + b), r * (a - b)
    return nouv


def deutsch(f):
    """A single call to the oracle U_f |x, y> = |x, y xor f(x)>: decides whether f(0) = f(1).
    Qubit 0: x; qubit 1: y."""
    etat = [0j] * 4
    etat[0b10] = 1                                  # x = 0, y = 1
    etat = hadamard(hadamard(etat, 0), 1)
    nouv = [0j] * 4
    for i, a in enumerate(etat):                    # the single call to the oracle
        x, y = i & 1, i >> 1
        nouv[x | (y ^ f(x)) << 1] += a
    etat = hadamard(nouv, 0)
    p1 = sum(abs(a) ** 2 for i, a in enumerate(etat) if i & 1)
    return "constant" if p1 < 1e-9 else "balanced"


def grover(n, cible):
    N = 2 ** n
    etat = [1 / math.sqrt(N)] * N
    k = int(math.pi / 4 * math.sqrt(N))
    for _ in range(k):
        etat[cible] = -etat[cible]                  # oracle: flips the sign of the target
        m = sum(etat) / N
        etat = [2 * m - a for a in etat]            # inversion about the mean
    return k, abs(etat[cible]) ** 2


def shor_simule(N, a, t=8):
    """Period finding for x -> a^x mod N with a register of t qubits (Q = 2^t).
    We compute exactly the distribution of the measurement after the Fourier transform."""
    Q = 2 ** t
    valeurs = {}
    for x in range(Q):
        valeurs.setdefault(pow(a, x, N), []).append(x)
    loi = [0.0] * Q
    for xs in valeurs.values():                     # each possible outcome of measuring f(x)
        # state after measurement: sum of the |x>, x in xs, normalized; after Fourier, the amplitude of |y>
        # is sum exp(2iπxy/Q) / sqrt(Q·|xs|); weighted by the probability |xs|/Q of this outcome
        for y in range(Q):
            s = sum(cmath.exp(2j * math.pi * x * y / Q) for x in xs)
            loi[y] += abs(s) ** 2 / Q ** 2
    return loi


def periode_depuis_mesure(y, Q, N):
    """Continued fractions: the denominator of the best approximation of y/Q."""
    return Fraction(y, Q).limit_denominator(N).denominator


def facteurs_depuis_periode(N, a, r):
    if r % 2 or pow(a, r // 2, N) == N - 1:
        return None
    return math.gcd(pow(a, r // 2) - 1, N), math.gcd(pow(a, r // 2) + 1, N)


if __name__ == "__main__":
    random.seed(0)
    pire = max(((sum(not temoin(a, n) for a in range(2, n - 1)) / (n - 3), n)
                for n in range(9, 5000, 2) if not premier(n)))
    print("1. Miller-Rabin: worst proportion of strong liars for odd composite n < 5000:",
          f"{pire[0]:.4f} (n = {pire[1]}), theoretical bound 1/4")
    print("   561 = 3·11·17 (Carmichael number): 2^560 mod 561 =", pow(2, 560, 561),
          "; Miller-Rabin witness for a = 2:", temoin(2, 561))
    print("   errors on the n < 20000 with 20 trials:",
          sum(miller_rabin(n) != premier(n) for n in range(2, 20000)))
    vrai = identite_probable(lambda x, y: (x + y) ** 5,
                             lambda x, y: x**5 + 5*x**4*y + 10*x**3*y**2 + 10*x**2*y**3 + 5*x*y**4 + y**5, 2, 5)
    faux = identite_probable(lambda x, y: (x + y) ** 5,
                             lambda x, y: x**5 + 5*x**4*y + 10*x**3*y**2 + 10*x**2*y**3 + 4*x*y**4 + y**5, 2, 5)
    print("2. Schwartz-Zippel: (x+y)^5 = exact expansion:", vrai, "; with a mistake:", faux)
    F = formule_aleatoire(100, 2000)
    fr = [fraction_satisfaite(F, {v: random.random() < .5 for v in range(1, 101)}) for _ in range(200)]
    print("3. MAX-3SAT: average over 200 random assignments:", round(sum(fr) / len(fr), 4), "(7/8 = 0.875)")
    print("4. Deutsch:", [deutsch(f) for f in (lambda x: 0, lambda x: 1, lambda x: x, lambda x: 1 - x)])
    for n in (4, 8, 12):
        k, p = grover(n, 5)
        print(f"   Grover, N = 2^{n} = {2**n}: {k} oracle calls, probability of finding the target {p:.4f}")
    for N, a in ((15, 7), (21, 2)):
        t = (N * N - 1).bit_length()                # 2^t >= N^2, as in Shor's algorithm
        Q = 2 ** t
        loi = shor_simule(N, a, t)
        pics = [y for y in range(Q) if loi[y] > 0.02]
        # each measurement y gives a denominator d (a divisor of r, often r itself);
        # we try its small multiples, which is an easy classical computation
        candidats = []
        for y in pics:
            d = periode_depuis_mesure(y, Q, N)
            candidats += [d * k for k in range(1, N // d + 1) if pow(a, d * k, N) == 1][:1]
        r = min(candidats)
        print(f"   Shor, N = {N}, a = {a}, Q = 2^{t}: likely measurements {pics}",
              f"(total probability {sum(loi[y] for y in pics):.3f}; total distribution {sum(loi):.3f}), period r = {r},",
              "factors", facteurs_depuis_periode(N, a, r))
