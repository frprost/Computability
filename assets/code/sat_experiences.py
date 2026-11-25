"""A modern SAT solver against three families of formulas (chapter "Complexity").

Requires the python-sat package (pip install python-sat), which provides the CaDiCaL solver.
1. Structured formulas (n queens): tens of thousands of variables, solved quickly.
2. Random 3-SAT at the threshold (4.26 clauses per variable): the time grows quickly with n.
3. Pigeonhole principle (n+1 pigeons, n holes): unsatisfiable, and exponential for
   every resolution-based solver (Haken, 1985).
"""
import random, statistics, time
from itertools import combinations
from pysat.solvers import Solver

SOLVEUR = "cd15"   # CaDiCaL 1.5


def resoudre(clauses):
    t0 = time.perf_counter()
    with Solver(name=SOLVEUR, bootstrap_with=clauses) as s:
        rep = s.solve()
        conflits = s.accum_stats().get("conflicts", 0)
    return rep, time.perf_counter() - t0, conflits


def reines(n):
    v = lambda i, j: i * n + j + 1
    C = [[v(i, j) for j in range(n)] for i in range(n)]                 # one queen per row
    for i in range(n):
        for j1, j2 in combinations(range(n), 2):
            C.append([-v(i, j1), -v(i, j2)])                            # not two in a row
            C.append([-v(j1, i), -v(j2, i)])                            # not two in a column
    for d in range(-n + 1, 2 * n):                                      # diagonals
        for diag in ([(i, i - d) for i in range(n) if 0 <= i - d < n],
                     [(i, d - i) for i in range(n) if 0 <= d - i < n]):
            for a, b in combinations(diag, 2):
                C.append([-v(*a), -v(*b)])
    return C, n * n


def aleatoire_3sat(n, ratio, graine):
    r = random.Random(graine)
    return [[x * r.choice((1, -1)) for x in r.sample(range(1, n + 1), 3)] for _ in range(round(ratio * n))]


def pigeons(n):                                   # n+1 pigeons, n holes
    v = lambda p, h: p * n + h + 1
    C = [[v(p, h) for h in range(n)] for p in range(n + 1)]
    for h in range(n):
        for p1, p2 in combinations(range(n + 1), 2):
            C.append([-v(p1, h), -v(p2, h)])
    return C, (n + 1) * n


if __name__ == "__main__":
    import sys
    parties = sys.argv[1:] or ["1", "2", "3"]
    if "1" in parties:
        print("1. n queens")
        for n in (30, 60, 100):
            C, nv = reines(n)
            rep, t, c = resoudre(C)
            print(f"   n={n:3d}: {nv:6d} variables, {len(C):8d} clauses -> {'SAT' if rep else 'UNSAT'} in {t:.2f} s", flush=True)
    if "2" in parties:
        print("2. random 3-SAT, 4.26 clauses per variable (median over 5 formulas)")
        for n in (100, 150, 200, 250, 300):
            res = [resoudre(aleatoire_3sat(n, 4.26, g)) for g in range(5)]
            print(f"   n={n:3d}: median time {statistics.median(r[1] for r in res):8.3f} s, "
                  f"median conflicts {int(statistics.median(r[2] for r in res)):9d}", flush=True)
    if "3" in parties:
        print("3. pigeonhole principle")
        for n in range(7, 11):
            C, nv = pigeons(n)
            rep, t, c = resoudre(C)
            print(f"   {n+1:2d} pigeons, {n:2d} holes: {nv:4d} variables -> {'SAT' if rep else 'UNSAT'} in {t:8.2f} s, {c} conflicts", flush=True)
