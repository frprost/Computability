"""Complexity: two experiments (chapter "Complexity").

1. Reachability in a graph: breadth-first search (memory proportional to the
   number of vertices) versus Savitch's recursive algorithm (stack depth
   log2 N, each level keeping only three vertices), at the cost of a huge running time.
2. The Cook-Levin encoding for a small nondeterministic machine, checked
   by a small SAT solver (search with unit propagation).
"""
from itertools import product
from math import ceil, log2


# ---------- 1. Savitch ----------
def accessible_largeur(arcs, n, s, t):
    vus, file = {s}, [s]
    while file:
        u = file.pop(0)
        for v in range(n):
            if (u, v) in arcs and v not in vus:
                vus.add(v)
                file.append(v)
    return t in vus, len(vus)               # memory: up to n vertices kept


def savitch(arcs, n, s, t):
    stats = {"appels": 0, "profondeur": 0}

    def acces(u, v, i, prof):                # is v reachable from u in at most 2^i edges?
        stats["appels"] += 1
        stats["profondeur"] = max(stats["profondeur"], prof)
        if i == 0:
            return u == v or (u, v) in arcs
        return any(acces(u, m, i - 1, prof + 1) and acces(m, v, i - 1, prof + 1) for m in range(n))

    return acces(s, t, ceil(log2(n)), 0), stats


# ---------- 2. Cook-Levin ----------
# Nondeterministic one-tape machine: on an input of 0s and 1s, it "guesses"
# a cell containing 1 while moving right, and accepts if it finds one.
# Transitions (state, read) -> set of (state, written, move).
DELTA = {
    ("q", "0"): {("q", "0", 1)},
    ("q", "1"): {("q", "1", 1), ("acc", "1", 0)},
    ("acc", "0"): {("acc", "0", 0)}, ("acc", "1"): {("acc", "1", 0)}, ("acc", "B"): {("acc", "B", 0)},
}
ETATS, SYMB = ("q", "acc"), ("0", "1", "B")


def formule_cook_levin(entree, p):
    """Clauses (in conjunctive normal form) of the Cook-Levin tableau, for p steps and cells 0..p."""
    var = {}
    def v(*cle):                              # variable number
        return var.setdefault(cle, len(var) + 1)
    C, cases, T = [], range(p + 1), range(p + 1)
    def exactement_un(lits):
        C.append(list(lits))
        C.extend([[-a, -b] for k, a in enumerate(lits) for b in lits[k + 1:]])
    for i in T:                               # each row: one state, one position, one symbol per cell
        exactement_un([v("Q", i, s) for s in ETATS])
        exactement_un([v("H", i, j) for j in cases])
        for j in cases:
            exactement_un([v("X", i, j, a) for a in SYMB])
    C.append([v("Q", 0, "q")]); C.append([v("H", 0, 0)])           # initial row
    for j in cases:
        C.append([v("X", 0, j, entree[j] if j < len(entree) else "B")])
    for i in range(p):                        # transitions
        for j in cases:
            for a in SYMB:                    # cell away from the head: unchanged
                C.append([v("H", i, j), -v("X", i, j, a), v("X", i + 1, j, a)])
            for s in ETATS:
                for a in SYMB:
                    choix = [(s2, b, d) for (s2, b, d) in DELTA.get((s, a), ()) if 0 <= j + d <= p]
                    hyp = [-v("H", i, j), -v("Q", i, s), -v("X", i, j, a)]
                    # at least one choice: one variable per choice
                    cs = [v("C", i, j, s, a, k) for k in range(len(choix))]
                    C.append(hyp + cs)
                    for c, (s2, b, d) in zip(cs, choix):
                        for lit in (v("Q", i + 1, s2), v("X", i + 1, j, b), v("H", i + 1, j + d)):
                            C.append(hyp + [-c, lit])
    C.append([v("Q", p, "acc")])              # acceptance
    return C, len(var)


def dpll(clauses, affect=None):
    """Exhaustive search with unit propagation."""
    affect = dict(affect or {})
    while True:
        reste, unit = [], None
        for c in clauses:
            if any(affect.get(abs(l)) == (l > 0) for l in c):
                continue
            libres = [l for l in c if abs(l) not in affect]
            if not libres:
                return None
            if len(libres) == 1:
                unit = libres[0]
            reste.append(libres)
        if not reste:
            return affect
        if unit is None:
            break
        affect[abs(unit)] = unit > 0
    l = reste[0][0]
    for val in (l > 0, l <= 0):
        r = dpll(reste, {**affect, abs(l): val})
        if r is not None:
            return r
    return None


def accepte_par_formule(entree, p):
    clauses, _ = formule_cook_levin(entree, p)
    return dpll(clauses) is not None


def accepte_directement(entree):
    return "1" in entree


if __name__ == "__main__":
    n = 64
    arcs = {(i, i + 1) for i in range(n - 1)} | {(i, i + 2) for i in range(0, n - 2, 7)}
    print("1. breadth-first:", accessible_largeur(arcs, n, 0, n - 1))
    rep, st = savitch(arcs, 16, 0, 15)
    print("   Savitch on 16 vertices: reachable =", rep, "; calls =", st["appels"],
          "; stack depth =", st["profondeur"], "(log2 16 = 4)")
    cl, nv = formule_cook_levin("0010", 5)
    print("2. formula for the input 0010 and 5 steps:", nv, "variables,", len(cl), "clauses")
    ok = all(accepte_par_formule("".join(w), len(w) + 1) == accepte_directement("".join(w))
             for k in range(0, 7) for w in product("01", repeat=k))
    print("   satisfiability of the formula: agrees with the machine on the 127 words of length <= 6:", ok)
