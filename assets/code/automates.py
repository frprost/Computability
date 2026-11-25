"""Cellular automata (chapter "Other models of computation").

1. Elementary automata: Wolfram numbering, rule 110, rule 90 and Pascal's triangle.
2. Simulation of a Turing machine by a cellular automaton of radius 1: one step of the
   machine = one step of the automaton. Checked on the 3-state busy beaver.
   (Identifiers are in French; directions are 'D' = right, 'G' = left.)
"""
from math import comb


def pas_elementaire(ligne, regle):
    """A finite row, surrounded by 0s (the pattern can grow by one cell on each side)."""
    l = [0, 0] + ligne + [0, 0]
    return [(regle >> (l[i - 1] << 2 | l[i] << 1 | l[i + 1])) & 1 for i in range(1, len(l) - 1)]


def evolution(regle, t, depart=(1,)):
    lignes = [list(depart)]
    for _ in range(t):
        lignes.append(pas_elementaire(lignes[-1], regle))
    return lignes


# Turing machine -> cellular automaton     ---------------------------------------
def regle_locale(delta):
    """The states of the automaton are symbols s or pairs (q, s) (head in state q on s).
    The new value of a cell depends only on itself and its two neighbours."""
    def f(g, c, d):
        if isinstance(c, tuple):                    # the head is here: write, it moves away
            q, s = c
            return delta[q, s][1] if (q, s) in delta else c      # halting state: freeze
        if isinstance(g, tuple) and g in delta and delta[g][2] == 'D':
            return (delta[g][0], c)                 # the head arrives from the left
        if isinstance(d, tuple) and d in delta and delta[d][2] == 'G':
            return (delta[d][0], c)                 # the head arrives from the right
        return c
    return f


def pas_automate(f, config, blanc='0'):
    l = [blanc, blanc] + config + [blanc, blanc]   # the configuration can grow by one cell on each side
    return [f(l[i - 1], l[i], l[i + 1]) for i in range(1, len(l) - 1)]


def machine_directe(delta, q0, n_pas, blanc='0'):
    bande, pos, q = {}, 0, q0
    for _ in range(n_pas):
        if (q, bande.get(pos, blanc)) not in delta:
            break
        q, s, d = delta[q, bande.get(pos, blanc)]
        bande[pos] = s
        pos += 1 if d == 'D' else -1
    return bande, pos, q


if __name__ == "__main__":
    print("1. rule 110 (start: one cell), first 8 rows:")
    for l in evolution(110, 7):
        print("   " + "".join("█" if x else "·" for x in l).rstrip("·").rjust(16))
    lignes = evolution(90, 31)
    ok90 = True
    for t, l in enumerate(lignes):
        # l has 2t+1 cells, with indices j = -t..t
        for i, x in enumerate(l):
            j = i - t
            attendu = comb(t, (t + j) // 2) % 2 if (t + j) % 2 == 0 else 0
            ok90 &= (x == attendu)
    print("   rule 90 = Pascal's triangle modulo 2 on 32 rows:", ok90)
    print("   rule 240 shifts by one cell:", evolution(240, 3, (1, 0, 1, 1))[3] == [0, 0, 0, 0, 0, 0, 1, 0, 1, 1])
    # 2. 3-state busy beaver (A0 -> 1RB, ...), 14 steps, 6 ones
    delta = {('A', '0'): ('B', '1', 'D'), ('A', '1'): ('H', '1', 'D'),
             ('B', '0'): ('C', '0', 'D'), ('B', '1'): ('B', '1', 'D'),
             ('C', '0'): ('C', '1', 'G'), ('C', '1'): ('A', '1', 'G')}
    f = regle_locale(delta)
    config, gauche = [('A', '0')], 0                # gauche: position of cell 0 of the list
    for t in range(20):
        config, gauche = pas_automate(f, config), gauche - 1
        bande, pos, q = machine_directe(delta, 'A', t + 1)
        tete = [i for i, c in enumerate(config) if isinstance(c, tuple)]
        assert len(tete) == 1 and tete[0] + gauche == pos and config[tete[0]][0] == q
        for i, c in enumerate(config):
            s = c[1] if isinstance(c, tuple) else c
            assert s == bande.get(i + gauche, '0')
    uns = sum((c[1] if isinstance(c, tuple) else c) == '1' for c in config)
    print("2. 3-state busy beaver simulated by a cellular automaton: identical to the machine",
          "for 20 steps; final state", config[tete[0]][0], ";", uns, "symbols 1")
