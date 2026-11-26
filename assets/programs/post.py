"""post.py: the Post correspondence problem, and the translation of a Turing machine into dominoes.

A domino is a pair (top, bottom) of words; here a word is a tuple of "letters", each letter
being a string (a tape symbol, a state name, the separator #...). A solution of a list
of dominoes is a sequence of indices such that the concatenation of the tops equals that of the bottoms.

Construction (chapter "Other models"): for a machine Z and an input x, we build
 1. a "modified" list of dominoes, whose solution must begin with the first domino;
    it has a solution if and only if Z halts on x: the only way to make the top and the
    bottom equal is to write the sequence of configurations of the computation, separated by #, the bottom always
    being one configuration ahead;
 2. an ordinary list of dominoes, by the star trick of the chapter "Languages".

    python3 post.py                         # dominoes for the addition 1 + 1, solution checked
    python3 post.py examples/successor.tm 0 --dominoes
    python3 post.py --search                # breadth-first search on small examples

MIT licence. Authors: Frédéric Prost and Claude.
"""
import sys
from collections import deque

from machines import Machine, BLANK, initial_tape

SEP, HALT, STAR, END = "#", "H", "⋆", "◇"


# --------------------------------------------------------------------------- solutions
def concatenate(dominoes, indices):
    top, bottom = [], []
    for i in indices:
        top.extend(dominoes[i][0])
        bottom.extend(dominoes[i][1])
    return tuple(top), tuple(bottom)


def is_solution(dominoes, indices, first=None):
    if not indices or (first is not None and indices[0] != first):
        return False
    h, b = concatenate(dominoes, indices)
    return h == b


def search(dominoes, max_nodes=200000, first=None):
    """Breadth-first search for a solution. Only the "lead" of one side over the other is kept:
    two sequences that leave the same lead have the same extensions. Returns a solution
    (list of indices) or None if nothing is found within the limit: this is a semi-decision."""
    start = [first] if first is not None else range(len(dominoes))
    queue, seen = deque(), set()

    def lead(h, b):
        n = min(len(h), len(b))
        if h[:n] != b[:n]:
            return None
        return ("t", h[n:]) if len(h) > n else ("b", b[n:])

    for i in start:
        a = lead(*dominoes[i])
        if a is not None:
            if a[1] == ():
                return [i]
            queue.append((a, [i]))
            seen.add(a)
    while queue and len(seen) < max_nodes:
        (side, rest), seq = queue.popleft()
        for i, (h, b) in enumerate(dominoes):
            if side == "t":
                a = lead(rest + h, b)
            else:
                a = lead(h, rest + b)
            if a is None:
                continue
            if a[1] == ():
                return seq + [i]
            if a not in seen:
                seen.add(a)
                queue.append((a, seq + [i]))
    return None


# --------------------------------------------------------------------------- machine -> dominoes
def modified_dominoes(machine, *args):
    """List of dominoes for which a solution beginning with domino 0 exists iff the machine halts.
    Returns (dominoes, names) where names[i] explains the role of domino i."""
    sigma = sorted(machine.symbols())
    states = sorted(machine.states())
    tape = initial_tape(args)
    word = tuple(tape.get(i, BLANK) for i in range(max(tape) + 1)) if tape else (BLANK,)
    D, names = [], []

    def add(h, b, name):
        D.append((tuple(h), tuple(b)))
        names.append(name)

    # start: the first configuration, preceded by a (harmless) blank so that the head can move left
    add([SEP], [SEP, BLANK, machine.initial_state] + list(word) + [SEP], "start")
    for a in sigma:
        add([a], [a], "copy " + a)
    add([SEP], [SEP], "separator")
    add([SEP], [BLANK, SEP], "separator, a blank added on the right")
    for (q, s, act, q2) in machine.quadruples:
        name = "rule %s %s %s %s" % (q, s, act, q2)
        if act == "R":
            add([q, s], [s, q2], name)
        elif act == "L":
            for c in sigma:
                add([c, q, s], [q2, c, s], name)
            add([SEP, q, s], [SEP, q2, BLANK, s], name + " (left edge)")
            add([SEP, q, s], [BLANK, SEP, q2, BLANK, s], name + " (left edge, blank on the right)")
        else:
            add([q, s], [q2, act], name)
    for q in states:
        for s in sigma:
            if (q, s) not in machine.table:
                add([q, s], [HALT, s], "halt in %s on %s" % (q, s))
    for a in sigma:
        add([a, HALT], [HALT], "erasure to the left of H")
        add([HALT, a], [HALT], "erasure to the right of H")
    add([HALT, SEP, SEP], [SEP], "end")
    return D, names


def solution_from_computation(machine, dominoes, names, *args, max_steps=10**5):
    """Builds the solution of the modified problem from the computation of the machine (which must halt).
    We write the successive rows (the configurations); each top row is copied to the bottom
    while being turned into the next row, the bottom always being one row ahead."""
    index = {}
    for i, (h, b) in enumerate(dominoes):
        index.setdefault((tuple(h), tuple(b)), i)

    def ind(h, b):
        return index[(tuple(h), tuple(b))]

    def copy(words):
        return [ind([c], [c]) for c in words]

    tape = initial_tape(args)
    right = [tape.get(i, BLANK) for i in range(max(tape) + 1)] if tape else [BLANK]
    left, q = [BLANK], machine.initial_state
    sol = [0]
    pad = False                 # must a blank be added on the right of the next row?
    first_row, steps = True, 0
    while True:
        s = right[0]
        rule = machine.table.get((q, s))
        left_edge = rule is not None and rule[2] == "L" and not left
        # the top separator before this row writes, at the bottom, the end of the next row
        if not first_row and not left_edge:
            sol.append(ind([SEP], ([BLANK] if pad else []) + [SEP]))
        if rule is None:                                          # the machine halts
            sol += copy(left) + [ind([q, s], [HALT, s])] + copy(right[1:])
            break
        act, q2 = rule[2], rule[3]
        old_pad, pad = pad, False
        if act == "R":
            sol += copy(left) + [ind([q, s], [s, q2])] + copy(right[1:])
            left, right = left + [s], right[1:]
            if not right:
                right, pad = [BLANK], True
        elif act == "L" and left_edge:
            sol.append(ind([SEP, q, s], ([BLANK] if old_pad else []) + [SEP, q2, BLANK, s]))
            sol += copy(right[1:])
            right = [BLANK] + right
        elif act == "L":
            c = left[-1]
            sol += copy(left[:-1]) + [ind([c, q, s], [q2, c, s])] + copy(right[1:])
            left, right = left[:-1], [c] + right
        else:
            sol += copy(left) + [ind([q, s], [q2, act])] + copy(right[1:])
            right = [act] + right[1:]
        q, first_row, steps = q2, False, steps + 1
        if steps > max_steps:
            raise RuntimeError("too long")
    # the bottom row now contains H; one letter is erased per row
    row = left + [HALT] + right
    while len(row) > 1:
        sol.append(ind([SEP], ([BLANK] if pad else []) + [SEP]))
        if pad:
            row = row + [BLANK]
            pad = False
        k = row.index(HALT)
        if k > 0:
            sol += copy(row[:k - 1]) + [ind([row[k - 1], HALT], [HALT])] + copy(row[k + 1:])
            row = row[:k - 1] + row[k:]
        else:
            sol += [ind([HALT, row[1]], [HALT])] + copy(row[2:])
            row = [HALT] + row[2:]
    sol.append(ind([SEP], [SEP]))
    sol.append(ind([HALT, SEP, SEP], [SEP]))
    return sol


def to_ordinary(dominoes):
    """Star trick (chapter "Languages"): the first domino becomes the only one that can begin."""
    def left(w):
        r = []
        for c in w:
            r += [STAR, c]
        return r

    def right(w):
        r = []
        for c in w:
            r += [c, STAR]
        return r
    new = [(tuple(left(dominoes[0][0])), tuple([STAR] + right(dominoes[0][1])))]
    for h, b in dominoes:
        new.append((tuple(left(h)), tuple(right(b))))
    new.append(((STAR, END), (END,)))
    return new


def ordinary_solution(modified_sol, nb_dominoes):
    """A solution 0, i2, ..., ir of the modified problem gives the solution 0, i2+1, ..., ir+1, end."""
    return [0] + [i + 1 for i in modified_sol[1:]] + [nb_dominoes + 1]


def show_word(w, max_letters=60):
    t = " ".join(w)
    return t if len(w) <= max_letters else " ".join(w[:max_letters]) + " …"


def _main(argv):
    import os
    if "--search" in argv:
        examples = [
            [(("a",), ("b", "a", "a")), (("a", "b"), ("a", "a")), (("b", "b", "a"), ("b", "b"))],
            [(("1",), ("1", "1", "1")), (("1", "0", "1", "1", "1"), ("1", "0")), (("1", "0"), ("0",))],
            [(("a", "b"), ("a",)), (("b",), ("a", "b"))],
        ]
        for d in examples:
            s = search(d)
            print(" / ".join("%s:%s" % ("".join(h), "".join(b)) for h, b in d), "->", s)
        m = Machine.from_text("q0 1 B q1")
        dm, _ = modified_dominoes(m, 0)
        print("Machine \"q0 1 B q1\" on 0:", len(dm), "dominoes; solution found by the search:", search(dm, first=0))
        return
    show = "--dominoes" in argv
    argv = [a for a in argv if not a.startswith("--")]
    if len(argv) >= 2:
        machine = Machine.from_file(argv[1])
        args = [int(x) for x in argv[2:]]
    else:
        machine = Machine.from_file(os.path.join(os.path.dirname(os.path.abspath(__file__)), "examples", "addition.tm"))
        args = [1, 1]
    dm, names = modified_dominoes(machine, *args)
    if show:
        for i, ((h, b), n) in enumerate(zip(dm, names)):
            print("%3d  %-22s / %-28s %s" % (i, " ".join(h), " ".join(b), n))
    sol = solution_from_computation(machine, dm, names, *args)
    assert is_solution(dm, sol, first=0)
    h, _ = concatenate(dm, sol)
    print("Modified problem: %d dominoes; solution of %d dominoes, checked." % (len(dm), len(sol)))
    print("Common word:", show_word(h, 80))
    do = to_ordinary(dm)
    so = ordinary_solution(sol, len(dm))
    assert is_solution(do, so)
    print("Ordinary Post problem: %d dominoes; solution of %d dominoes, checked." % (len(do), len(so)))


if __name__ == "__main__":
    _main(sys.argv)
