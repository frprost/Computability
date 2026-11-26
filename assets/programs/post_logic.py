"""post_logic.py: from the Post problem to first-order logic (Floyd's reduction).

To a list of dominoes (u_1/v_1, ..., u_k/v_k) we associate the sentence

    phi = [ AND_i P(u_i, v_i)  and  for all x, y : P(x, y) -> AND_i P(x.u_i, y.v_i) ]  ->  there is z : P(z, z)

where P is a binary relation symbol, e a constant (the empty word), and "x.w" the term obtained by
appending to x the letters of w one by one. Two ways of writing this term:
  * with one unary function f_a per letter a: x.ab = f_b(f_a(x));
  * with ONE single binary function c (append a letter) and one constant per letter: x.ab = c(c(x, a), b).
The second uses only symbols of arity at most two: a binary relation, a binary function,
constants. phi is valid (true in every structure) if and only if the dominoes have a solution.

With post.py, we obtain, for every Turing machine Z and every input x, a sentence that is valid if and
only if Z halts on x: validity is therefore not decidable (theorem of Church and Turing).

    python3 post_logic.py                   # the example a/baa, ab/aa, bba/bb: sentence and deduction
    python3 post_logic.py --tptp            # the sentence in TPTP format, for a prover (E, Vampire)
    python3 post_logic.py --machine examples/successor.tm 0

MIT licence. Authors: Frédéric Prost and Claude.
"""
import sys

import post


def term(x, word, binary, names):
    """The term x.word, written with unary functions f_a or with the binary function c."""
    t = x
    for a in word:
        t = "c(%s,%s)" % (t, names[a]) if binary else "f_%s(%s)" % (names[a], t)
    return t


def letter_names(dominoes):
    letters = sorted({a for h, b in dominoes for a in h + b})
    return {a: "l%d" % k for k, a in enumerate(letters)}


def sentence(dominoes, binary=True, tptp=False):
    """Floyd's sentence, in readable notation or in TPTP format (fof)."""
    names = letter_names(dominoes)
    if tptp:
        X, Y, Z, E = "X", "Y", "Z", "e"
        base = " & ".join("p(%s,%s)" % (term(E, h, binary, names), term(E, b, binary, names)) for h, b in dominoes)
        step = " & ".join("p(%s,%s)" % (term(X, h, binary, names), term(Y, b, binary, names)) for h, b in dominoes)
        return "fof(post, conjecture, ( ( (%s) & ! [X,Y] : ( p(X,Y) => (%s) ) ) => ? [Z] : p(Z,Z) ) )." % (base, step)
    base = " ∧ ".join("P(%s, %s)" % (term("e", h, binary, names), term("e", b, binary, names)) for h, b in dominoes)
    step = " ∧ ".join("P(%s, %s)" % (term("x", h, binary, names), term("y", b, binary, names)) for h, b in dominoes)
    return "[ %s ∧ ∀x ∀y ( P(x, y) → %s ) ] → ∃z P(z, z)" % (base, step)


def deduction(dominoes, solution, binary=True):
    """If the sequence of indices is a solution, the list of facts P(s, t) deduced from the hypotheses,
    one domino after another; the last one has the form P(t, t), which proves the conclusion."""
    names = letter_names(dominoes)
    h, b = dominoes[solution[0]]
    facts = [(term("e", h, binary, names), term("e", b, binary, names))]
    for i in solution[1:]:
        u, v = dominoes[i]
        x, y = facts[-1]
        facts.append((term(x, u, binary, names), term(y, v, binary, names)))
    return facts


def model_of_words(dominoes, depth):
    """The "natural" model: the objects are the words, e is the empty word, x.w is concatenation,
    and P(x, y) is true if (x, y) is obtained by chaining dominoes. The hypotheses of phi are true there,
    and the conclusion is true there if and only if the dominoes have a solution. We enumerate the pairs
    obtained with at most "depth" dominoes and look for a pair (z, z)."""
    pairs = {d: [i] for i, d in enumerate(dominoes)}
    front = dict(pairs)
    for _ in range(depth):
        for (x, y), s in front.items():
            if x == y:
                return s
        new = {}
        for (x, y), s in front.items():
            for i, (u, v) in enumerate(dominoes):
                c = (x + u, y + v)
                n = min(len(c[0]), len(c[1]))
                if c[0][:n] == c[1][:n] and c not in pairs:
                    pairs[c] = s + [i]
                    new[c] = s + [i]
        front = new
    for (x, y), s in front.items():
        if x == y:
            return s
    return None


def _main(argv):
    if "--machine" in argv:
        from machines import Machine
        k = argv.index("--machine")
        machine = Machine.from_file(argv[k + 1])
        args = [int(a) for a in argv[k + 2:] if not a.startswith("--")]
        dm, names = post.modified_dominoes(machine, *args)
        dominoes = post.to_ordinary(dm)
        sol = post.ordinary_solution(post.solution_from_computation(machine, dm, names, *args), len(dm))
        e = sentence(dominoes, tptp="--tptp" in argv)
        print("Machine of %d quadruples -> %d dominoes -> sentence of %d characters." % (len(machine), len(dominoes), len(e)))
        if "--tptp" in argv:
            print(e)
        f = deduction(dominoes, sol)
        assert f[-1][0] == f[-1][1]
        print("The machine halts: the deduction has %d stages and ends with P(t, t), with t of %d characters."
              % (len(f), len(f[-1][0])))
        return
    dominoes = [(("a",), ("b", "a", "a")), (("a", "b"), ("a", "a")), (("b", "b", "a"), ("b", "b"))]
    if "--tptp" in argv:
        print(sentence(dominoes, tptp=True))
        return
    print("Dominoes: a/baa, ab/aa, bba/bb (letters a = l0, b = l1)")
    print("Sentence, with a binary function c:")
    print("  " + sentence(dominoes))
    print("The same, with unary functions:")
    print("  " + sentence(dominoes, binary=False))
    sol = model_of_words(dominoes, 8)
    print("Solution found in the model of words:", [i + 1 for i in sol])
    for x, y in deduction(dominoes, sol):
        print("  P(%s, %s)" % (x, y))
    print("The last fact is P(t, t): the sentence is proved.")


if __name__ == "__main__":
    _main(sys.argv)
