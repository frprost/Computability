"""Computability and AI: three small experiments (chapter "Computability and artificial intelligence").

1. Synthesis by blind search for a testable specification.
2. The diagonal sequence against a predictor: it is wrong every time.
3. Gold's argument: a learner that learns all finite languages
   changes its mind forever on a text for the infinite language {a^n : n >= 1}.
"""
from itertools import count


# 1. Testable specification: psi(x, y) decidable, and for every x there is a y.
def synthese(psi):
    """The program  x -> mu y psi(x, y)  satisfies psi (slow, but correct)."""
    return lambda x: next(y for y in count() if psi(x, y))


racine = synthese(lambda x, y: y * y <= x < (y + 1) * (y + 1))   # integer part of sqrt(x)


# 2. Predictors: a function from the list of bits seen so far to the predicted bit.
def majorite(vus):
    return 1 if 2 * sum(vus) > len(vus) else 0


def dernier_motif(vus):
    """Finds the longest suffix seen earlier and predicts what followed it."""
    for k in range(len(vus) - 1, 0, -1):
        suffixe = vus[-k:]
        for i in range(len(vus) - k - 1, -1, -1):
            if vus[i:i + k] == suffixe:
                return vus[i + k]
    return 0


def diagonale(predicteur, n):
    s = []
    for _ in range(n):
        s.append(1 - predicteur(s))   # always take the opposite of the prediction
    return s


# 3. Gold. A learner receives the words one by one and proposes a language.
def apprenant_prudent(vus):
    """Proposes the finite set of words seen: it learns every finite language."""
    return frozenset(vus)


def texte_de_gold(apprenant, etapes):
    """Builds the beginning of Gold's text for L = {a, aa, aaa, ...}."""
    texte, changements, devinette = [], 0, None
    for k in range(1, etapes + 1):
        mot = "a" * k
        cible = frozenset("a" * j for j in range(1, k + 1))
        while True:                      # repeat the word until the learner guesses {a,...,a^k}
            texte.append(mot)
            nouvelle = apprenant(texte)
            if nouvelle != devinette:
                changements += 1
                devinette = nouvelle
            if nouvelle == cible:
                break
    return texte, changements


if __name__ == "__main__":
    print("1. integer square root by blind search:", [racine(x) for x in (0, 1, 15, 16, 99)])
    for nom, p in (("majority", majorite), ("last pattern", dernier_motif)):
        s = diagonale(p, 40)
        erreurs = sum(p(s[:i]) != s[i] for i in range(len(s)))
        print(f"2. predictor {nom:14s} sequence {''.join(map(str, s[:24]))}...  errors: {erreurs}/40")
    texte, ch = texte_de_gold(apprenant_prudent, 10)
    print("3. Gold: after", len(texte), "words, the learner has changed its mind", ch, "times;",
          "on the infinite text, it will keep changing forever")
