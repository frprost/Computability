"""Kolmogorov complexity: a few experiments.

1. The self-delimiting code  w -> 1^|w| 0 w  and its decoding.
2. UPPER bounds on complexity by compression (zlib):
   a lower bound, on the other hand, cannot be computed (chapter 14).
"""
import os, zlib

def auto(w):                      # self-delimiting code
    return "1" * len(w) + "0" + w

def lire_auto(s):                 # returns (w, rest)
    k = s.index("0")
    return s[k + 1:2 * k + 1], s[2 * k + 1:]

def mot(n):                       # bijection N -> {0,1}* : 0->'', 1->'0', 2->'1', 3->'00'...
    return bin(n + 1)[3:]

def entier(w):
    return int("1" + w, 2) - 1

if __name__ == "__main__":
    e, p = mot(12), "0110"
    code = auto(e) + p
    print("e =", 12, "->", e, "; program", p, "; input of U:", code)
    print("decoding:", lire_auto(code), "-> e =", entier(lire_auto(code)[0]))
    assert all(entier(mot(n)) == n for n in range(1000))

    n = 100_000
    exemples = {
        "zeros": bytes(n),
        "pattern 'ab' repeated": b"ab" * (n // 2),
        "decimals of 1/7": ("142857" * (n // 6 + 1))[:n].encode(),
        "random bytes": os.urandom(n),
    }
    for nom, x in exemples.items():
        print(f"{nom:22s} {8*len(x):7d} bits -> at most {8*len(zlib.compress(x, 9)):7d} bits")
