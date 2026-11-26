# Programs of the manual “Computability” (technological level)

These programs carry out, down to the last quadruple, the constructions proved in the manual. They use only Python 3 (version 3.8 or later), with no library to install.

## Installation

Unzip the archive, open a terminal in the `programs` folder, then run:

```
python3 tests.py
```

On Windows, replace `python3` with `py` or `python`. The script checks every claim in about ten seconds and ends with “Everything as expected.”

## The files

| File | What it does | Chapter |
|---|---|---|
| `machines.py` | simulator of quadruple Turing machines; reads the `.tm` files | Turing machines |
| `examples/*.tm` | the machines of chapter 3 (addition, subtraction, multiplication, equality…) | Turing machines |
| `recursive.py` | recursive functions: terms C, S, A, σ, ρ, μ, evaluation, library | Recursive functions |
| `compiler.py` | compiler recursive functions → Turing machines | Equivalence |
| `turing_to_recursive.py` | translation Turing machine → recursive function (Kleene normal form) | Equivalence |
| `lambda_calculus.py` | λ-term reducer and compiler recursive functions → λ-calculus | λ-calculus, Equivalence |
| `universal.py` | universal function U(e, x), then the universal Turing machine obtained by compiling it | Universality |
| `recursion.py` | s-m-n theorem on machines; Kleene's fixed point; quine | s-m-n and recursion |
| `halting.py` | the diagonal argument run against several candidate “deciders” | Undecidability |
| `stacks.py` | two-stack automata: translation of a Turing machine, checked step by step | Other models |
| `counters.py` | the tape in two numbers, then two counters through the prime numbers | Other models |
| `post.py` | the Post dominoes of a Turing machine, and the solution drawn from the computation | Other models |
| `post_logic.py` | from dominoes to a logical sentence with a binary relation and a binary function | Logic and types |
| `tests.py` | checks the whole | |

## Examples

```
python3 machines.py examples/addition.tm 2 3 --trace
python3 recursive.py "rho[A(1,1), sigma[S, A(3,2)]]" 2 3
python3 compiler.py mult 2 3 --output mult.tm
python3 machines.py mult.tm 2 3
python3 turing_to_recursive.py examples/proper_subtraction.tm 5 2
python3 lambda_calculus.py --compile fact 3
python3 universal.py
python3 universal.py --machine
python3 recursion.py
python3 halting.py
python3 stacks.py examples/addition.tm 1 1 --trace
python3 counters.py examples/addition.tm 2 1
python3 post.py
python3 post_logic.py
```

Each file begins with a comment that explains its conventions and its use; `python3 file.py` without arguments prints it.

## Licence

MIT licence (see `LICENSE-CODE` at the root of the manual). Authors: Frédéric Prost and Claude.
