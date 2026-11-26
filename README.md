# Computability — a manual with three reading levels

Authors: **Frédéric Prost and Claude**.

**Version 2.** The three levels are more sharply contrasted: the philosophical level is a self-contained narrative readable with a secondary-school education (it replaces the formal statements), the technical level is unchanged, and the technological level contains “workshops” with the complete constructions and downloadable Python programs (`assets/programs/`, archive `assets/programs.zip`). This is the main version of the manual. It adds two-stack automata, two-counter machines (the tape coded in two numbers) and the reduction of Turing machines to Post’s dominoes, then to logic with one binary relation and one binary function. The chapter on complexity also contains a dated section on the announced proof of VP ≠ VNP (November 2026).

What a machine can compute, what no machine will ever be able to compute, and why this concerns all of us. The manual is a static HTML site: each result has a statement and can be read at three levels: philosophical (meaning and implications), technical (mathematical proofs) and technological (complete constructions, executable machines), with programs and interactive simulations.

This is the English edition of *Calculabilité — manuel à trois niveaux de lecture*. The mathematical notation is the same in both editions.

## Reading the manual

Open `index.html` in a browser. No server or network connection is needed: KaTeX is bundled in `assets/katex/`. The site can also be published as is, for example with GitHub Pages (main branch, root folder).

## Contents

- 25 chapters, from Turing machines to complexity, randomness and quantum computing, followed by case studies (the Ackermann function, busy beavers, computability and AI, other models of computation);
- appendices: reading paths, Cantor’s argument, basic notions, Leibniz, bibliography;
- exercises with solutions at the end of each chapter;
- the programs of the technological level, in `assets/programs/`: Turing machine simulator, recursive functions, compiler from recursive functions to Turing machines, converse translation (Kleene normal form), λ-calculus, universal function and machine, s-m-n and fixed point, diagonal argument, two-stack automata, counter machines, Post’s dominoes and their translation into logic; `python3 tests.py` checks everything;
- the verification programs of the other chapters, in `assets/code/`; each Python file runs with `python3 file.py` and checks what it claims (the C files give their compilation and usage instructions in their header).

Results stated without proof are marked “quoted for information”.

## File layout

| Path | Role |
|---|---|
| `*.html` | generated pages (do not edit by hand) |
| `_sources/pages/*.html` | page sources, with a header (title, table-of-contents label, prerequisites) |
| `_sources/build.py` | assembly: template, table of contents, numbering, previous/next links |
| `assets/style.css` | layout (light and dark themes) |
| `assets/*.js` | interactive simulators (Turing machines, λ-calculus, Post correspondence, cellular automata) |
| `assets/programs/` | Python programs of the technological level (archive produced by the build: `assets/programs.zip`) |
| `assets/code/` | verification programs |

Page sources use the same tags as the French edition (`<res>`, `<enonce>`, `<philo>`, `<tech>`, `<techno>`, `<exo>`, `<corrige>`), and the anchors (`id`) are those of the French edition, so that a link from one edition can be carried over to the other by changing only the file name.

## Rebuilding the site

From the root of the repository:

```
python3 _sources/build.py
```

To produce a copy in another folder: `python3 _sources/build.py --out FOLDER`, then copy `assets/` into `FOLDER`.

## Licence

- Text, figures and exercises: [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/) (Creative Commons Attribution-ShareAlike 4.0 International).
- Code (`assets/programs/`, `assets/code/`, `assets/*.js`, `assets/style.css`, `_sources/build.py`): MIT licence, see [`LICENSE-CODE`](LICENSE-CODE).
- KaTeX (`assets/katex/`) keeps its own MIT licence, see `assets/katex/LICENSE`.

Details are in [`LICENSE`](LICENSE).
