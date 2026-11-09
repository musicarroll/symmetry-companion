# Symmetry companion

Python experiments, Lean proofs, and Beamer slides accompanying *Algebraic
Symmetry Breaking: Symmetry, Randomness, and Relational Structures*.
The manuscript is maintained separately in a private repository. This repository
builds without access to it and starts with independent Git history.

The book is available on Amazon:  https://www.amazon.com/dp/B0HR22Q63S/ref=sr_1_1?crid=271J1B70N1W7Y&dib=eyJ2IjoiMSJ9.JUh_vQnsDoba6Nrv5IL10UQBt-IpgN3V325ULk5Lg47FJaPMSxabL_Y9FkOteLu8DSx4oz3R62_sY2SNOJ9aSKXS-aVp1yNqx16IZ2SPBBXkaSiQaPne7Z0wvi5kKeDu5h41II12kM4YV-UxQitQR0lKuXxakiIYbHYSt411ZKEIXK0b9uC72Z9es0NwLE_FSSBpItzJeejBTm46hUUZ2Vw8rNvMPDxhThXGnlYaPT4.KW8fyzJ_UN68PCsz1aUoT0bCvvVh0Qg3nQ1IinPbcj0&dib_tag=se&keywords=algebraic%2Bsymmetry&qid=1794251749&sprefix=algebraic%2Bsymmetry%2Caps%2C162&sr=8-1&th=1

The current release version is recorded in `VERSION`. Book proof 0.1.0 cites
companion tag `v0.1.0`; use that tag to reproduce the edition's supporting
materials. Subsequent work may appear on the default branch.

| Location | Contents |
|---|---|
| `src/`, `scripts/` | Numerical models, scans, plotting, and validation tools |
| `results/data/`, `results/figures/` | Recorded numerical results and presentation assets |
| `SymmetryMonograph/`, `SymmetryMonograph.lean` | Lean formalization and statement ledger |
| `lean/` | Formalization guide, exported statement inventory, and slide count table |
| `doc/lean-*` | Formalization status, scope, and historical audit records |
| `slides/` | Beamer sources and compiled presentation |
| `references.bib` | Bibliography snapshot used by the slides |

## Python

Use Python 3.10 or later. From this repository:

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python scripts/run_two_block_scan.py
.venv/bin/python scripts/plot_two_block_results.py
```

[Computational guide](README_computational.md) documents the additional finite
algebra, lattice, and reference-group experiments. The recorded numerical
results were carried over unchanged during the repository split.

## Lean

Install Lean through elan. `lean-toolchain` and `lake-manifest.json` pin the
toolchain and dependencies. On a fresh checkout:

```bash
lake exe cache get
lake build
python3 scripts/check_lean_coverage.py
```

The checker resolves declaration names, audits theorem axioms, and compares the
ledger with the exported statement inventory. A standalone check certifies
agreement with that snapshot; it cannot inspect later private manuscript edits.
See [the Lean guide](lean/README.md) for proof scopes and the full workflow.

## Slides

With PDFLaTeX, BibTeX, and Make installed:

```bash
make -C slides
```

The [presentation PDF](slides/symmetry-slides.pdf) uses figures, bibliography,
and generated counts stored entirely in this repository. Source changes require
editorial review before refreshing the slide snapshot.

## Validation and maintenance

```bash
python3 -m unittest discover -s tests
```

[SYNC.md](SYNC.md) documents coordination with an optional private manuscript
checkout. [GITHUB_SETUP.md](GITHUB_SETUP.md) describes the first public push.
[Publication tools and versioning](doc/publication-builds.md) describe the
optional paperback/MathML EPUB builds for an explicitly supplied manuscript.
