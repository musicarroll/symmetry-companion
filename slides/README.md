# Beamer presentation

The entry point is `symmetry-slides.tex`. The deck is intended for a
45--60-minute research presentation to mathematicians and physicists; backup
slides follow the main conclusion.

## Build

From this directory:

```bash
make
```

The build uses PDFLaTeX and BibTeX and produces `symmetry-slides.pdf`. It reuses
the companion repository's figures from `../results/figures/` and bibliography from
`../references.bib`; no shell escape is required.

For TeXstudio, open `symmetry-slides.tex` as the root document and set the
working directory to `slides/`.

## Keeping the deck synchronized

`make` compares public computation, Lean, slide, bibliography, and figure sources
with `source.sha256`. All inputs are in this public repository. When sources
change, review affected slides using `SOURCE_MAP.md`, then run:

```bash
make refresh-snapshot
make
```

When also maintaining the private manuscript, pass its path relative to this
`slides/` directory to check or record the private review digest as well:

```bash
make refresh-snapshot BOOK=../../symmetry-monograph
make BOOK=../../symmetry-monograph
```

The manuscript digest is stored only in the private repository. Snapshot updates
record an editorial review; they do not replace that review. See [SYNC.md](../SYNC.md)
for figure, bibliography, and Lean inventory coordination.
