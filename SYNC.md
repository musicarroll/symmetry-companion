# Maintaining the public companion and private manuscript

Keep the repositories as siblings when working on both:

```text
Physics/
  symmetry-monograph/   private AMS LaTeX manuscript
  symmetry-companion/  public Python, Lean, results, and slides
```

They have independent histories and remotes. Public builds and CI never require
access to the private repository. There is no submodule or symlink between them.

## Ownership

| Material | Authority | Other checkout |
|---|---|---|
| Chapters, cover, chapter summaries | Private manuscript | Remain private |
| Bibliography | Private `references.bib` | Exported copy for public slides |
| Python, Lean, numerical data, figures, slides | Public companion | Book keeps figure copies for independent compilation |
| Statement inventory | Exported from private labeled statements | Public labels/source paths/kinds only, without chapter prose |
| Proof status and generated ledger | Public Lean ledger | Generated book tables and public slide count table |

The synchronization script copies files in these specific directions; it does
not delete extra files or copy private source trees into the public checkout.
Review regenerated figures and affected claims before accepting changed outputs.

## Coordinated change

Run these commands from the companion repository. Give Codex access to both
folders for work spanning the manuscript and companion.

1. Update the affected chapter, private summary, code, proof, or result. Update
   `SymmetryMonograph/BookIndex.lean` when a statement or its proof scope changes.
2. After Lean changes, build and check the actual manuscript inventory:

   ```bash
   lake build
   python3 scripts/check_lean_coverage.py --book ../symmetry-monograph --write
   ```

   With `--write`, this exports the public inventory and coverage artifacts and
   regenerates the three ledger tables in the private book. Without `--write`,
   it compares both repositories without changing them.
3. Synchronize bibliography and figures, then verify the copies:

   ```bash
   python3 scripts/sync_private_book.py --book ../symmetry-monograph --write
   python3 scripts/sync_private_book.py --book ../symmetry-monograph
   ```
4. Review affected slides and `slides/SOURCE_MAP.md`. After that review:

   ```bash
   make -C slides refresh-snapshot BOOK=../../symmetry-monograph
   make -C slides BOOK=../../symmetry-monograph
   ```

   `BOOK` is relative to `slides/` because Make changes directory there. The
   public source digest is stored in `slides/source.sha256`; the manuscript
   review digest is stored privately in `companion-review.json`.
5. Compile the private book from `main.tex` (PDFLaTeX twice; run BibTeX as needed).
   Recheck the coverage inventory and both Git diffs, then commit each repository
   separately. Mention the corresponding commit in the other repository's commit
   message when coordinating a mathematical change.

## Public-only work

```bash
python3 scripts/check_lean_coverage.py
make -C slides
```

The default coverage check verifies the committed inventory snapshot and audited
Lean declarations. It does not silently look for a neighboring private checkout.
When public sources change, review the slides before `make -C slides
refresh-snapshot`. When the private checkout becomes available, run the live
`--book` checks and review any corresponding manuscript changes.

For a manuscript-only edit, review the affected slides and use the two `make`
commands with `BOOK` above. The private review digest detects changes even when
the statement inventory and the public files have not changed.
