# Slide-to-book source map

Use this map when the separately maintained private monograph changes.
Chapter and appendix references below describe private sources; they are not
public build dependencies. Public builds use exported inventory and count metadata. Frame titles are stable identifiers;
page numbers are deliberately omitted because the book is still evolving.

| Slide topic | Primary monograph source | Other dependency |
|---|---|---|
| Central thesis; evidence levels | Introduction; chapter summaries | private `requirements.md` |
| Physical systems and three roles for infinity; selective physical reading path | Introduction; Chapter 5, Section 1; Chapter 6, Sections 1 and 5 | Finite size, continuous variables, and thermodynamic limits distinguished |
| Finite structures and symmetry deficit | Chapter 1, Sections 1--3 | `FiniteRelationalStructures.lean`; arbitrary indexed signatures and relabeling in `Relabeling.lean` |
| Orbit size and single-arrow example | Chapter 1, Section 2 | `orbit_single_arrow.pdf` |
| Refinement and relation operations | Chapter 1, Sections 3--4 | `BinaryRelations.lean` |
| Relational partition function and energy--multiplicity example | Chapter 2, Sections 1--2 (especially Example 2.7) | `Chapter2.lean`; concrete orbit-class regrouping in `Relabeling.lean`; physical counting qualification in Section 2.1 |
| Two-block coarse graining | Chapter 3, Sections 1--3 | exact profile fibers in `FiniteProfiles.lean`; continuum limits remain open |
| Refined instability, Landau remainder, unique exact broken minima, and critical scaling | Chapter 3, Sections 4--5 | `Chapter3Landau.lean`; inverse branch and minima in `Chapter3Completion.lean`; general mean in `GeneralLandau.lean` |
| Numerical mean-field evidence | Chapter 3, Section 11; Appendix B | generated figures and data |
| Graphon limit | Chapter 3, Section 2 | Lovász--Szegedy citation |
| Goldstone and gauge geometry | Chapter 3, Sections 6--10 | `FieldEnergy.lean` proves orthogonal invariance and the potential polynomial; quotient and gauge results remain open |
| Finite algebraic structures | Chapter 4, Sections 1--4 | `Chapter4.lean` |
| Infinite structures and candidate deficits | Chapter 5, Sections 1--4 | `Chapter5.lean` |
| Reference-group phase diagnostics, scaling taxonomy, computed $SO(2)$ transition, and interacting Bose/Heisenberg comparison | Chapter 6, Sections 1--7 | discrete core in `Chapter6.lean`; Haar/KL in `Chapter6Measure.lean`; scalar-unitary invariance in `Chapter6Operators.lean`; `src/reference_group_phase_model.py`; generated data and figures; external OpenAI Math Release theorems; remaining statements indexed in `BookIndex.lean` |
| Formalization ledger | Appendix D; `lean/README.md`; `BookIndex.lean` | `lake build`; `scripts/check_lean_coverage.py`; `lean/generated/lean-ledger-counts.tex` exported from the same Lean ledger as the private tables |
| Numerical limitations, structural-susceptibility hypothesis, and open problems | Appendices B--C; Chapter 3, Section 12 | generated lattice figures |

The synchronization script hashes the public computational, Lean, figure, and
presentation sources. With `BOOK` supplied, it also checks a private manuscript
review digest. When either check reports a change, review the corresponding
rows and slides before refreshing the snapshots. See `../SYNC.md`.

Review after the coverage repairs (27 October 2026): the mean-field frames use
the refined threshold 2/J and remain valid. The unrefined half point is not an
equilibrium at 4/J; the book and chapter summary now call that a curvature
threshold. The two-slot parameter exchange is distinct from block relabeling.
The Landau and machine-checked-core frames have been updated. Existing
reference-group and Bose frames remain mathematically consistent with the
new proofs; they do not claim that the external condensation theorem is
formalized. Numerical figures and reported measurements are unchanged.

Review after the physical-scope revision (3 November 2026): the overview now
distinguishes finite system size, continuous state variables, thermodynamic
limits, and abstract infinite algebra, and gives the selective physical reading
path. The partition-function frame states what is counted and the need to
identify redundant labels. The reference-diagnostic frame and conclusion now
apply explicitly to finite systems as well as phase limits, matching Chapter
6's title, Physical Reference Symmetry, Finite Systems, and Phase Limits.
The Chapter 5 examples, diagnostic formulas, numerical frames, and formalization
ledger were reviewed and remain consistent; no results or proof statuses changed.

Cover review (3 November 2026): the supplied cover artwork is included as a
separate opening page through `chapters/cover.tex`. This is a book production
change; the presentation's title frame and mathematical content remain current.

Repository split review (3 November 2026): all presentation inputs now reside in
the public companion. The formalization frame reads the public generated count
table; the statement inventory contains identifiers and source locations only.
The book's mathematical content, numerical measurements, and proof scopes are
unchanged. Existing frames were reviewed against the private manuscript and
remain consistent. The public build requires no private chapter files.
