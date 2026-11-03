# Lean formalization

Run from the repository root:

```bash
~/.elan/bin/lake build
python3 scripts/check_lean_coverage.py
```

The second command compares the exported manuscript statement inventory with
stable labels in `BookIndex.lean`, resolves every mapped Lean name, audits all
project theorem dependencies, and checks the generated public coverage artifacts.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted axioms.
It works without the private manuscript. To compare the current private sources
and the book's generated tables, add `--book ../symmetry-monograph`.
Semantic correspondence still requires reviewing each statement's hypotheses
and scope. The exported inventory contains labels, source paths, and statement
kinds, without copying the manuscript's chapter prose.

[Current counts and scopes](../doc/lean-coverage-status.md) are generated from
the elaborated ledger. Numbered statements, unnumbered identities, and
supplementary claims are counted separately. External citations,
compatibility conditions, computational evidence, and research proposals are
explicit statuses rather than completed Lean proofs.

## File map

| Module | Content |
|---|---|
| `FiniteRelationalStructures.lean` | Binary relation families, bounds, refinement, and both directions of extremal equality cases. |
| `BinaryRelations.lean` | Equivariance and preservation under binary relation operations. |
| `Relabeling.lean` | Arbitrary indexed arities, genuine automorphism subgroups, operation graphs including nullary operations, binary bridges, isomorphism classes, and concrete orbit partition sums. |
| `Chapter2.lean` | Positive finite Gibbs weights, normalization, profile regrouping, conditional entropy identities, and the Stirling remainder. |
| `FiniteProfiles.lean` | Independent block configurations and the exact product-of-binomial-coefficients fiber count. |
| `Chapter3.lean` | Finite coordinate derivatives, two-block equations and algebraic quartic results. |
| `Chapter3Landau.lean` | Refined Hessian derivatives, centered Landau jet, uniform remainder, unique exact broken local minima, and the parametrized critical limit. |
| `Chapter3Completion.lean` | Unrefined second derivatives and curvature, local quartic minima, vector minima, the inverse branch, and the critical limit in the coupling parameter. |
| `GeneralLandau.lean` | Exact scaling identity and sixth-order remainder at every fixed interior mean. |
| `TwoBlockSymmetry.lean` | Actual two-slot permutation action, stabilizers, and exact coarse-deficit equivalences. |
| `FieldEnergy.lean` | Orthogonal invariance including field derivatives, and the exact Goldstone potential polynomial. |
| `Chapter4.lean` | Binary operations as ternary graphs, refinement, and algebraic deficit equality cases. |
| `Chapter5.lean` | Integer and real-field automorphisms; the finite compatibility requirement. |
| `Chapter6.lean` | Reference stabilizers, conjugacy, finite-index deficit and monotonicity. |
| `Chapter6Measure.lean` | Haar subgroup index; extended KL divergence, finite integral positivity/equality, and invariance under measurable equivalences. |
| `Chapter6Operators.lean` | Scalar-unitary conjugation on arbitrary complex Hilbert spaces; fixed-number and one-particle operator invariance. |
| `BookIndex.lean` | Statement labels, scopes, statuses and declaration mappings. |

## Updating coverage

1. Prove the result, or record an explicit remaining gap and scope.
2. Update `BookIndex.lean`; preserve stable LaTeX statement labels.
3. Run `lake build`, then `python3 scripts/check_lean_coverage.py --write`.
   When the private book is available, also pass `--book ../symmetry-monograph`;
   this updates the exported inventory and the private book tables together.
4. Review generated artifacts, the affected manuscript and summaries when
   available, and the slides and `slides/SOURCE_MAP.md`. Follow [SYNC.md](../SYNC.md)
   to synchronize figures and bibliography and record review snapshots.
5. Build the slides and the private book if present, then rerun the checker
   without `--write` to confirm synchronization.

Continuous integration builds Lean and validates the public inventory snapshot
and generated public artifacts without private access. The slides use
`lean/generated/lean-ledger-counts.tex`; the private Appendix D retains its own
synchronized generated tables. The original audit is preserved in
[the historical review](../doc/lean-coverage-review.md); implemented repairs and
outstanding work are in [the repair record](../doc/lean-coverage-repairs.md).
