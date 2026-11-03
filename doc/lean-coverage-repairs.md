# Lean coverage repairs

This records changes following the audit of revision `b5cc56f`.
The [generated current ledger](lean-coverage-status.md) is authoritative for
counts, scopes and remaining proof targets. The historical audit is retained
without rewriting its original findings as if the fixes had already existed.

## Implemented

- **Finite extrema:** upper deficit bounds and both directions of the maximum
  equality cases, including degree of order; algebraic zero and maximum cases.
- **Actual symmetry actions:** fixed indexed symbols and arbitrary relation
  arities, including operation graphs with nullary operations; automorphisms
  are subgroups and actual stabilizers. Existing binary structures embed in
  the common representation. The old tautological table stabilizer is replaced.
- **Ensembles:** isomorphism-class fibers are actual orbits, and the labeled
  partition sum regroups with exponential symmetry-deficit multiplicities.
  Positive finite weights imply positive partition functions and normalized
  positive Gibbs weights. Normalized deficit bounds have an explicit positive
  denominator hypothesis.
- **Profiles:** exact product-of-binomial fiber count for independent directed
  block positions and exact finite regrouping by a profile map. These results
  do not assert entropy asymptotics or a continuum limit.
- **Two-block calculus:** the unrefined Hessian is identified through actual
  second partial derivatives; positive definiteness and a negative direction
  at the half point are proved. The stationary-equation check proves that this
  point is stationary only at zero coupling.
- **Landau and branches:** all local quartic minima are classified, the origin
  is a local maximum at negative quadratic coefficient, and scalar radial
  minima are lifted to vectors. A constructed inverse branch tends to zero
  and satisfies the book's coupling-parameter 3/8 limit. Rescaling the centered
  entropy pair proves the full sixth-order remainder for every interior mean.
- **Reduced and field symmetry:** exact two-slot swap stabilizers and both
  coarse-deficit equivalences; orthogonal invariance of the interval field
  energy, including the derivative term; exact potential expansion with its
  cubic and quartic terms retained.
- **Chapter 6:** positive Haar measure iff finite subgroup index, with the
  reciprocal-index formula; KL nonnegativity, equality and invariance; and
  scalar-unitary conjugation invariance of arbitrary bounded Hilbert-space
  operators, covering both fixed-number and reduced one-particle operators.
- **Coverage integrity:** all 57 numbered statements have stable labels and
  exactly one ledger entry. The omitted Chapter 6 results are included. Exact
  swap calculations are no longer called computational evidence. External
  citations and compatibility requirements have distinct statuses. Nine
  supplementary targets make important unnumbered material visible.
  CI resolves every mapped declaration, audits all project theorem axioms,
  and rejects missing statements, duplicates and stale generated tables.

## Manuscript corrections

The text now distinguishes curvature at the unrefined half point from
stationary-branch instability, invariance of each relation from absence of
relations, adding symbols from inserting tuples, profile-fiber entropy from
individual orbit deficit, and parameter exchange from block-label permutation.
The diagonal/off-diagonal matrix remains invariant under simultaneous block
permutations even when its two values differ. Regularity, vacuum-constraint,
variation-support, dimension and KL-integrability qualifications have been
made explicit where needed. The human-authored preface was not edited.

## Work still open

The numbered targets still requiring proofs are continuum first and second
variations; the orthogonal quotient and dimension; the full integrated
Goldstone expansion; the constrained vacuum-field reduction; a precise
connection covariance statement; curvature/parallel-transport comparison;
Yang--Mills variation; and homogeneous-space dimension. The connection entry
needs a mathematical specification before a meaningful proof can be written.
The Goldstone entry is partial: its potential polynomial is proved, while the
field decomposition and integrated remainder are not.

Supplementary targets include certified small-structure enumeration and
examples; binomial entropy estimates, a Laplace principle and continuum
convergence; additional infinite algebraic examples; and the von Mises/Bessel
transition analysis. Numerical measurements remain computational evidence.
Structural-susceptibility and universality proposals remain research claims.
The externally cited hard-sphere condensation theorem has no Lean proof here
and has not been introduced as an axiom.

The next effective proof sequence is to finish the integrated Goldstone
expansion, then specify function spaces and admissible variations for the
continuum results. The geometric work needs explicit bundle and group-action
models before its prose conclusions can be matched to Lean statements.

## Verification

The dependency-aware Lean build and the coverage/dependency audit pass without
unfinished proofs or additional axioms. The checker was also exercised against
missing, duplicated and mismatched statement entries. The monograph and slide
PDFs are rebuilt from their prescribed entry points; the slide source map is
reviewed before its snapshot is refreshed. No numerical experiments were
rerun, because their code, data and numerical claims were unchanged.
