# Current Lean coverage

Generated from the elaborated `BookIndex.lean` ledger.

The exported manuscript statement inventory has a unique label for every numbered entry.
Standalone checks validate this snapshot; use `--book PATH` to check current private sources.
Declaration names resolve, and all project theorem dependencies use only the standard Lean axioms.
A complete status applies to the stated scope; it does not certify every surrounding example or discussion.

| Numbered-statement status | Count |
|---|---:|
| complete | 46 |
| partial | 1 |
| needs definitions | 1 |
| analysis-heavy | 7 |
| external citation | 1 |
| compatibility condition | 1 |
| Total | 57 |

| Source | Category | Statement | Status | Scope |
|---|---|---|---|---|
| 1.1 (`chapters/ch1/section1.tex`) | numbered | aut size bound | complete | Finite underlying type. Relabeling.lean additionally treats indexed relations of arbitrary arity. |
| 1.2 (`chapters/ch1/section2.tex`) | numbered | symmetry deficit basic bounds | complete | Deficit and degree-of-order bounds and extremal equality cases, including arbitrary indexed relation arities. |
| 1.3 (`chapters/ch1/section3.tex`) | numbered | automorphism group under refinement | complete | Adding named relations, represented by forgetting symbols in the reverse direction; not inclusion of tuples inside one relation. |
| 1.3 (`chapters/ch1/section3.tex`) | numbered | symmetry deficit monotonicity under refinement | complete |  |
| 1.4 (`chapters/ch1/section4.tex`) | numbered | relation ops equivariant | complete |  |
| 1.4 (`chapters/ch1/section4.tex`) | numbered | aut inherited by ops | complete |  |
| 1.4 (`chapters/ch1/section4.tex`) | numbered | separate relations intersection | complete |  |
| 1.4 (`chapters/ch1/section4.tex`) | numbered | Complement and converse preserve symmetry deficit | complete |  |
| 1.4 (`chapters/ch1/section4.tex`) | numbered | invariant operand bounds | complete |  |
| 2.4 (`chapters/ch2/section4.tex`) | numbered | labeled realizations orbit stabilizer | complete | Actual relabeling action, automorphism subgroup, and isomorphism-class fiber. |
| 2.4 (`chapters/ch2/section4.tex`) | identity | entropy-energy form of relational partition function | complete | Finite fixed signature and finite underlying type; energy is constant on isomorphism classes. |
| 2.5 (`chapters/ch2/section5.tex`) | identity | symmetry deficit as logarithmic degeneracy | complete | Instantiated at the relabeling orbit of a binary structure; also proved for arbitrary indexed arities. |
| 2.5 (`chapters/ch2/section5.tex`) | numbered | symmetry entropy additive under multiplicativity | complete | Conditional on multiplicative degeneracy; does not assert multiplicativity for unrestricted disjoint unions. |
| 2.5 (`chapters/ch2/section5.tex`) | numbered | stirling maximal symmetry deficit growth | complete |  |
| 3.3 (`chapters/ch3/section3.tex`) | numbered | k-block Euler--Lagrange equations | complete | Interior densities and a coordinate derivative hypothesis on the supplied energy functional. |
| 3.3 (`chapters/ch3/section3.tex`) | numbered | continuum Euler--Lagrange equation | analysis-heavy |  |
| 3.3 (`chapters/ch3/section3.tex`) | numbered | second variation of homogeneous phase | analysis-heavy |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | two-block Euler--Lagrange equations | complete |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | diagonal branch of two-block system | complete |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | two-block Hessian and modes | complete | Second partial derivatives and the resulting operator/eigenmode identities on the interior. |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | unrefined curvature threshold at the half point | complete | Curvature changes at beta J = 4. The half point is stationary only when beta J = 0. |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | two block hessian stability | complete | Positive definiteness below the threshold and a negative direction above it; no equilibrium assertion. |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | refined two-block first derivatives | complete |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | refined two-block symmetric branch | complete |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | refined two-block Hessian | complete |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | refined two-block Hessian eigenmodes | complete |  |
| 3.4 (`chapters/ch3/section4.tex`) | numbered | refined two-block critical instability | complete |  |
| 3.5 (`chapters/ch3/section5.tex`) | numbered | binary entropy derivatives | complete |  |
| 3.5 (`chapters/ch3/section5.tex`) | numbered | landau local form | complete | Every fixed interior mean 0 < m < 1; exact displayed coefficients and O(d^6) remainder. |
| 3.5 (`chapters/ch3/section5.tex`) | numbered | landau expansion symmetric | complete |  |
| 3.5 (`chapters/ch3/section5.tex`) | numbered | landau quartic minimizers | complete | Global and local minima of the quartic truncation for positive quartic coefficient. |
| 3.5 (`chapters/ch3/section5.tex`) | numbered | exact broken stationary pair | complete |  |
| 3.5 (`chapters/ch3/section5.tex`) | numbered | exact broken branch asymptotic | complete | The inverse branch d_ex(K) is constructed, tends to zero, and satisfies the stated K-limit. |
| 3.6 (`chapters/ch3/section6.tex`) | numbered | O(m)-invariance of continuum functional | complete | Interval-integral field energy, differentiable real-normed-space fields, and linear isometry equivalences. |
| 3.6 (`chapters/ch3/section6.tex`) | numbered | minima of radial quartic potential | complete | Vector minima in a nontrivial real normed space; positive radius is realized. |
| 3.6 (`chapters/ch3/section6.tex`) | numbered | O(m) to O(m-1) breaking pattern | analysis-heavy |  |
| 3.6 (`chapters/ch3/section6.tex`) | numbered | quadratic expansion around chosen vacuum | partial | Exact potential polynomial, including cubic and quartic terms; field decomposition and integrated remainder remain open. |
| 3.7 (`chapters/ch3/section7.tex`) | numbered | Relational Low-Energy Fields | analysis-heavy |  |
| 3.8 (`chapters/ch3/section8.tex`) | numbered | connection supplies covariant infinitesimal comparison | needs definitions | The present prose statement is conceptual; a precise bundle, gauge transformation, and covariance theorem remain to be specified. |
| 3.9 (`chapters/ch3/section9.tex`) | numbered | curvature obstructs path independence | analysis-heavy |  |
| 3.10 (`chapters/ch3/section10.tex`) | numbered | Euler--Lagrange equations from curvature action | analysis-heavy |  |
| 3.11 (`chapters/ch3/section11.tex`) | numbered | order parameter and coarse symmetry deficit | complete | Exact two-slot parameter-exchange action; this is not relabeling the two blocks of a diagonal/off-diagonal density matrix. |
| 4.1 (`chapters/ch4/section1.tex`) | numbered | operations are functional ternary relations | complete |  |
| 4.2 (`chapters/ch4/section2.tex`) | numbered | operation preservation iff graph preservation | complete |  |
| 4.2 (`chapters/ch4/section2.tex`) | numbered | automorphism group as operation-table stabilizer | complete | A genuine relabeling action on indexed binary relations and ternary operation graphs. |
| 4.2 (`chapters/ch4/section2.tex`) | numbered | automorphisms decrease under added algebraic data | complete |  |
| 4.3 (`chapters/ch4/section3.tex`) | numbered | algebraic symmetry-deficit bounds | complete | Both extremal equality characterizations for the represented binary algebraic data. |
| 5.2 (`chapters/ch5/section2.tex`) | numbered | automorphism group of (Z,+) has order 2 | complete |  |
| 5.2 (`chapters/ch5/section2.tex`) | numbered | unital ring of integers is rigid | complete |  |
| 5.2 (`chapters/ch5/section2.tex`) | numbered | real field automorphisms trivial | complete |  |
| 5.3 (`chapters/ch5/section3.tex`) | numbered | finite compatibility of infinite symmetry-deficit invariants | compatibility condition | Applies the finite compatibility assumption; no infinite invariant is constructed. |
| 6.1 (`chapters/ch6/section1.tex`) | numbered | reference stabilizer conjugate | complete |  |
| 6.1 (`chapters/ch6/section1.tex`) | numbered | reference-group deficit is constant on G-orbits | complete |  |
| 6.2 (`chapters/ch6/section2.tex`) | numbered | Monotonicity at fixed reference group | complete |  |
| 6.3 (`chapters/ch6/section3.tex`) | numbered | dimension of the homogeneous-space quotient | analysis-heavy |  |
| 6.4 (`chapters/ch6/section4.tex`) | numbered | haar subgroup index | complete | Measurable subgroups and normalized left-invariant probability; applies in particular to closed subgroups with normalized Haar measure. |
| 6.4 (`chapters/ch6/section4.tex`) | numbered | nonnegativity and invariance of measure symmetry deficit | complete | Probability measures, absolute continuity and integrable log density for the real integral; action by measurable equivalences preserving the reference measure. |
| 6.7 (`chapters/ch6/section7.tex`) | numbered | openai hard sphere bec | external citation | Reported external preprint theorem; source statement checked, full proof not independently verified here; not formalized or assumed as a Lean axiom. |
| 6.7 (`chapters/ch6/section7.tex`) | numbered | number-conserving invariance | complete | Every bounded operator on a complex Hilbert space is fixed by scalar-unitary conjugation, covering both fixed-N and one-particle operators. No condensation or partial-trace construction is asserted. |
| 2.3 (`chapters/ch2/section3.tex`) | supplement | positive relational Gibbs weights | complete | Positive multiplicities and a nonempty finite ensemble imply normalization and positivity. Normalized deficit lies in [0,1] when the permutation count exceeds one; expectations and examples remain separate targets. |
| 3.1 (`chapters/ch3/section1.tex`) | supplement | exact block-profile fiber count | complete | Independent directed relation positions, represented as disjoint block coordinates; product of binomial coefficients. |
| 3.1 (`chapters/ch3/section1.tex`) | supplement | partition regrouping by profiles | complete | Exact finite fiber identity. Entropy and large-system approximations do not follow from this identity alone. |
| 1.2 (`chapters/ch1/section2.tex`) | supplement | finite examples and 512-relation enumeration | finite proof target | Distinguished-point, arrow and cycle examples and the 104-class histogram require dedicated certified finite computations. |
| 3.2 (`chapters/ch3/section2.tex`) | supplement | profile entropy and continuum limit | analysis-heavy | Binomial entropy asymptotics, profile error estimates, a Laplace principle and step-kernel convergence remain open. |
| 5.2 (`chapters/ch5/section2.tex`) | supplement | additional infinite algebraic examples | needs definitions | Examples beyond the proved integer and real-field cases need separate representations and automorphism proofs. |
| 6.5 (`chapters/ch6/section5.tex`) | supplement | von Mises and Bessel analysis | analysis-heavy | Normalization, self-consistency, threshold, KL formula and critical asymptotics are analytic proof targets distinct from simulation evidence. |
| 6.5 (`chapters/ch6/section5.tex`) | supplement | finite-system numerical comparisons | computational | Monte Carlo measurements and fitted errors are computational evidence; the analytic formulas are tracked separately. |
| App. B (`chapters/app/appendixB.tex`) | supplement | structural susceptibility and scaling proposals | research program | Proposed diagnostics and universality comparisons are research hypotheses, not established formal theorems. |
