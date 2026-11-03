**Lean coverage review — 27 October 2026 (historical baseline)**

Subsequent repairs are described in [the repair record](lean-coverage-repairs.md).
For current statuses and proof scopes, use [the generated ledger](lean-coverage-status.md).

Reviewed repository revision `b5cc56f`, following `main.tex` through the six chapters and Appendices A–D, and comparing the mathematical claims with all project Lean modules. This is a coverage audit: numerical experiments and cited external proofs were not independently rerun or verified. Existing manuscript, Lean, and slide sources have not been changed.

The formal development builds successfully and contains substantial proved mathematics, especially the refined two-block analysis. The advertised **43 complete statements out of 57 ledger entries is not a reliable measure of complete monograph coverage**. Some entries cover a restricted representation or an intermediate result; two numbered statements are absent; and several important unnumbered claims have no entry.

**Validation and inventory**

- `~/.elan/bin/lake build` passed: “Build completed successfully (8665 jobs).” This was the normal dependency-aware build, not a clean rebuild of mathlib.
- An additional imported Lean audit checked all **116 distinct declaration names** listed in `BookIndex.lean`; all resolved.
- `#print axioms` was run for all **168 project theorem declarations** outside the ledger. Their dependencies contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx` or a project-specific axiom. These are standard Lean foundations, not unfinished proofs.
- A source scan found no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` in the project Lean files.
- The manuscript has **57 theorem/lemma/proposition environments**: Chapter 1: 9; Chapter 2: 3; Chapter 3: 28; Chapter 4: 5; Chapter 5: 4; Chapter 6: 8. The appendices have none of these environments.
- The ledger also has 57 entries, but these comprise **55 attempted mappings of numbered statements plus two unnumbered identities**. Adding the two omitted Chapter 6 statements would make **59 entries**, before adding other unnumbered claims. One existing mapping also has an obsolete description.

**Highest-priority findings**

1. **The basic finite bounds omit parts of the book's equality claims.**
   [Chapter 1 §2](../chapters/ch1/section2.tex) at line 324 asserts maximal deficit *precisely* for rigid structures and the analogous “exactly when” statement for degree of order. [FiniteRelationalStructures.lean](../SymmetryMonograph/FiniteRelationalStructures.lean), lines 106–127, proves rigid ⇒ the maximum value, but not either reverse implication. It also lacks a theorem bounding every relational deficit above by the logarithm of the permutation count. Chapter 4 has that upper bound, but [Chapter4.lean](../SymmetryMonograph/Chapter4.lean), lines 158–181, does not prove the two equality characterizations in [Chapter 4 §3](../chapters/ch4/section3.tex), line 45. These rows should be partial until the missing implications are supplied. Small cardinality/logarithm arguments should suffice.

2. **The unrefined two-block “critical temperature” entry masks an incorrect premise in the text.**
   [Chapter 3 §4](../chapters/ch3/section4.tex), line 324, calls `r = 1/2` a symmetric solution of the unrefined model. Its stationary equation at that point requires `βJ/2 = 0`; thus it is not stationary at `βJ = 4`. The formal theorem [twoBlock_critical_threshold_at_half](../SymmetryMonograph/Chapter3.lean), line 635, correctly proves only a sign criterion for a defined eigenvalue. It does not prove the book's equilibrium interpretation. The curvature threshold at that point is valid, but an instability of a stationary branch cannot be inferred from it. Correct the book statement before trying to formalize that interpretation. This concern does **not** apply to the refined model, whose centered point is stationary for all couplings.

3. **The unrefined Hessian and stability statements are only partly connected to derivatives.**
   The ledger maps the Hessian theorem to a definition and eigenvector identities ([Chapter3.lean](../SymmetryMonograph/Chapter3.lean), lines 85–91 and 137–150). It does not prove that this operator is the derivative of the unrefined free-energy gradient. The stability theorem at book line 399 is mapped to the same negative-eigenvalue criterion; its positive-definiteness conclusion below threshold has no explicit formal counterpart. Add the second partial derivatives and quadratic-form positivity/negativity statements. The refined Hessian does have actual gradient-derivative theorems in [Chapter3Landau.lean](../SymmetryMonograph/Chapter3Landau.lean), lines 160–229.

4. **The exact branch asymptotic is proved in the contrast parameter, with the inverse-branch step still missing.**
   The book's [exact asymptotic theorem](../chapters/ch3/section5.tex), line 592, is a limit of `d_ex(K)^2 / (K - 2)` as `K ↓ 2`. Lean proves `d^2 / (exactContrastCoupling d - 2) → 3/8` as `d ↓ 0` ([Chapter3Landau.lean](../SymmetryMonograph/Chapter3Landau.lean), line 1095). There is no Lean definition of `d_ex`, inverse identity, or theorem that this inverse tends to zero as `K ↓ 2`. Existence, uniqueness, strict monotonicity, and the parametrized limit already provide the main ingredients; the missing step is a real but comparatively small analytic bridge. The full local-minimum pair itself **is** proved, including uniqueness among nonsymmetric interior stationary points, for `2 < βJ < 2 log 3`.

5. **The representations and group actions do not yet cover the full signatures in the text.**
   The book permits arbitrary relation arities and finitary operations, including constants. [RelStructure](../SymmetryMonograph/FiniteRelationalStructures.lean), line 20, stores only binary relations; [AlgRelStructure](../SymmetryMonograph/Chapter4.lean), line 85, stores binary relations and binary operations. Neither presents its automorphisms as a `Subgroup` with closure and inverse proofs. The ternary operation graphs have a separate type and are not embedded into a common general relational structure. Moreover, `AlgRelStructure.Stabilizer` is defined using exactly the same predicate as `AutSet`, making `alg_autSet_eq_stabilizer` an `rfl` proof, without a relabeling action on operation tables. This is a valid definitional identity, but it leaves the natural-action claim in Chapter 4 §2 unconstructed. A fixed signature with indexed interpretations would also make explicit that each symbol is preserved separately.

6. **The finite-ensemble formulas are generic algebra, with the relational instantiation missing.**
   [Chapter2.lean](../SymmetryMonograph/Chapter2.lean), lines 24–99, gives finite weighted sums and an abstract group-action orbit–stabilizer theorem. There is no instantiated relabeling action on structures, identification of its stabilizer with `RelStructure.AutSet`, quotient of isomorphism classes, or theorem regrouping a labeled partition sum into orbit contributions. `partition_entropy_energy_form` assumes `multiplicity S = exp (symmetryDeficit S)`, and `symmetry_deficit_eq_log_degeneracy` unfolds a newly defined scalar logarithm; neither supplies that whole connection. `gibbs_weights_sum_one` proves normalization under `Z ≠ 0`, but does not establish positivity of `Z` or nonnegativity of the weights from positive multiplicities and a nonempty ensemble. These are useful proved cores, but not yet an integrated formal relational probability model.

7. **Two numbered statements and several analytic Chapter 6 results are absent from the ledger.**
   [Chapter 6 §7](../chapters/ch6/section7.tex) contains the external hard-sphere condensation theorem at line 56 and the number-conserving invariance lemma at line 90. Neither appears in `BookIndex.lean`; [Chapter6.lean](../SymmetryMonograph/Chapter6.lean) contains only the discrete stabilizer/index theory. The external theorem should be tracked explicitly as cited and unformalized, without importing it as an unmarked axiom. The invariance lemma is a separate, much smaller target, starting with invariance under scalar unitary conjugation and then treating reduced density operators. Section 6.5's von Mises normalization, Bessel self-consistency equation, critical threshold, KL formula, and asymptotics are also unformalized despite being analytic claims rather than simulation outputs.

8. **Two ledger classifications need correction independently of proof work.**
   The exact proposition in [Chapter 3 §11](../chapters/ch3/section11.tex), line 105, is not computational-only: it computes the stabilizer of a two-element swap action and relates it to `|p-q| = 0`. A concrete action plus a two-case cardinality argument would prove it. The swap invariance of the refined energy is already formalized. Also, the Chapter 3 §8 ledger entry says “covariantly constant fields minimize variation,” while the current [proposition](../chapters/ch3/section8.tex), line 194, concerns a connection supplying covariant comparison. That is a different claim and needs a precise target statement.

**Other incomplete or limited correspondences**

| Book result | What is proved | Remaining work |
|---|---|---|
| General local Landau form, §3.5 line 219 | Derivatives and remainder for the centered slice `m = 1/2` | Define the slice for arbitrary `0 < m < 1`, prove the displayed coefficients, and control the sixth-order remainder on `|d| < min(m, 1-m)`. The existing partial status is appropriate. |
| Quartic local minima, §3.5 line 526 | Global minimizers of the scalar quartic, [Chapter3.lean](../SymmetryMonograph/Chapter3.lean) lines 480 and 505 | Explicit local-minimum classification and instability/local maximum of zero when `A < 0`. Global minimizers are local minima, but global classification alone does not rule out additional nonglobal local minima. |
| Radial potential minima, §3.6 line 170 | Scalar radius minimization on `[0,∞)`, [Chapter3.lean](../SymmetryMonograph/Chapter3.lean) lines 547 and 578 | Lift to vectors using the norm, prove the minimizing sphere description, and state the dimension/nontriviality condition needed to realize a positive radius. |
| Finite compatibility of infinite deficits, §5.3 line 222 | An assumed equality is applied to two real arguments, [Chapter5.lean](../SymmetryMonograph/Chapter5.lean) lines 19–30 | This is a compatibility requirement, not a construction of an infinite invariant or a proof that a proposed invariant satisfies it. The formalization accurately reflects that limited logical content. |
| Stirling growth, §2.5 line 164 | The actual `O(log n)` estimate for `log(n!)` | A named superlinear-growth corollary and linkage to maximal relational deficit would complete the explanatory consequence; the asymptotic formula itself is proved. |

**Coverage beyond the numbered statements**

| Location | Uncovered material and appropriate treatment |
|---|---|
| Chapters 1–2 examples | Automorphism counts for distinguished points, arrows, cycles, and symmetric pairs; the 512 relations/104 classes enumeration and orbit histogram; small partition-function evaluations. These are exact finite claims suitable for proofs or certified enumeration, not intrinsically numerical-only. |
| §§2.1–2.3 | Relational Gibbs probability construction, expectations, normalized-deficit bounds with nonzero denominator, and concrete ensemble examples. Generic normalization exists, but the model-level statements and observables do not. |
| §§3.1–3.2 | Definitions of finite partitions, profile maps and fibers; the exact product-of-binomial-coefficients fiber count; the binomial entropy asymptotic; regrouping the partition sum by profiles; error bounds or a Laplace principle; step-kernel entropy and continuum convergence. Defining `kBlockEntropy` is not a proof of these counting and limiting statements. |
| §3.3 | The finite coordinate Euler–Lagrange calculation is proved under an energy derivative hypothesis. Logistic examples, continuum first and second variations, and stability of continuum phases are not. |
| §§3.6–3.10 | Orthogonal invariance of the field functional; the sphere orbit and stabilizer; quotient dimension; the quadratic Goldstone expansion; low-energy reduction; connections, curvature, and Yang–Mills variation. No project definitions of these field/geometric objects exist. The polynomial part of the Goldstone expansion can be separated from the harder functional analysis. |
| §3.12 | Renormalization and information geometry are explicitly prospective. Record them as research directions, not missing proofs of established theorems. |
| §4.4 | Operation-table counts, associativity/commutativity/identity/group predicates, the two-element ensemble, the three-element enumeration, and algebraic Gibbs ensembles. The generic finite-sum results could be reused after constructing these objects. |
| §§5.1–5.4 | Complex automorphisms, ordered integers, vector-space stabilizers, modular quotient examples, regular automorphisms, and finite-approximation schemes. The direct integer and real-field theorems are proved. Proposed random and limit ensembles are research directions, not completed results awaiting transcription. |
| §§6.2 and 6.6 | Finite-window sequences, rate limits, global versus product symmetry examples, fractional-deficit bounds, boundary-error implications, and fluctuation observables. Monotonicity at one fixed group is proved; none of these scaling results follows merely from that theorem. |
| §§6.3–6.4 | Quotient dimension, Haar subgroup/index equivalence, KL nonnegativity/equality/invariance, and finite-orbit KL compatibility. These are correctly recorded as open at the numbered-result level; the finite-orbit compatibility example is an additional approachable target. |
| §§6.5–6.7 | Separate analytic XY predictions, exact finite-group scaling, numerical sampling, operator invariance, external condensation/ferromagnetism results, and effective phase-field descriptions. None is verified by the current Chapter 6 file. |
| Appendices A–C | Numerical output is not certified by Lean. Exact identities relating contrast, squared contrast, variance, and susceptibility could be isolated. Numerical fits, equilibration, and universality claims require independent statistical/analytic evidence. The structural-susceptibility hypothesis would require moment/uniform-integrability and remainder-control hypotheses for a theorem; distributional convergence alone does not control variances. |
| Appendix D | The ledger repeats the incomplete mappings and totals described above. Its declaration names are strings, so compiling the ledger does not itself check their existence or agreement with the book. This audit checked existence separately. |

The continuum work also needs explicit hypotheses before formalization: a function space and admissible variations for §3.3, justification for differentiation under integrals, appropriate almost-everywhere conclusions, regularity of fields and connections, and boundary conditions or compact support for the action variation. For KL divergence, choose an extended-valued definition or impose integrability; absolute continuity alone does not ensure a finite real-valued integral. These are specification tasks as well as proof tasks.

**Textual obstacles exposed by the coverage review**

These should be resolved before making the corresponding coverage claims stronger.

- [Chapter 1 §1](../chapters/ch1/section1.tex), line 132, says the automorphism-size bound is an equality iff there are no relations. A structure with the full binary relation has every permutation as an automorphism, despite having a nonempty relation family. The correct condition is invariance of every specified relation under all permutations. This is already compatible with the formal zero-deficit theorem. The full-relation counterexample was checked separately in Lean during this audit.
- The unrefined centered stationary-point issue in finding 2 was also checked separately in Lean: `twoBlockCriticalEquations β J (1/2) (1/2) ↔ β * J = 0`.
- [Chapter 1 §3](../chapters/ch1/section3.tex), line 123, calls enlargement of a tuple set a refinement. That example happens to decrease the automorphism group, but it does not satisfy the formal theorem's inclusion of *families of relations*. Section 1.4 explains the distinction correctly. This example needs its own proof rather than an application of the refinement theorem.
- [Appendix B](../chapters/app/appendixB.tex), around lines 365–399, says a matrix with common diagonal value `p` and common off-diagonal value `q` loses block-label permutation symmetry when `p ≠ q`. Such a matrix is still fixed by every simultaneous row/column permutation. Its entry variance detects nonconstancy, not loss of that particular symmetry. The abstract `(p,q) ↦ (q,p)` action in §3.11 is a different action and should not be identified with relabeling the blocks. A concrete-action formalization would force this distinction.
- The “asymptotically equivalent” language in [§3.1](../chapters/ch3/section1.tex), line 316, needs a precise aggregated counting statement. An individual orbit deficit is at most `log(n!) = O(n log n)`, whereas a nondegenerate profile fiber can have logarithmic size of order `n²`. A fiber contains many orbits; its entropy cannot generally be identified with one orbit's deficit.

**Statement-by-statement crosswalk**

“Covered” below means a matching formal mathematical core in the represented types. The arbitrary-arity and group-action limitations above still apply where relevant. “Bridge” identifies an absent specialization, construction, or final implication; “partial” identifies missing components of the stated conclusion. This table is an audit recommendation, not an edit to the official statuses.

| Source | Numbered statement | Audit |
|---|---|---|
| 1.1:121 | Automorphism-size bound | Covered for binary relation families; uses permutation cardinality. |
| 1.2:324 | Deficit and degree-of-order bounds | Partial: upper-deficit bound and reverse extremal implications missing. |
| 1.3:38 | Automorphisms under refinement | Covered as inclusion of automorphism sets. |
| 1.3:63 | Deficit monotonicity | Covered. |
| 1.4:77 | Equivariance of relation operations | Covered. |
| 1.4:104 | Inherited automorphisms | Covered. |
| 1.4:127 | Separate-relations intersection | Covered. |
| 1.4:150 | Complement and converse | Covered. |
| 1.4:180 | Invariant operands | Covered. |
| 2.4:63 | Labeled realizations and orbit–stabilizer | Abstract theorem covered; relational action/stabilizer bridge missing. |
| 2.5:83 | Additivity under multiplicativity | Conditional scalar identity covered; no disjoint-union construction. |
| 2.5:164 | Stirling growth | Asymptotic formula covered; superlinear corollary not packaged. |
| 3.3:43 | Finite block Euler–Lagrange equations | Covered with coordinate differentiability of the energy. |
| 3.3:131 | Continuum Euler–Lagrange equation | Open; specify analytic hypotheses. |
| 3.3:238 | Homogeneous second variation | Open. |
| 3.4:119 | Two-block Euler–Lagrange equations | Covered in the interior. |
| 3.4:192 | Diagonal branch | Covered as a stationary-equation implication. |
| 3.4:258 | Unrefined Hessian and modes | Partial: operator algebra covered, derivative identification missing. |
| 3.4:324 | Unrefined critical temperature | Correct eigenvalue calculation; book's centered-solution premise needs correction. |
| 3.4:399 | Hessian stability threshold | Partial: positive-definiteness statement and derivative connection missing. |
| 3.4:559 | Refined first derivatives | Covered. |
| 3.4:599 | Refined symmetric branch | Covered. |
| 3.4:628 | Refined Hessian | Covered by actual second partial derivatives. |
| 3.4:681 | Refined eigenmodes | Covered. |
| 3.4:731 | Refined critical instability | Covered with `J > 0`. |
| 3.5:164 | Entropy derivatives | Covered through fourth order. |
| 3.5:219 | General local Landau form | Partial: only the centered slice. |
| 3.5:280 | Symmetric Landau expansion | Covered, including uniform sixth-order remainder. |
| 3.5:425 | Unique exact broken local-minimum pair | Covered on the book's explicit coupling interval. |
| 3.5:526 | Quartic local minima | Global classification covered; local classification/instability bridge missing. |
| 3.5:592 | Exact branch asymptotic | Partial: parametrized limit covered; inverse-branch limit missing. |
| 3.6:139 | Orthogonal invariance of field energy | Open. |
| 3.6:170 | Vector radial-potential minima | Scalar radius covered; vector/norm bridge missing. |
| 3.6:229 | Orthogonal breaking pattern and dimension | Open. |
| 3.6:286 | Quadratic expansion at a vacuum | Open; polynomial core is an approachable first step. |
| 3.7:169 | Relational low-energy fields | Open; specify constrained/effective model. |
| 3.8:194 | Connection and covariant comparison | Open; current ledger title targets a different claim. |
| 3.9:100 | Curvature and infinitesimal path dependence | Open. |
| 3.10:144 | Curvature-action Euler–Lagrange equation | Open. |
| 3.11:105 | Contrast and coarse deficit | Open finite proof target; incorrectly classified computational-only. |
| 4.1:93 | Functional ternary relations | Covered. |
| 4.2:42 | Operation/graph preservation equivalence | Covered for binary operations. |
| 4.2:87 | Automorphisms as table stabilizer | Definitional identity only; natural action unconstructed. |
| 4.2:111 | Added algebraic data reduce automorphisms | Covered for represented binary data. |
| 4.3:45 | Algebraic deficit bounds/equality cases | Inequalities covered; equality characterizations partial. |
| 5.2:17 | Additive integer automorphisms | Covered. |
| 5.2:28 | Integer ring rigidity | Covered. |
| 5.2:74 | Real-field rigidity | Covered. |
| 5.3:222 | Finite compatibility requirement | Covered as an assumed compatibility condition, not an extension theorem. |
| 6.1:60 | Stabilizer conjugacy | Covered. |
| 6.1:77 | Orbit invariance of reference deficit | Covered with finite-index hypotheses. |
| 6.2:39 | Fixed-reference monotonicity | Covered with finite-index hypotheses. |
| 6.3:26 | Quotient dimension | Open. |
| 6.4:13 | Haar measure and subgroup index | Open. |
| 6.4:60 | KL nonnegativity, equality, invariance | Open. |
| 6.7:56 | Positive-temperature hard-sphere condensation | Missing ledger entry; external theorem, unformalized here. |
| 6.7:90 | Number-conserving invariance | Missing ledger entry and formal definitions/proof. |

The two additional existing ledger identities are the entropy–energy partition rewrite (§2.4) and logarithmic degeneracy (§2.5). Their scalar cores are checked; the model connections are described in finding 6.

**Suggested order of work**

1. Correct the ledger inventory and obsolete target, split “full statement,” “restricted/core result,” “compatibility condition,” “external theorem,” and “numerical evidence,” and fix the textual obstacles above. Avoid publishing a revised completion percentage until these criteria are agreed.
2. Close the small finite gaps: equality cases, the swap-action diagnostic, normalization/positivity, and concrete automorphism examples. Add the unrefined derivative/positivity results and scalar-to-vector/local-minimum bridges.
3. Finish the inverse-branch asymptotic and the general-`m` Landau expansion.
4. Build a common signature/action/stabilizer layer, then connect orbit counting, relational Gibbs ensembles, profile fibers, and coarse partition sums. This supplies the missing connection between the finite and mean-field theories.
5. Add manageable continuous targets: finite-orbit KL compatibility, Haar/index, KL invariance, the polynomial Goldstone expansion, then field functionals and quotient geometry. Treat the Bose operator lemma separately from the much larger external condensation theorem.

For future regression checks, scan the actual `main.tex` input tree for stable statement labels, require an explicit ledger disposition, resolve stored Lean names against the imported environment, and audit axioms. Existence checks will not establish semantic equivalence; a written record of hypotheses, scope, and missing conclusions is still needed.

The slide review found the same 57/43 totals and computational-only classification in [the formalization slide](../slides/sections/06_algebra_infinite_formal.tex), plus the corresponding dependency in [SOURCE_MAP.md](../slides/SOURCE_MAP.md). The source map says the remaining Chapter 6 statements are indexed, which is inaccurate for §6.7. When the official statuses or mathematical text are corrected, update Appendix D, `lean/README.md`, the affected slides and source map together, then run `make -C slides refresh-snapshot` and `make -C slides`. This review-only report does not change those sources or refresh their snapshot.
