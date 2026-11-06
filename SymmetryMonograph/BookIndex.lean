import SymmetryMonograph.Chapter3Landau
import SymmetryMonograph.Chapter3Completion
import SymmetryMonograph.GeneralLandau
import SymmetryMonograph.FieldEnergy
import SymmetryMonograph.TwoBlockSymmetry
import SymmetryMonograph.FiniteProfiles
import SymmetryMonograph.Relabeling
import SymmetryMonograph.Chapter4
import SymmetryMonograph.Chapter5
import SymmetryMonograph.Chapter6
import SymmetryMonograph.Chapter6Measure
import SymmetryMonograph.Chapter6Operators

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Checked monograph coverage ledger

`scripts/check_lean_coverage.py` checks the numbered LaTeX inventory, resolves
every mapped declaration, audits project theorem axioms, and verifies generated
tables. A status describes the stated scope, not every claim in a chapter.
Unnumbered analytic, computational, and research claims are tracked separately.
-/

namespace SymmetryMonograph.BookIndex

inductive FormalizationStatus where
  | complete
  | partiallyComplete
  | formalizableNow
  | needsDefinitions
  | analyticHeavy
  | computationalOnly
  | externallyCited
  | compatibilityCondition
  | researchProgram
deriving DecidableEq, Repr

structure BookStatement where
  kind : String
  source : String
  labelOrTitle : String
  bookLabel : String := ""
  category : String := "numbered"
  scope : String := ""
  leanNames : List String
  status : FormalizationStatus
deriving Repr

def statements : List BookStatement := [
  {
    kind := "lemma",
    source := "chapters/ch1/section1.tex",
    labelOrTitle := "lem:aut-size-bound",
    bookLabel := "lem:aut-size-bound",
    scope := "Finite underlying type. Relabeling.lean additionally treats indexed relations of arbitrary arity.",
    leanNames := ["SymmetryMonograph.aut_size_bound"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch1/section2.tex",
    labelOrTitle := "thm:symmetry-deficit-basic-bounds",
    bookLabel := "thm:symmetry-deficit-basic-bounds",
    scope := "Deficit and degree-of-order bounds and extremal equality cases, including arbitrary indexed relation arities.",
    leanNames := ["SymmetryMonograph.symmetryDeficit_nonneg", "SymmetryMonograph.symmetryDeficit_eq_zero_iff_autSet_eq_univ", "SymmetryMonograph.rigid_symmetryDeficit_eq_log_perm_card", "SymmetryMonograph.degreeOfOrder_nonneg", "SymmetryMonograph.degreeOfOrder_le_perm_card_sub_one", "SymmetryMonograph.rigid_degreeOfOrder_eq_perm_card_sub_one", "SymmetryMonograph.symmetryDeficit_le_log_perm_card", "SymmetryMonograph.symmetryDeficit_eq_max_iff_rigid", "SymmetryMonograph.degreeOfOrder_eq_max_iff_rigid", "SymmetryMonograph.RelationalModel.symmetryDeficit_bounds", "SymmetryMonograph.RelationalModel.symmetryDeficit_eq_zero_iff", "SymmetryMonograph.RelationalModel.symmetryDeficit_eq_max_iff", "SymmetryMonograph.RelationalModel.degreeOfOrder_bounds", "SymmetryMonograph.RelationalModel.degreeOfOrder_eq_max_iff"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch1/section3.tex",
    labelOrTitle := "automorphism group under refinement",
    bookLabel := "lean:automorphism-group-under-refinement",
    scope := "Adding named relations, represented by forgetting symbols in the reverse direction; not inclusion of tuples inside one relation.",
    leanNames := ["SymmetryMonograph.refinement_aut_subset", "SymmetryMonograph.refinement_aut_card_le", "SymmetryMonograph.RelationalModel.aut_le_restrict"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch1/section3.tex",
    labelOrTitle := "symmetry deficit monotonicity under refinement",
    bookLabel := "lean:symmetry-deficit-monotonicity-under-refinement",
    leanNames := ["SymmetryMonograph.refinement_symmetryDeficit_le"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch1/section4.tex",
    labelOrTitle := "lem:relation-ops-equivariant",
    bookLabel := "lem:relation-ops-equivariant",
    leanNames := ["SymmetryMonograph.relMap_union", "SymmetryMonograph.relMap_inter", "SymmetryMonograph.relMap_diff", "SymmetryMonograph.relMap_comp"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch1/section4.tex",
    labelOrTitle := "lem:aut-inherited-by-ops",
    bookLabel := "lem:aut-inherited-by-ops",
    leanNames := ["SymmetryMonograph.preserves_union", "SymmetryMonograph.preserves_inter", "SymmetryMonograph.preserves_diff", "SymmetryMonograph.preserves_comp"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch1/section4.tex",
    labelOrTitle := "prop:separate-relations-intersection",
    bookLabel := "prop:separate-relations-intersection",
    leanNames := ["SymmetryMonograph.pair_autSet_eq_inter"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch1/section4.tex",
    labelOrTitle := "Complement and converse preserve symmetry deficit",
    bookLabel := "lean:complement-and-converse-preserve-symmetry-deficit",
    leanNames := ["SymmetryMonograph.preserves_compl_iff", "SymmetryMonograph.preserves_conv_iff", "SymmetryMonograph.single_autSet_compl_eq", "SymmetryMonograph.single_autSet_conv_eq", "SymmetryMonograph.symmetryDeficit_compl_eq", "SymmetryMonograph.symmetryDeficit_conv_eq"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch1/section4.tex",
    labelOrTitle := "prop:invariant-operand-bounds",
    bookLabel := "prop:invariant-operand-bounds",
    leanNames := ["SymmetryMonograph.invariant_operand_union_aut_subset", "SymmetryMonograph.invariant_operand_inter_aut_subset", "SymmetryMonograph.invariant_operand_diff_aut_subset", "SymmetryMonograph.invariant_operand_union_symmetryDeficit_le", "SymmetryMonograph.invariant_operand_inter_symmetryDeficit_le", "SymmetryMonograph.invariant_operand_diff_symmetryDeficit_le"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch2/section4.tex",
    labelOrTitle := "lem:labeled-realizations-orbit-stabilizer",
    bookLabel := "lem:labeled-realizations-orbit-stabilizer",
    scope := "Actual relabeling action, automorphism subgroup, and isomorphism-class fiber.",
    leanNames := ["SymmetryMonograph.Chapter2.orbit_card_mul_stabilizer_card", "SymmetryMonograph.Chapter2.orbit_card_eq_group_card_div_stabilizer_card", "SymmetryMonograph.RelationalModel.symmetryDeficit_eq_log_orbit", "SymmetryMonograph.RelationalModel.class_fiber_card", "SymmetryMonograph.RelStructure.autSet_eq_model_aut"],
    status := .complete
  },
  {
    kind := "identity",
    source := "chapters/ch2/section4.tex",
    labelOrTitle := "entropy-energy form of relational partition function",
    category := "identity",
    scope := "Finite fixed signature and finite underlying type; energy is constant on isomorphism classes.",
    leanNames := ["SymmetryMonograph.Chapter2.partition_entropy_energy_form", "SymmetryMonograph.RelationalModel.labeled_partition_eq_class_partition"],
    status := .complete
  },
  {
    kind := "identity",
    source := "chapters/ch2/section5.tex",
    labelOrTitle := "symmetry deficit as logarithmic degeneracy",
    category := "identity",
    scope := "Instantiated at the relabeling orbit of a binary structure; also proved for arbitrary indexed arities.",
    leanNames := ["SymmetryMonograph.Chapter2.symmetry_deficit_eq_log_degeneracy", "SymmetryMonograph.symmetryDeficit_eq_log_orbit"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch2/section5.tex",
    labelOrTitle := "lem:symmetry-entropy-additive-under-multiplicativity",
    bookLabel := "lem:symmetry-entropy-additive-under-multiplicativity",
    scope := "Conditional on multiplicative degeneracy; does not assert multiplicativity for unrestricted disjoint unions.",
    leanNames := ["SymmetryMonograph.Chapter2.entropy_additive_of_degeneracy_multiplicative"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch2/section5.tex",
    labelOrTitle := "prop:stirling-maximal-symmetry-deficit-growth",
    bookLabel := "prop:stirling-maximal-symmetry-deficit-growth",
    leanNames := ["SymmetryMonograph.Chapter2.log_factorial_stirling_bigO", "SymmetryMonograph.Chapter2.log_factorial_stirling_remainder_eventually"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section3.tex",
    labelOrTitle := "k-block Euler--Lagrange equations",
    bookLabel := "lean:k-block-euler-lagrange-equations",
    scope := "Interior densities and a coordinate derivative hypothesis on the supplied energy functional.",
    leanNames := ["SymmetryMonograph.Chapter3.hasDerivAt_binaryEntropy_of_interior", "SymmetryMonograph.Chapter3.kBlockEulerLagrange_of_coordCritical", "SymmetryMonograph.Chapter3.kBlockEulerLagrange_of_interior_coordCritical"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section3.tex",
    labelOrTitle := "continuum Euler--Lagrange equation",
    bookLabel := "lean:continuum-euler-lagrange-equation",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section3.tex",
    labelOrTitle := "second variation of homogeneous phase",
    bookLabel := "lean:second-variation-of-homogeneous-phase",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "two-block Euler--Lagrange equations",
    bookLabel := "lean:two-block-euler-lagrange-equations",
    leanNames := ["SymmetryMonograph.Chapter3.hasPartialP_twoBlockFreeEnergy", "SymmetryMonograph.Chapter3.hasPartialQ_twoBlockFreeEnergy", "SymmetryMonograph.Chapter3.twoBlock_eulerLagrange_of_critical", "SymmetryMonograph.Chapter3.twoBlock_criticalEquations_iff_neg_logOdds"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "diagonal branch of two-block system",
    bookLabel := "lean:diagonal-branch-of-two-block-system",
    leanNames := ["SymmetryMonograph.Chapter3.twoBlock_diagonal_branch"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "two-block Hessian and modes",
    bookLabel := "lean:two-block-hessian-and-modes",
    scope := "Second partial derivatives and the resulting operator/eigenmode identities on the interior.",
    leanNames := ["SymmetryMonograph.Chapter3.twoBlockHessian", "SymmetryMonograph.Chapter3.twoBlock_hessian_at_symmetric_point_eq", "SymmetryMonograph.Chapter3.twoBlock_hessian_symmetric_mode", "SymmetryMonograph.Chapter3.twoBlock_hessian_antisymmetric_mode", "SymmetryMonograph.Chapter3.twoBlockHessian_is_gradient_jacobian"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "unrefined curvature threshold at the half point",
    bookLabel := "lean:unrefined-curvature-threshold-at-the-half-point",
    scope := "Curvature changes at beta J = 4. The half point is stationary only when beta J = 0.",
    leanNames := ["SymmetryMonograph.Chapter3.twoBlock_unstable_iff", "SymmetryMonograph.Chapter3.twoBlock_critical_threshold_at_half", "SymmetryMonograph.Chapter3.twoBlock_centered_critical_iff"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "thm:two-block-hessian-stability",
    bookLabel := "thm:two-block-hessian-stability",
    scope := "Positive definiteness below the threshold and a negative direction above it; no equilibrium assertion.",
    leanNames := ["SymmetryMonograph.Chapter3.twoBlock_unstable_iff", "SymmetryMonograph.Chapter3.twoBlock_critical_threshold_at_half", "SymmetryMonograph.Chapter3.twoBlock_hessian_posDef_at_half", "SymmetryMonograph.Chapter3.twoBlock_hessian_negative_antisymmetric_at_half"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "refined two-block first derivatives",
    bookLabel := "lean:refined-two-block-first-derivatives",
    leanNames := ["SymmetryMonograph.Chapter3.hasPartialP_refinedTwoBlockFreeEnergy", "SymmetryMonograph.Chapter3.hasPartialQ_refinedTwoBlockFreeEnergy", "SymmetryMonograph.Chapter3.refined_first_derivatives"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "refined two-block symmetric branch",
    bookLabel := "lean:refined-two-block-symmetric-branch",
    leanNames := ["SymmetryMonograph.Chapter3.log_odds_eq_zero_iff_eq_half", "SymmetryMonograph.Chapter3.refined_symmetric_branch_iff"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "refined two-block Hessian",
    bookLabel := "lean:refined-two-block-hessian",
    leanNames := ["SymmetryMonograph.Chapter3.refinedHessian", "SymmetryMonograph.Chapter3.refinedHessian_at_half_eq", "SymmetryMonograph.Chapter3.refinedHessian_is_gradient_jacobian"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "refined two-block Hessian eigenmodes",
    bookLabel := "lean:refined-two-block-hessian-eigenmodes",
    leanNames := ["SymmetryMonograph.Chapter3.refined_hessian_symmetric_mode", "SymmetryMonograph.Chapter3.refined_hessian_antisymmetric_mode"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section4.tex",
    labelOrTitle := "refined two-block critical instability",
    bookLabel := "lean:refined-two-block-critical-instability",
    leanNames := ["SymmetryMonograph.Chapter3.refined_antisymmetric_mode_unstable_iff"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch3/section5.tex",
    labelOrTitle := "lem:binary-entropy-derivatives",
    bookLabel := "lem:binary-entropy-derivatives",
    leanNames := ["SymmetryMonograph.Chapter3.hasDerivAt_logOdds_of_interior", "SymmetryMonograph.Chapter3.hasDerivAt_logOdds_binaryEntropySecondFormula", "SymmetryMonograph.Chapter3.hasDerivAt_binaryEntropySecondFormula", "SymmetryMonograph.Chapter3.hasDerivAt_binaryEntropyThirdFormula", "SymmetryMonograph.Chapter3.binaryEntropy_successive_derivatives_through_four", "SymmetryMonograph.Chapter3.binaryEntropy_derivative_formulas_at_half"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section5.tex",
    labelOrTitle := "prop:landau-local-form",
    bookLabel := "prop:landau-local-form",
    scope := "Every fixed interior mean 0 < m < 1; exact displayed coefficients and O(d^6) remainder.",
    leanNames := ["SymmetryMonograph.Chapter3.symmetricContrastFreeEnergy_eq_refined", "SymmetryMonograph.Chapter3.hasDerivAt_symmetricContrastFreeEnergy", "SymmetryMonograph.Chapter3.hasDerivAt_symmetricContrastFirst", "SymmetryMonograph.Chapter3.hasDerivAt_symmetricContrastSecond", "SymmetryMonograph.Chapter3.hasDerivAt_symmetricContrastThird", "SymmetryMonograph.Chapter3.contrastLandauRemainder_isBigO"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section5.tex",
    labelOrTitle := "thm:landau-expansion-symmetric",
    bookLabel := "thm:landau-expansion-symmetric",
    leanNames := ["SymmetryMonograph.Chapter3.symmetricContrastLandauJet", "SymmetryMonograph.Chapter3.symmetricContrast_landau_jet", "SymmetryMonograph.Chapter3.symmetricContrastLandauJet_eq", "SymmetryMonograph.Chapter3.abs_symmetricContrastLandauRemainderFirst_le", "SymmetryMonograph.Chapter3.abs_symmetricContrastLandauRemainder_le", "SymmetryMonograph.Chapter3.abs_symmetricContrastLandauRemainder_le_on", "SymmetryMonograph.Chapter3.symmetricContrastLandauRemainder_isBigO"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section5.tex",
    labelOrTitle := "thm:landau-quartic-minimizers",
    bookLabel := "thm:landau-quartic-minimizers",
    scope := "Global and local minima of the quartic truncation for positive quartic coefficient.",
    leanNames := ["SymmetryMonograph.Chapter3.quartic_unique_min_of_quadratic_pos", "SymmetryMonograph.Chapter3.quartic_global_min_iff_sq_eq_of_quadratic_neg", "SymmetryMonograph.Chapter3.quartic_localMin_iff_of_pos", "SymmetryMonograph.Chapter3.quartic_localMin_iff_of_neg", "SymmetryMonograph.Chapter3.quartic_zero_not_localMin", "SymmetryMonograph.Chapter3.quartic_zero_isLocalMax"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section5.tex",
    labelOrTitle := "thm:exact-broken-stationary-pair",
    bookLabel := "thm:exact-broken-stationary-pair",
    leanNames := ["SymmetryMonograph.Chapter3.refinedStationary_symmetricContrast_iff", "SymmetryMonograph.Chapter3.exactContrastCoupling_strictMonoOn", "SymmetryMonograph.Chapter3.refinedStationary_sum_eq_one", "SymmetryMonograph.Chapter3.refinedTwoBlockFreeEnergy_isLocalMin_at_positive_root", "SymmetryMonograph.Chapter3.refinedTwoBlockFreeEnergy_isLocalMin_at_negative_root", "SymmetryMonograph.Chapter3.exists_unique_exact_broken_local_min_pair"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section5.tex",
    labelOrTitle := "thm:exact-broken-branch-asymptotic",
    bookLabel := "thm:exact-broken-branch-asymptotic",
    scope := "The inverse branch d_ex(K) is constructed, tends to zero, and satisfies the stated K-limit.",
    leanNames := ["SymmetryMonograph.Chapter3.abs_exactContrastCoupling_normalized_sub_le", "SymmetryMonograph.Chapter3.tendsto_exactContrastCoupling", "SymmetryMonograph.Chapter3.tendsto_exactContrast_sq_div_coupling_sub_two", "SymmetryMonograph.Chapter3.exactBrokenContrast_spec", "SymmetryMonograph.Chapter3.tendsto_exactBrokenContrast", "SymmetryMonograph.Chapter3.tendsto_exactBrokenContrast_sq_div_sub_two"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch3/section6.tex",
    labelOrTitle := "O(m)-invariance of continuum functional",
    bookLabel := "lean:o-m-invariance-of-continuum-functional",
    scope := "Interval-integral field energy, differentiable real-normed-space fields, and linear isometry equivalences.",
    leanNames := ["SymmetryMonograph.Chapter3.fieldEnergy_orthogonal_invariant"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section6.tex",
    labelOrTitle := "minima of radial quartic potential",
    bookLabel := "lean:minima-of-radial-quartic-potential",
    scope := "Vector minima in a nontrivial real normed space; positive radius is realized.",
    leanNames := ["SymmetryMonograph.Chapter3.radial_quartic_unique_min_of_quadratic_pos", "SymmetryMonograph.Chapter3.radial_quartic_global_min_iff_sq_eq_of_quadratic_neg", "SymmetryMonograph.Chapter3.radial_vector_min_iff_zero", "SymmetryMonograph.Chapter3.radial_vector_min_iff_norm"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch3/section6.tex",
    labelOrTitle := "O(m) to O(m-1) breaking pattern",
    bookLabel := "lean:o-m-to-o-m-1-breaking-pattern",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section6.tex",
    labelOrTitle := "quadratic expansion around chosen vacuum",
    bookLabel := "lean:quadratic-expansion-around-chosen-vacuum",
    scope := "Exact potential polynomial, including cubic and quartic terms; field decomposition and integrated remainder remain open.",
    leanNames := ["SymmetryMonograph.Chapter3.radial_quartic_vacuum_expansion"],
    status := .partiallyComplete
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section7.tex",
    labelOrTitle := "Relational Low-Energy Fields",
    bookLabel := "lean:relational-low-energy-fields",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section8.tex",
    labelOrTitle := "connection supplies covariant infinitesimal comparison",
    bookLabel := "lean:connection-supplies-covariant-infinitesimal-comparison",
    scope := "The present prose statement is conceptual; a precise bundle, gauge transformation, and covariance theorem remain to be specified.",
    leanNames := [],
    status := .needsDefinitions
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section9.tex",
    labelOrTitle := "curvature obstructs path independence",
    bookLabel := "lean:curvature-obstructs-path-independence",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section10.tex",
    labelOrTitle := "Euler--Lagrange equations from curvature action",
    bookLabel := "lean:euler-lagrange-equations-from-curvature-action",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "proposition",
    source := "chapters/ch3/section11.tex",
    labelOrTitle := "order parameter and coarse symmetry deficit",
    bookLabel := "lean:order-parameter-and-coarse-symmetry-deficit",
    scope := "Exact two-slot parameter-exchange action; this is not relabeling the two blocks of a diagonal/off-diagonal density matrix.",
    leanNames := ["SymmetryMonograph.Chapter3.parameterStabilizer_eq_top", "SymmetryMonograph.Chapter3.parameterStabilizer_eq_bot", "SymmetryMonograph.Chapter3.coarseSymmetryDeficit_eq_zero_iff", "SymmetryMonograph.Chapter3.coarseSymmetryDeficit_eq_log_two_iff"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch4/section1.tex",
    labelOrTitle := "operations are functional ternary relations",
    bookLabel := "lean:operations-are-functional-ternary-relations",
    leanNames := ["SymmetryMonograph.Chapter4.opGraph_functional", "SymmetryMonograph.Chapter4.functional_iff_exists_opGraph"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch4/section2.tex",
    labelOrTitle := "operation preservation iff graph preservation",
    bookLabel := "lean:operation-preservation-iff-graph-preservation",
    leanNames := ["SymmetryMonograph.Chapter4.preservesOperation_iff_preserves_opGraph", "SymmetryMonograph.RelationalModel.operationModel_aut_iff"],
    status := .complete
  },
  {
    kind := "lemma",
    source := "chapters/ch4/section2.tex",
    labelOrTitle := "automorphism group as operation-table stabilizer",
    bookLabel := "lean:automorphism-group-as-operation-table-stabilizer",
    scope := "A genuine relabeling action on indexed binary relations and ternary operation graphs.",
    leanNames := ["SymmetryMonograph.Chapter4.alg_autSet_eq_stabilizer", "SymmetryMonograph.Chapter4.AlgRelStructure.autSet_eq_model_aut"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch4/section2.tex",
    labelOrTitle := "automorphisms decrease under added algebraic data",
    bookLabel := "lean:automorphisms-decrease-under-added-algebraic-data",
    leanNames := ["SymmetryMonograph.Chapter4.alg_refinement_aut_subset", "SymmetryMonograph.Chapter4.alg_refinement_aut_card_le"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch4/section3.tex",
    labelOrTitle := "algebraic symmetry-deficit bounds",
    bookLabel := "lean:algebraic-symmetry-deficit-bounds",
    scope := "Both extremal equality characterizations for the represented binary algebraic data.",
    leanNames := ["SymmetryMonograph.Chapter4.alg_symmetryDeficit_nonneg", "SymmetryMonograph.Chapter4.alg_symmetryDeficit_le_log_perm_card", "SymmetryMonograph.Chapter4.alg_rigid_symmetryDeficit_eq_log_perm_card", "SymmetryMonograph.Chapter4.alg_symmetryDeficit_eq_zero_iff_autSet_eq_univ", "SymmetryMonograph.Chapter4.alg_symmetryDeficit_eq_max_iff_rigid"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch5/section2.tex",
    labelOrTitle := "automorphism group of (Z,+) has order 2",
    bookLabel := "lean:automorphism-group-of-z-has-order-2",
    leanNames := ["SymmetryMonograph.Chapter5.int_additive_automorphism_card"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch5/section2.tex",
    labelOrTitle := "unital ring of integers is rigid",
    bookLabel := "lean:unital-ring-of-integers-is-rigid",
    leanNames := ["SymmetryMonograph.Chapter5.int_ring_automorphism_subsingleton", "SymmetryMonograph.Chapter5.int_ring_automorphism_eq_refl"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch5/section2.tex",
    labelOrTitle := "prop:real-field-automorphisms-trivial",
    bookLabel := "prop:real-field-automorphisms-trivial",
    leanNames := ["SymmetryMonograph.Chapter5.real_ring_automorphism_monotone", "SymmetryMonograph.Chapter5.real_field_automorphism_eq_refl", "SymmetryMonograph.Chapter5.real_field_automorphism_subsingleton"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch5/section3.tex",
    labelOrTitle := "finite compatibility of infinite symmetry-deficit invariants",
    bookLabel := "lean:finite-compatibility-of-infinite-symmetry-deficit-invariants",
    scope := "Applies the finite compatibility assumption; no infinite invariant is constructed.",
    leanNames := ["SymmetryMonograph.Chapter5.finite_extension_agrees_with_cardinality_formula"],
    status := .compatibilityCondition
  },
  {
    kind := "lemma",
    source := "chapters/ch6/section1.tex",
    labelOrTitle := "lem:reference-stabilizer-conjugate",
    bookLabel := "lem:reference-stabilizer-conjugate",
    leanNames := ["SymmetryMonograph.Chapter6.reference_stabilizer_conjugate"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch6/section1.tex",
    labelOrTitle := "reference-group deficit is constant on G-orbits",
    bookLabel := "lean:reference-group-deficit-is-constant-on-g-orbits",
    leanNames := ["SymmetryMonograph.Chapter6.residualSymmetry_index_smul", "SymmetryMonograph.Chapter6.residualSymmetry_finiteIndex_smul", "SymmetryMonograph.Chapter6.referenceGroupDeficit_orbit_invariant"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch6/section2.tex",
    labelOrTitle := "Monotonicity at fixed reference group",
    bookLabel := "lean:monotonicity-at-fixed-reference-group",
    leanNames := ["SymmetryMonograph.Chapter6.referenceSubgroupDeficit_antitone", "SymmetryMonograph.Chapter6.referenceGroupDeficit_mono_of_residualSymmetry_le"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch6/section3.tex",
    labelOrTitle := "dimension of the homogeneous-space quotient",
    bookLabel := "lean:dimension-of-the-homogeneous-space-quotient",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "proposition",
    source := "chapters/ch6/section4.tex",
    labelOrTitle := "prop:haar-subgroup-index",
    bookLabel := "prop:haar-subgroup-index",
    scope := "Measurable subgroups and normalized left-invariant probability; applies in particular to closed subgroups with normalized Haar measure.",
    leanNames := ["SymmetryMonograph.Chapter6.subgroup_measure_pos_iff_finiteIndex", "SymmetryMonograph.Chapter6.subgroup_measure_eq_inv_index"],
    status := .complete
  },
  {
    kind := "proposition",
    source := "chapters/ch6/section4.tex",
    labelOrTitle := "nonnegativity and invariance of measure symmetry deficit",
    bookLabel := "lean:nonnegativity-and-invariance-of-measure-symmetry-deficit",
    scope := "Probability measures, absolute continuity and integrable log density for the real integral; action by measurable equivalences preserving the reference measure.",
    leanNames := ["SymmetryMonograph.Chapter6.measureDeficit_integral_nonneg", "SymmetryMonograph.Chapter6.measureDeficit_integral_eq_zero_iff", "SymmetryMonograph.Chapter6.measureSymmetryDeficit_invariant"],
    status := .complete
  },
  {
    kind := "theorem",
    source := "chapters/ch6/section7.tex",
    labelOrTitle := "thm:openai-hard-sphere-bec",
    bookLabel := "thm:openai-hard-sphere-bec",
    scope := "Reported external preprint theorem; source statement checked, full proof not independently verified here; not formalized or assumed as a Lean axiom.",
    leanNames := [],
    status := .externallyCited
  },
  {
    kind := "lemma",
    source := "chapters/ch6/section7.tex",
    labelOrTitle := "number-conserving invariance",
    bookLabel := "lean:number-conserving-invariance",
    scope := "Every bounded operator on a complex Hilbert space is fixed by scalar-unitary conjugation, covering both fixed-N and one-particle operators. No condensation or partial-trace construction is asserted.",
    leanNames := ["SymmetryMonograph.Chapter6.scalar_unitary_conjugation", "SymmetryMonograph.Chapter6.number_conserving_invariance"],
    status := .complete
  },
  {
    kind := "supplement",
    source := "chapters/ch2/section3.tex",
    labelOrTitle := "positive relational Gibbs weights",
    category := "supplement",
    scope := "Positive multiplicities and a nonempty finite ensemble imply normalization and positivity. Normalized deficit lies in [0,1] when the permutation count exceeds one; expectations and examples remain separate targets.",
    leanNames := ["SymmetryMonograph.Chapter2.partitionMultiplicity_pos", "SymmetryMonograph.Chapter2.gibbsWeight_pos", "SymmetryMonograph.Chapter2.gibbs_weights_sum_one", "SymmetryMonograph.RelationalModel.normalizedSymmetryDeficit_bounds"],
    status := .complete
  },
  {
    kind := "supplement",
    source := "chapters/ch3/section1.tex",
    labelOrTitle := "exact block-profile fiber count",
    category := "supplement",
    scope := "Independent directed relation positions, represented as disjoint block coordinates; product of binomial coefficients.",
    leanNames := ["SymmetryMonograph.Chapter3.blockProfile_fiber_card", "SymmetryMonograph.Chapter3.directed_block_positions_card"],
    status := .complete
  },
  {
    kind := "supplement",
    source := "chapters/ch3/section1.tex",
    labelOrTitle := "partition regrouping by profiles",
    category := "supplement",
    scope := "Exact finite fiber identity. Entropy and large-system approximations do not follow from this identity alone.",
    leanNames := ["SymmetryMonograph.Chapter2.partition_regroup_by_fibers"],
    status := .complete
  },
  {
    kind := "supplement",
    source := "chapters/ch1/section2.tex",
    labelOrTitle := "finite examples and 512-relation enumeration",
    category := "supplement",
    scope := "Distinguished-point, arrow and cycle examples and the 104-class histogram require dedicated certified finite computations.",
    leanNames := [],
    status := .formalizableNow
  },
  {
    kind := "supplement",
    source := "chapters/ch3/section2.tex",
    labelOrTitle := "profile entropy and continuum limit",
    category := "supplement",
    scope := "Binomial entropy asymptotics, profile error estimates, a Laplace principle and step-kernel convergence remain open.",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "supplement",
    source := "chapters/ch5/section2.tex",
    labelOrTitle := "additional infinite algebraic examples",
    category := "supplement",
    scope := "Examples beyond the proved integer and real-field cases need separate representations and automorphism proofs.",
    leanNames := [],
    status := .needsDefinitions
  },
  {
    kind := "supplement",
    source := "chapters/ch6/section5.tex",
    labelOrTitle := "von Mises and Bessel analysis",
    category := "supplement",
    scope := "Normalization, self-consistency, threshold, KL formula and critical asymptotics are analytic proof targets distinct from simulation evidence.",
    leanNames := [],
    status := .analyticHeavy
  },
  {
    kind := "supplement",
    source := "chapters/ch6/section5.tex",
    labelOrTitle := "finite-system numerical comparisons",
    category := "supplement",
    scope := "Monte Carlo measurements and fitted errors are computational evidence; the analytic formulas are tracked separately.",
    leanNames := [],
    status := .computationalOnly
  },
  {
    kind := "supplement",
    source := "chapters/app/appendixB.tex",
    labelOrTitle := "structural susceptibility and scaling proposals",
    category := "supplement",
    scope := "Proposed diagnostics and universality comparisons are research hypotheses, not established formal theorems.",
    leanNames := [],
    status := .researchProgram
  }
]

end SymmetryMonograph.BookIndex
