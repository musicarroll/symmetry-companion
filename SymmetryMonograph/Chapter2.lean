import SymmetryMonograph.FiniteRelationalStructures
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling

set_option linter.style.header false

/-!
# Chapter 2: finite relational ensembles

Formal counterparts for the exact finite-sum and orbit-counting statements in
Chapter 2.  Analytic asymptotics, such as the Stirling estimate, are left
indexed in `BookIndex.lean`.
-/

namespace SymmetryMonograph.Chapter2

open scoped BigOperators
open Filter Asymptotics

noncomputable section

variable {ι G Ω : Type*}

def partitionMultiplicity [Fintype ι]
    (multiplicity energy : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ S, multiplicity S * Real.exp (-β * energy S)

def partitionEntropy [Fintype ι]
    (symmetryDeficit energy : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ S, Real.exp (symmetryDeficit S - β * energy S)

def gibbsWeight [Fintype ι]
    (multiplicity energy : ι → ℝ) (β : ℝ) (S : ι) : ℝ :=
  multiplicity S * Real.exp (-β * energy S) /
    partitionMultiplicity multiplicity energy β

theorem partitionMultiplicity_pos [Fintype ι] [Nonempty ι]
    (multiplicity energy : ι → ℝ) (β : ℝ) (hm : ∀ S, 0 < multiplicity S) :
    0 < partitionMultiplicity multiplicity energy β := by
  exact Finset.sum_pos (fun S _ => mul_pos (hm S) (Real.exp_pos _)) Finset.univ_nonempty

theorem gibbsWeight_pos [Fintype ι] [Nonempty ι]
    (multiplicity energy : ι → ℝ) (β : ℝ) (hm : ∀ S, 0 < multiplicity S) (S : ι) :
    0 < gibbsWeight multiplicity energy β S :=
  div_pos (mul_pos (hm S) (Real.exp_pos _))
    (partitionMultiplicity_pos multiplicity energy β hm)

/-- Exact regrouping by any finite profile map, including an orbit-quotient map.
No large-system or Laplace approximation enters this identity. -/
theorem partition_regroup_by_fibers {P : Type*} [Fintype ι] [Fintype P]
    (profile : ι → P) (energy : P → ℝ) (β : ℝ) :
    (∑ x, Real.exp (-β * energy (profile x))) =
      ∑ p, (Nat.card {x // profile x = p} : ℝ) * Real.exp (-β * energy p) := by
  classical
  rw [← Fintype.sum_fiberwise' profile (fun p => Real.exp (-β * energy p))]
  simp [Nat.card_eq_fintype_card]

theorem partition_entropy_energy_form [Fintype ι]
    (multiplicity symmetryDeficit energy : ι → ℝ) (β : ℝ)
    (h : ∀ S, multiplicity S = Real.exp (symmetryDeficit S)) :
    partitionMultiplicity multiplicity energy β =
      partitionEntropy symmetryDeficit energy β := by
  unfold partitionMultiplicity partitionEntropy
  refine Finset.sum_congr rfl ?_
  intro S _hS
  rw [h S, ← Real.exp_add]
  congr 1
  ring

theorem gibbs_weights_sum_one [Fintype ι]
    (multiplicity energy : ι → ℝ) (β : ℝ)
    (hZ : partitionMultiplicity multiplicity energy β ≠ 0) :
    ∑ S, gibbsWeight multiplicity energy β S = 1 := by
  calc
    ∑ S, gibbsWeight multiplicity energy β S
        = (∑ S, multiplicity S * Real.exp (-β * energy S)) /
            partitionMultiplicity multiplicity energy β := by
          simp [gibbsWeight, Finset.sum_div]
    _ = partitionMultiplicity multiplicity energy β /
            partitionMultiplicity multiplicity energy β := by
          rfl
    _ = 1 := div_self hZ

theorem orbit_card_mul_stabilizer_card [Group G] [MulAction G Ω]
    [Fintype G] (S : Ω) [Fintype (MulAction.orbit G S)]
    [Fintype (MulAction.stabilizer G S)] :
    Fintype.card (MulAction.orbit G S) *
      Fintype.card (MulAction.stabilizer G S) =
        Fintype.card G := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) (X := Ω) S

theorem orbit_card_eq_group_card_div_stabilizer_card [Group G] [MulAction G Ω]
    [Fintype G] (S : Ω) [Fintype (MulAction.orbit G S)]
    [Fintype (MulAction.stabilizer G S)]
    (hstab : Fintype.card (MulAction.stabilizer G S) ≠ 0) :
    Fintype.card (MulAction.orbit G S) =
      Fintype.card G / Fintype.card (MulAction.stabilizer G S) := by
  apply Nat.eq_div_of_mul_eq_right hstab
  rw [mul_comm]
  exact orbit_card_mul_stabilizer_card (G := G) (Ω := Ω) S

def degeneracy (fullSymmetry automorphisms : ℝ) : ℝ :=
  fullSymmetry / automorphisms

def symmetryDeficitFromDegeneracy (g : ℝ) : ℝ :=
  Real.log g

theorem symmetry_deficit_eq_log_degeneracy (g : ℝ) :
    symmetryDeficitFromDegeneracy g = Real.log g := rfl

theorem entropy_additive_of_degeneracy_multiplicative
    {g₁ g₂ g₁₂ I₁ I₂ I₁₂ : ℝ}
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂)
    (hI₁ : I₁ = Real.log g₁)
    (hI₂ : I₂ = Real.log g₂)
    (hI₁₂ : I₁₂ = Real.log g₁₂)
    (hmul : g₁₂ = g₁ * g₂) :
    I₁₂ = I₁ + I₂ := by
  rw [hI₁₂, hmul, Real.log_mul hg₁.ne' hg₂.ne', hI₁, hI₂]

def logFactorialMainTerm (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log n - n

def logFactorialStirlingRemainder (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n)

theorem log_factorial_stirling_remainder_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n.factorial : ℝ) =
        logFactorialMainTerm n + logFactorialStirlingRemainder n := by
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  have hformula := Stirling.log_stirlingSeq_formula n
  have hlog_div : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
    rw [Real.log_div, Real.log_exp]
    · exact Nat.cast_ne_zero.mpr hn
    · exact Real.exp_ne_zero 1
  rw [hlog_div] at hformula
  rw [logFactorialMainTerm, logFactorialStirlingRemainder]
  calc
    Real.log (n.factorial : ℝ)
        = Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) +
            (n : ℝ) * (Real.log (n : ℝ) - 1) := by
          linarith
    _ = (n : ℝ) * Real.log (n : ℝ) - ↑n +
          (Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * ↑n)) := by
          ring

theorem log_stirlingSeq_isBigO_log :
    (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) := by
  have hlim :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (nhds (Real.log (Real.sqrt Real.pi))) := by
    exact Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)
  have hOone :
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) =O[atTop]
        fun _n : ℕ => (1 : ℝ) :=
    isBigO_const_of_tendsto hlim one_ne_zero
  have honeOlog : (fun _n : ℕ => (1 : ℝ)) =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) := by
    exact Real.isLittleO_const_log_atTop.isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  exact hOone.trans honeOlog

theorem log_two_mul_nat_isBigO_log :
    (fun n : ℕ => Real.log (2 * (n : ℝ))) =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) := by
  exact (Real.isBigO_log_const_mul_log_atTop 2).comp_tendsto tendsto_natCast_atTop_atTop

theorem log_factorial_stirling_remainder_isBigO_log :
    logFactorialStirlingRemainder =O[atTop] fun n : ℕ => Real.log (n : ℝ) := by
  unfold logFactorialStirlingRemainder
  exact log_stirlingSeq_isBigO_log.add (log_two_mul_nat_isBigO_log.const_mul_left (1 / 2 : ℝ))

theorem log_factorial_stirling_bigO :
    (fun n : ℕ => Real.log (n.factorial : ℝ) - logFactorialMainTerm n) =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) := by
  have heq :
      (fun n : ℕ => Real.log (n.factorial : ℝ) - logFactorialMainTerm n) =ᶠ[atTop]
        logFactorialStirlingRemainder := by
    filter_upwards [log_factorial_stirling_remainder_eventually] with n hn
    rw [hn]
    abel
  exact log_factorial_stirling_remainder_isBigO_log.congr' heq.symm EventuallyEq.rfl

end

end SymmetryMonograph.Chapter2
