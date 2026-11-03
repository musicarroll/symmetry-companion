import Mathlib
import Mathlib.GroupTheory.ArchimedeanDensely

set_option linter.style.header false

/-!
# Chapter 5: classical infinite structures

Small formal counterparts for the integer automorphism examples in Chapter 5.
-/

namespace SymmetryMonograph.Chapter5

noncomputable section

def finiteSymmetryDeficitFormula (fullSymmetry residualSymmetry : ℝ) : ℝ :=
  Real.log (fullSymmetry / residualSymmetry)

def ExtendsFiniteSymmetryDeficitTheory (I : ℝ → ℝ → ℝ) : Prop :=
  ∀ fullSymmetry residualSymmetry,
    I fullSymmetry residualSymmetry =
      finiteSymmetryDeficitFormula fullSymmetry residualSymmetry

theorem finite_extension_agrees_with_cardinality_formula
    {I : ℝ → ℝ → ℝ} (hI : ExtendsFiniteSymmetryDeficitTheory I)
    (fullSymmetry residualSymmetry : ℝ) :
    I fullSymmetry residualSymmetry =
      Real.log (fullSymmetry / residualSymmetry) := by
  exact hI fullSymmetry residualSymmetry

theorem int_additive_automorphism_card :
    Fintype.card (ℤ ≃+ ℤ) = 2 := by
  exact Int.card_fintype_addEquiv

theorem int_ring_automorphism_subsingleton :
    Subsingleton (ℤ ≃+* ℤ) := by
  constructor
  intro f g
  ext n
  exact (map_intCast f n).trans (map_intCast g n).symm

theorem int_ring_automorphism_eq_refl (f : ℤ ≃+* ℤ) :
    f = RingEquiv.refl ℤ := by
  exact @Subsingleton.elim (ℤ ≃+* ℤ) int_ring_automorphism_subsingleton f (RingEquiv.refl ℤ)

theorem real_ring_automorphism_monotone (f : ℝ ≃+* ℝ) : Monotone f := by
  intro x y hxy
  have hnonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hsqrt : (Real.sqrt (y - x)) ^ 2 = y - x := Real.sq_sqrt hnonneg
  have hmap_nonneg : 0 ≤ f (y - x) := by
    rw [← hsqrt, map_pow]
    positivity
  rw [map_sub] at hmap_nonneg
  exact sub_nonneg.mp hmap_nonneg

theorem real_field_automorphism_eq_refl (f : ℝ ≃+* ℝ) :
    f = RingEquiv.refl ℝ := by
  let g : ℝ →+*o ℝ :=
    { f.toRingHom with
      monotone' := real_ring_automorphism_monotone f }
  ext x
  exact g.apply_eq_self x

theorem real_field_automorphism_subsingleton :
    Subsingleton (ℝ ≃+* ℝ) := by
  constructor
  intro f g
  rw [real_field_automorphism_eq_refl f, real_field_automorphism_eq_refl g]

end

end SymmetryMonograph.Chapter5
