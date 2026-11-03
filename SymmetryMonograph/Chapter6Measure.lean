import SymmetryMonograph.Chapter6
import Mathlib.InformationTheory.KullbackLeibler.Basic

set_option linter.style.header false

namespace SymmetryMonograph.Chapter6
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

section Haar
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ]

/-- The positive-measure direction needs only a finite invariant measure and
measurability of the subgroup; compactness is not needed for this argument. -/
theorem finiteIndex_of_subgroup_measure_pos (H : Subgroup G)
    (hH : MeasurableSet (H : Set G)) (hpos : 0 < μ H) : H.FiniteIndex := by
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 1
  have hfin := finite_const_le_meas_of_disjoint_iUnion μ hpos
    (fun a : s => hH.const_smul a.val)
    (fun a b hab => hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab))
    (measure_ne_top μ _)
  have hf : Finite s := by
    have hu : Set.Finite (Set.univ : Set s) := by
      simpa only [measure_smul, le_refl, setOf_true] using hfin
    exact Set.finite_univ_iff.mp hu
  exact hs.finite_left_iff.mp hf

theorem subgroup_measure_eq_inv_index (H : Subgroup G) [H.FiniteIndex]
    (hH : MeasurableSet (H : Set G)) : μ H = (H.index : ℝ≥0∞)⁻¹ := by
  have h := MeasureTheory.Subgroup.index_mul_measure H hH μ
  rw [measure_univ] at h
  have hn : (H.index : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := H))
  calc
    μ H = (H.index : ℝ≥0∞)⁻¹ * ((H.index : ℝ≥0∞) * μ H) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hn (by simp), one_mul]
    _ = (H.index : ℝ≥0∞)⁻¹ := by rw [h, mul_one]

theorem subgroup_measure_pos_iff_finiteIndex (H : Subgroup G)
    (hH : MeasurableSet (H : Set G)) : 0 < μ H ↔ H.FiniteIndex := by
  constructor
  · exact finiteIndex_of_subgroup_measure_pos μ H hH
  · intro h
    letI := h
    rw [subgroup_measure_eq_inv_index μ H hH]
    simp
end Haar

section RelativeEntropy
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (ν μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

/-- Extended relative entropy also records singular laws without turning infinity into zero. -/
def measureSymmetryDeficit : ℝ≥0∞ := InformationTheory.klDiv ν μ

theorem measureSymmetryDeficit_eq_zero_iff :
    measureSymmetryDeficit ν μ = 0 ↔ ν = μ :=
  InformationTheory.klDiv_eq_zero_iff

theorem measureDeficit_integral_nonneg (hac : ν ≪ μ)
    (hint : Integrable (llr ν μ) ν) : 0 ≤ ∫ x, llr ν μ x ∂ν := by
  simpa using InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint

theorem measureDeficit_integral_eq_zero_iff (hac : ν ≪ μ)
    (hint : Integrable (llr ν μ) ν) : (∫ x, llr ν μ x ∂ν) = 0 ↔ ν = μ := by
  have heq : (InformationTheory.klDiv ν μ).toReal = ∫ x, llr ν μ x ∂ν := by
    simpa using InformationTheory.toReal_klDiv hac hint
  rw [← heq, ENNReal.toReal_eq_zero_iff]
  simp [InformationTheory.klDiv_ne_top hac hint, InformationTheory.klDiv_eq_zero_iff]

theorem measureSymmetryDeficit_map (e : X ≃ᵐ Y) (hac : ν ≪ μ) :
    measureSymmetryDeficit (ν.map e) (μ.map e) = measureSymmetryDeficit ν μ := by
  unfold measureSymmetryDeficit
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac
    (e.measurableEmbedding.absolutelyContinuous_map hac),
    InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac, lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map ν μ] with x hx
  rw [hx]

theorem measureSymmetryDeficit_invariant (e : X ≃ᵐ X) (he : μ.map e = μ)
    (hac : ν ≪ μ) : measureSymmetryDeficit (ν.map e) μ = measureSymmetryDeficit ν μ := by
  nth_rw 1 [← he]
  exact measureSymmetryDeficit_map ν μ e hac
end RelativeEntropy

end
end SymmetryMonograph.Chapter6
