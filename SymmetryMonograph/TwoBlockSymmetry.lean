import SymmetryMonograph.Chapter3
import SymmetryMonograph.FiniteRelationalStructures

set_option linter.style.header false

namespace SymmetryMonograph.Chapter3
noncomputable section

/-- A pair of reduced parameters, with the permutation action on its two slots. -/
structure ParameterPair where
  coordinate : Fin 2 → ℝ

@[ext] theorem ParameterPair.ext {s t : ParameterPair}
    (h : ∀ i, s.coordinate i = t.coordinate i) : s = t := by
  cases s
  cases t
  congr
  exact funext h

instance : MulAction (Equiv.Perm (Fin 2)) ParameterPair where
  smul σ s := ⟨s.coordinate ∘ σ.symm⟩
  one_smul s := by ext i; rfl
  mul_smul σ τ s := by ext i; rfl

def parameterPair (p q : ℝ) : ParameterPair := ⟨![p, q]⟩

def parameterStabilizer (p q : ℝ) : Subgroup (Equiv.Perm (Fin 2)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 2)) (parameterPair p q)

theorem parameterStabilizer_eq_top {p q : ℝ} (h : p = q) :
    parameterStabilizer p q = ⊤ := by
  subst q
  apply top_unique
  intro σ _
  change σ • parameterPair p p = parameterPair p p
  ext i
  change (![p, p] : Fin 2 → ℝ) (σ.symm i) = ![p, p] i
  have hc : (![p, p] : Fin 2 → ℝ) = fun _ => p := by ext j; fin_cases j <;> rfl
  rw [hc]

theorem parameterStabilizer_eq_bot {p q : ℝ} (h : p ≠ q) :
    parameterStabilizer p q = ⊥ := by
  apply bot_unique
  intro σ hσ
  have hi : Function.Injective (![p, q] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have heq : σ • parameterPair p q = parameterPair p q := hσ
  have hfix : ∀ i, σ.symm i = i := fun i =>
    hi (congrArg (fun s => s.coordinate i) heq)
  change σ = 1
  apply Equiv.ext
  intro i
  have := congrArg σ (hfix i)
  simpa using this.symm

def coarseSymmetryDeficit (p q : ℝ) : ℝ :=
  Real.log ((Nat.card (Equiv.Perm (Fin 2)) : ℝ) / Nat.card (parameterStabilizer p q))

theorem coarseSymmetryDeficit_cases (p q : ℝ) :
    coarseSymmetryDeficit p q = if p = q then 0 else Real.log 2 := by
  classical
  unfold coarseSymmetryDeficit
  by_cases h : p = q
  · rw [parameterStabilizer_eq_top h]
    simp [h, Nat.card_eq_fintype_card, Fintype.card_perm]
  · rw [parameterStabilizer_eq_bot h]
    simp [h, Nat.card_eq_fintype_card, Fintype.card_perm]

theorem coarseSymmetryDeficit_eq_zero_iff (p q : ℝ) :
    coarseSymmetryDeficit p q = 0 ↔ |p - q| = 0 := by
  rw [coarseSymmetryDeficit_cases]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  by_cases h : p = q
  · simp [h]
  · simp only [h, ↓reduceIte, hlog, abs_eq_zero, sub_eq_zero]

theorem coarseSymmetryDeficit_eq_log_two_iff (p q : ℝ) :
    coarseSymmetryDeficit p q = Real.log 2 ↔ 0 < |p - q| := by
  rw [coarseSymmetryDeficit_cases]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  by_cases h : p = q
  · simp only [h, ↓reduceIte, sub_self, abs_zero, lt_self_iff_false, iff_false]
    exact hlog.symm
  · simp [h, abs_pos, sub_ne_zero]

end
end SymmetryMonograph.Chapter3
