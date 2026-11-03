import Mathlib

set_option linter.style.header false

/-!
# Chapter 6: discrete reference-group symmetry

This file formalizes the discrete group-action core of Chapter 6.  A physical
reference group `G` acts on a type of states `X`; the residual symmetry of a
state is its stabilizer.  The numerical deficit is the logarithm of the
stabilizer index and is mathematically meaningful when that stabilizer has
finite index.
-/

namespace SymmetryMonograph.Chapter6

noncomputable section

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

/-- The residual symmetry subgroup of a state relative to the reference
group acting on the state space. -/
def residualSymmetry (G : Type*) [Group G] {X : Type*} [MulAction G X]
    (s : X) : Subgroup G :=
  MulAction.stabilizer G s

/-- The deficit associated with a residual subgroup.  Its physical
interpretation requires the hypothesis `H.FiniteIndex`. -/
def referenceSubgroupDeficit (H : Subgroup G) [H.FiniteIndex] : ℝ :=
  Real.log (H.index : ℝ)

/-- The reference-group symmetry deficit of a state with finite-index residual
stabilizer. -/
def referenceGroupDeficit (G : Type*) [Group G] {X : Type*} [MulAction G X]
    (s : X) [(residualSymmetry G s).FiniteIndex] : ℝ :=
  referenceSubgroupDeficit (residualSymmetry G s)

/-- Stabilizers of states in the same orbit are conjugate.  The subgroup map
by `MulAut.conj g` is the formal version of `g H_s g⁻¹`. -/
theorem reference_stabilizer_conjugate (g : G) (s : X) :
    residualSymmetry G (g • s) =
      (residualSymmetry G s).map (MulAut.conj g).toMonoidHom := by
  simpa [residualSymmetry] using
    (MulAction.stabilizer_smul_eq_stabilizer_map_conj g s)

/-- Conjugate residual subgroups have equal index in the reference group. -/
theorem residualSymmetry_index_smul (g : G) (s : X) :
    (residualSymmetry G (g • s)).index = (residualSymmetry G s).index := by
  rw [reference_stabilizer_conjugate]
  exact Subgroup.index_map_equiv (residualSymmetry G s) (MulAut.conj g)

/-- A finite-index residual subgroup remains finite-index along its orbit. -/
theorem residualSymmetry_finiteIndex_smul (g : G) (s : X)
    [(residualSymmetry G s).FiniteIndex] :
    (residualSymmetry G (g • s)).FiniteIndex := by
  constructor
  rw [residualSymmetry_index_smul]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The reference-group deficit is constant on each orbit. -/
theorem referenceGroupDeficit_orbit_invariant (g : G) (s : X)
    [(residualSymmetry G s).FiniteIndex]
    [(residualSymmetry G (g • s)).FiniteIndex] :
    referenceGroupDeficit G (g • s) = referenceGroupDeficit G s := by
  simp only [referenceGroupDeficit, referenceSubgroupDeficit]
  rw [residualSymmetry_index_smul]

/-- At fixed reference group, inclusion of finite-index residual subgroups
reverses the symmetry deficit: a smaller residual group has at least as large
a deficit. -/
theorem referenceSubgroupDeficit_antitone {H₁ H₂ : Subgroup G}
    (h : H₂ ≤ H₁) [H₁.FiniteIndex] [H₂.FiniteIndex] :
    referenceSubgroupDeficit H₁ ≤ referenceSubgroupDeficit H₂ := by
  apply Real.log_le_log
  · exact_mod_cast Nat.zero_lt_of_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := H₁))
  · exact_mod_cast Subgroup.index_antitone h

/-- State-level form of monotonicity at fixed reference group. -/
theorem referenceGroupDeficit_mono_of_residualSymmetry_le (s₁ s₂ : X)
    (h : residualSymmetry G s₂ ≤ residualSymmetry G s₁)
    [(residualSymmetry G s₁).FiniteIndex]
    [(residualSymmetry G s₂).FiniteIndex] :
    referenceGroupDeficit G s₁ ≤ referenceGroupDeficit G s₂ := by
  exact referenceSubgroupDeficit_antitone h

end

end SymmetryMonograph.Chapter6
