import Mathlib

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Finite relational structures

Lean formalization for the foundational statements in Chapter 1 of the
monograph.  Relations are represented as sets of ordered pairs and
automorphisms are permutations preserving each relation in a family.
-/

namespace SymmetryMonograph

noncomputable section

abbrev BinaryRel (α : Type u) := Set (α × α)

structure RelStructure (α : Type u) where
  relations : Set (BinaryRel α)

def relMap (σ : Equiv.Perm α) (R : BinaryRel α) : BinaryRel α :=
  {p | (σ.symm p.1, σ.symm p.2) ∈ R}

def RelStructure.IsAutomorphism {α : Type u} (S : RelStructure α) (σ : Equiv.Perm α) : Prop :=
  ∀ R, R ∈ S.relations → relMap σ R = R

def RelStructure.AutSet {α : Type u} (S : RelStructure α) : Set (Equiv.Perm α) :=
  {σ | S.IsAutomorphism σ}

def RelStructure.symmetryMultiplicity {α : Type u} (S : RelStructure α) : ℝ :=
  (Nat.card (Equiv.Perm α) : ℝ) / (Nat.card S.AutSet : ℝ)

def RelStructure.symmetryDeficit {α : Type u} (S : RelStructure α) : ℝ :=
  Real.log S.symmetryMultiplicity

def RelStructure.degreeOfOrder {α : Type u} (S : RelStructure α) : ℕ :=
  Nat.card (Equiv.Perm α) - Nat.card S.AutSet

def RelStructure.IsRigid {α : Type u} (S : RelStructure α) : Prop :=
  S.AutSet = {1}

theorem relMap_one {α : Type u} (R : BinaryRel α) :
    relMap (1 : Equiv.Perm α) R = R := by
  ext p
  rfl

theorem one_mem_autSet {α : Type u} (S : RelStructure α) :
    (1 : Equiv.Perm α) ∈ S.AutSet := by
  intro R _hR
  exact relMap_one R

theorem aut_card_pos {α : Type u} [Finite α] (S : RelStructure α) :
    0 < Nat.card S.AutSet := by
  rw [Nat.card_coe_set_eq, Set.ncard_pos]
  exact ⟨1, one_mem_autSet S⟩

theorem aut_set_subset_all_perms {α : Type u} (S : RelStructure α) :
    S.AutSet ⊆ Set.univ := by
  intro σ hσ
  trivial

theorem aut_size_bound {α : Type u} [Finite α] (S : RelStructure α) :
    Nat.card S.AutSet ≤ Nat.card (Equiv.Perm α) := by
  exact Set.ncard_le_card S.AutSet

theorem symmetryMultiplicity_one_le {α : Type u} [Finite α] (S : RelStructure α) :
    1 ≤ S.symmetryMultiplicity := by
  have hcard := aut_size_bound S
  have hpos : (0 : ℝ) < Nat.card S.AutSet := by exact_mod_cast aut_card_pos S
  rw [RelStructure.symmetryMultiplicity]
  exact (one_le_div hpos).mpr (by exact_mod_cast hcard)

theorem symmetryDeficit_nonneg {α : Type u} [Finite α] (S : RelStructure α) :
    0 ≤ S.symmetryDeficit := by
  rw [RelStructure.symmetryDeficit]
  exact Real.log_nonneg (symmetryMultiplicity_one_le S)

theorem autSet_eq_univ_of_aut_card_eq_perm_card {α : Type u} [Finite α]
    {S : RelStructure α} (h : Nat.card S.AutSet = Nat.card (Equiv.Perm α)) :
    S.AutSet = Set.univ := by
  rw [Set.eq_univ_iff_ncard]
  simpa [Nat.card_coe_set_eq] using h

theorem symmetryDeficit_eq_zero_iff_autSet_eq_univ {α : Type u} [Finite α]
    (S : RelStructure α) :
    S.symmetryDeficit = 0 ↔ S.AutSet = Set.univ := by
  constructor
  · intro hzero
    have hmult_pos : 0 < S.symmetryMultiplicity := lt_of_lt_of_le zero_lt_one
      (symmetryMultiplicity_one_le S)
    have hmult_eq : S.symmetryMultiplicity = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hmult_pos hzero
    have hden_pos : (0 : ℝ) < Nat.card S.AutSet := by exact_mod_cast aut_card_pos S
    have hcard_real :
        (Nat.card (Equiv.Perm α) : ℝ) = (Nat.card S.AutSet : ℝ) := by
      rw [RelStructure.symmetryMultiplicity] at hmult_eq
      exact (div_eq_one_iff_eq hden_pos.ne').mp hmult_eq
    apply autSet_eq_univ_of_aut_card_eq_perm_card
    exact_mod_cast hcard_real.symm
  · intro h
    rw [RelStructure.symmetryDeficit, RelStructure.symmetryMultiplicity, h]
    simp

theorem rigid_symmetryDeficit_eq_log_perm_card {α : Type u} [Finite α]
    {S : RelStructure α} (h : S.IsRigid) :
    S.symmetryDeficit = Real.log (Nat.card (Equiv.Perm α) : ℝ) := by
  rw [RelStructure.symmetryDeficit, RelStructure.symmetryMultiplicity,
    RelStructure.IsRigid] at *
  rw [h]
  simp

theorem degreeOfOrder_nonneg {α : Type u} [Finite α] (S : RelStructure α) :
    0 ≤ S.degreeOfOrder := Nat.zero_le _

theorem degreeOfOrder_le_perm_card_sub_one {α : Type u} [Finite α] (S : RelStructure α) :
    S.degreeOfOrder ≤ Nat.card (Equiv.Perm α) - 1 := by
  rw [RelStructure.degreeOfOrder]
  exact Nat.sub_le_sub_left (aut_card_pos S) _

theorem rigid_degreeOfOrder_eq_perm_card_sub_one {α : Type u} [Finite α]
    {S : RelStructure α} (h : S.IsRigid) :
    S.degreeOfOrder = Nat.card (Equiv.Perm α) - 1 := by
  rw [RelStructure.degreeOfOrder, RelStructure.IsRigid] at *
  rw [h]
  simp

theorem refinement_aut_subset {α : Type u} {S₁ S₂ : RelStructure α}
    (h : S₁.relations ⊆ S₂.relations) :
    S₂.AutSet ⊆ S₁.AutSet := by
  intro σ hσ R hR
  exact hσ R (h hR)

theorem refinement_aut_card_le {α : Type u} [Finite α] {S₁ S₂ : RelStructure α}
    (h : S₁.relations ⊆ S₂.relations) :
    Nat.card S₂.AutSet ≤ Nat.card S₁.AutSet := by
  exact Set.ncard_le_ncard (refinement_aut_subset h)

theorem symmetryDeficit_le_of_autSet_subset {α : Type u} [Finite α]
    {S₁ S₂ : RelStructure α} (h : S₁.AutSet ⊆ S₂.AutSet) :
    S₂.symmetryDeficit ≤ S₁.symmetryDeficit := by
  rw [RelStructure.symmetryDeficit, RelStructure.symmetryDeficit]
  apply Real.log_le_log
  · rw [RelStructure.symmetryMultiplicity]
    exact div_pos (by exact_mod_cast (Nat.card_pos (α := Equiv.Perm α)))
      (by exact_mod_cast aut_card_pos S₂)
  · rw [RelStructure.symmetryMultiplicity, RelStructure.symmetryMultiplicity]
    have hcard : Nat.card S₁.AutSet ≤ Nat.card S₂.AutSet := Set.ncard_le_ncard h
    have hperm_nonneg : (0 : ℝ) ≤ Nat.card (Equiv.Perm α) := by positivity
    have hS₁pos : (0 : ℝ) < Nat.card S₁.AutSet := by exact_mod_cast aut_card_pos S₁
    exact div_le_div_of_nonneg_left hperm_nonneg hS₁pos (by exact_mod_cast hcard)

theorem refinement_symmetryDeficit_le {α : Type u} [Finite α] {S₁ S₂ : RelStructure α}
    (h : S₁.relations ⊆ S₂.relations) :
    S₁.symmetryDeficit ≤ S₂.symmetryDeficit := by
  exact symmetryDeficit_le_of_autSet_subset (refinement_aut_subset h)


/-- A finite set containing a distinguished element is a singleton exactly when
its cardinality is one. -/
theorem natCard_eq_one_iff_eq_singleton {α : Type*} [Finite α]
    (s : Set α) (a : α) (ha : a ∈ s) : Nat.card s = 1 ↔ s = {a} := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_one]
  constructor
  · rintro ⟨b, hb⟩
    have hab : a = b := by simpa [hb] using ha
    simpa [hab] using hb
  · intro h
    exact ⟨a, h⟩

theorem symmetryDeficit_le_log_perm_card {α : Type*} [Finite α]
    (S : RelStructure α) :
    S.symmetryDeficit ≤ Real.log (Nat.card (Equiv.Perm α) : ℝ) := by
  rw [RelStructure.symmetryDeficit, RelStructure.symmetryMultiplicity]
  have hp : (0 : ℝ) < Nat.card (Equiv.Perm α) := by
    exact_mod_cast (Nat.card_pos (α := Equiv.Perm α))
  have ha : (0 : ℝ) < Nat.card S.AutSet := by exact_mod_cast aut_card_pos S
  have ha1 : (1 : ℝ) ≤ Nat.card S.AutSet := by exact_mod_cast aut_card_pos S
  apply Real.log_le_log (div_pos hp ha)
  rw [div_le_iff₀ ha]
  nlinarith

theorem symmetryDeficit_eq_max_iff_rigid {α : Type*} [Finite α]
    (S : RelStructure α) :
    S.symmetryDeficit = Real.log (Nat.card (Equiv.Perm α) : ℝ) ↔ S.IsRigid := by
  constructor
  · intro h
    have hp : (0 : ℝ) < Nat.card (Equiv.Perm α) := by
      exact_mod_cast (Nat.card_pos (α := Equiv.Perm α))
    have ha : (0 : ℝ) < Nat.card S.AutSet := by exact_mod_cast aut_card_pos S
    have heq := Real.log_injOn_pos (div_pos hp ha) hp h
    change (Nat.card (Equiv.Perm α) : ℝ) / Nat.card S.AutSet =
      Nat.card (Equiv.Perm α) at heq
    have hc : (Nat.card S.AutSet : ℝ) = 1 := by
      have := (div_eq_iff ha.ne').mp heq
      nlinarith
    exact (natCard_eq_one_iff_eq_singleton S.AutSet 1 (one_mem_autSet S)).mp
      (by exact_mod_cast hc)
  · exact rigid_symmetryDeficit_eq_log_perm_card

theorem degreeOfOrder_eq_max_iff_rigid {α : Type*} [Finite α]
    (S : RelStructure α) :
    S.degreeOfOrder = Nat.card (Equiv.Perm α) - 1 ↔ S.IsRigid := by
  constructor
  · intro h
    have hle := aut_size_bound S
    have hpos := aut_card_pos S
    have hc : Nat.card S.AutSet = 1 := by
      unfold RelStructure.degreeOfOrder at h
      omega
    exact (natCard_eq_one_iff_eq_singleton S.AutSet 1 (one_mem_autSet S)).mp hc
  · exact rigid_degreeOfOrder_eq_perm_card_sub_one

end

end SymmetryMonograph
