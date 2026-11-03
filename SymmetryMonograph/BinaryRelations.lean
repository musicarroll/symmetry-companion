import SymmetryMonograph.FiniteRelationalStructures

set_option linter.style.header false

/-!
# Binary relation operations

Formal versions of the set-operation results from Chapter 1, Section 4.
-/

namespace SymmetryMonograph

noncomputable section

def singleRelStructure {α : Type u} (R : BinaryRel α) : RelStructure α :=
  ⟨{R}⟩

def pairRelStructure {α : Type u} (R S : BinaryRel α) : RelStructure α :=
  ⟨{R, S}⟩

def relComp {α : Type u} (R S : BinaryRel α) : BinaryRel α :=
  {p | ∃ y, (p.1, y) ∈ R ∧ (y, p.2) ∈ S}

def relConv {α : Type u} (R : BinaryRel α) : BinaryRel α :=
  {p | (p.2, p.1) ∈ R}

theorem relMap_union {α : Type u} (σ : Equiv.Perm α) (R S : BinaryRel α) :
    relMap σ (R ∪ S) = relMap σ R ∪ relMap σ S := by
  ext p
  rfl

theorem relMap_inter {α : Type u} (σ : Equiv.Perm α) (R S : BinaryRel α) :
    relMap σ (R ∩ S) = relMap σ R ∩ relMap σ S := by
  ext p
  rfl

theorem relMap_diff {α : Type u} (σ : Equiv.Perm α) (R S : BinaryRel α) :
    relMap σ (R \ S) = relMap σ R \ relMap σ S := by
  ext p
  rfl

theorem relMap_comp {α : Type u} (σ : Equiv.Perm α) (R S : BinaryRel α) :
    relMap σ (relComp R S) = relComp (relMap σ R) (relMap σ S) := by
  ext p
  constructor
  · intro h
    rcases h with ⟨y, hyR, hyS⟩
    refine ⟨σ y, ?_, ?_⟩
    · simpa [relMap] using hyR
    · simpa [relMap] using hyS
  · intro h
    rcases h with ⟨y, hyR, hyS⟩
    refine ⟨σ.symm y, ?_, ?_⟩
    · simpa [relMap] using hyR
    · simpa [relMap] using hyS

theorem preserves_union {α : Type u} {σ : Equiv.Perm α} {R S : BinaryRel α}
    (hR : relMap σ R = R) (hS : relMap σ S = S) :
    relMap σ (R ∪ S) = R ∪ S := by
  rw [relMap_union, hR, hS]

theorem preserves_inter {α : Type u} {σ : Equiv.Perm α} {R S : BinaryRel α}
    (hR : relMap σ R = R) (hS : relMap σ S = S) :
    relMap σ (R ∩ S) = R ∩ S := by
  rw [relMap_inter, hR, hS]

theorem preserves_diff {α : Type u} {σ : Equiv.Perm α} {R S : BinaryRel α}
    (hR : relMap σ R = R) (hS : relMap σ S = S) :
    relMap σ (R \ S) = R \ S := by
  rw [relMap_diff, hR, hS]

theorem preserves_comp {α : Type u} {σ : Equiv.Perm α} {R S : BinaryRel α}
    (hR : relMap σ R = R) (hS : relMap σ S = S) :
    relMap σ (relComp R S) = relComp R S := by
  rw [relMap_comp, hR, hS]

theorem relMap_compl {α : Type u} (σ : Equiv.Perm α) (R : BinaryRel α) :
    relMap σ Rᶜ = (relMap σ R)ᶜ := by
  ext p
  rfl

theorem preserves_compl_iff {α : Type u} {σ : Equiv.Perm α} {R : BinaryRel α} :
    relMap σ Rᶜ = Rᶜ ↔ relMap σ R = R := by
  constructor
  · intro h
    apply compl_injective
    rw [← relMap_compl σ R, h]
  · intro h
    rw [relMap_compl, h]

theorem relMap_conv {α : Type u} (σ : Equiv.Perm α) (R : BinaryRel α) :
    relMap σ (relConv R) = relConv (relMap σ R) := by
  ext p
  rfl

theorem relConv_injective {α : Type u} : Function.Injective (@relConv α) := by
  intro R S h
  ext p
  have hp := Set.ext_iff.mp h (p.2, p.1)
  simpa [relConv] using hp

theorem preserves_conv_iff {α : Type u} {σ : Equiv.Perm α} {R : BinaryRel α} :
    relMap σ (relConv R) = relConv R ↔ relMap σ R = R := by
  constructor
  · intro h
    apply relConv_injective
    rw [← relMap_conv σ R, h]
  · intro h
    rw [relMap_conv, h]

theorem pair_autSet_eq_inter {α : Type u} (R S : BinaryRel α) :
    (pairRelStructure R S).AutSet =
      (singleRelStructure R).AutSet ∩ (singleRelStructure S).AutSet := by
  ext σ
  constructor
  · intro hσ
    constructor
    · intro T hT
      rw [show T = R by simpa [singleRelStructure] using hT]
      exact hσ R (by simp [pairRelStructure])
    · intro T hT
      rw [show T = S by simpa [singleRelStructure] using hT]
      exact hσ S (by simp [pairRelStructure])
  · intro hσ T hT
    have hcases : T = R ∨ T = S := by simpa [pairRelStructure] using hT
    rcases hcases with hTR | hTS
    · rw [hTR]
      exact hσ.1 R (by simp [singleRelStructure])
    · rw [hTS]
      exact hσ.2 S (by simp [singleRelStructure])

theorem single_autSet_compl_eq {α : Type u} (R : BinaryRel α) :
    (singleRelStructure Rᶜ).AutSet = (singleRelStructure R).AutSet := by
  ext σ
  constructor
  · intro hσ T hT
    rw [show T = R by simpa [singleRelStructure] using hT]
    exact preserves_compl_iff.mp (hσ Rᶜ (by simp [singleRelStructure]))
  · intro hσ T hT
    rw [show T = Rᶜ by simpa [singleRelStructure] using hT]
    exact preserves_compl_iff.mpr (hσ R (by simp [singleRelStructure]))

theorem single_autSet_conv_eq {α : Type u} (R : BinaryRel α) :
    (singleRelStructure (relConv R)).AutSet = (singleRelStructure R).AutSet := by
  ext σ
  constructor
  · intro hσ T hT
    rw [show T = R by simpa [singleRelStructure] using hT]
    exact preserves_conv_iff.mp (hσ (relConv R) (by simp [singleRelStructure]))
  · intro hσ T hT
    rw [show T = relConv R by simpa [singleRelStructure] using hT]
    exact preserves_conv_iff.mpr (hσ R (by simp [singleRelStructure]))

theorem symmetryDeficit_compl_eq {α : Type u} [Finite α] (R : BinaryRel α) :
    (singleRelStructure Rᶜ).symmetryDeficit = (singleRelStructure R).symmetryDeficit := by
  rw [RelStructure.symmetryDeficit, RelStructure.symmetryDeficit,
    RelStructure.symmetryMultiplicity, RelStructure.symmetryMultiplicity,
    single_autSet_compl_eq]

theorem symmetryDeficit_conv_eq {α : Type u} [Finite α] (R : BinaryRel α) :
    (singleRelStructure (relConv R)).symmetryDeficit =
      (singleRelStructure R).symmetryDeficit := by
  rw [RelStructure.symmetryDeficit, RelStructure.symmetryDeficit,
    RelStructure.symmetryMultiplicity, RelStructure.symmetryMultiplicity,
    single_autSet_conv_eq]

theorem invariant_operand_union_aut_subset {α : Type u} {R S : BinaryRel α}
    (h : (singleRelStructure R).AutSet ⊆ (singleRelStructure S).AutSet) :
    (singleRelStructure R).AutSet ⊆ (singleRelStructure (R ∪ S)).AutSet := by
  intro σ hσ T hT
  rw [show T = R ∪ S by simpa [singleRelStructure] using hT]
  exact preserves_union (hσ R (by simp [singleRelStructure]))
    ((h hσ) S (by simp [singleRelStructure]))

theorem invariant_operand_inter_aut_subset {α : Type u} {R S : BinaryRel α}
    (h : (singleRelStructure R).AutSet ⊆ (singleRelStructure S).AutSet) :
    (singleRelStructure R).AutSet ⊆ (singleRelStructure (R ∩ S)).AutSet := by
  intro σ hσ T hT
  rw [show T = R ∩ S by simpa [singleRelStructure] using hT]
  exact preserves_inter (hσ R (by simp [singleRelStructure]))
    ((h hσ) S (by simp [singleRelStructure]))

theorem invariant_operand_diff_aut_subset {α : Type u} {R S : BinaryRel α}
    (h : (singleRelStructure R).AutSet ⊆ (singleRelStructure S).AutSet) :
    (singleRelStructure R).AutSet ⊆ (singleRelStructure (R \ S)).AutSet := by
  intro σ hσ T hT
  rw [show T = R \ S by simpa [singleRelStructure] using hT]
  exact preserves_diff (hσ R (by simp [singleRelStructure]))
    ((h hσ) S (by simp [singleRelStructure]))

theorem invariant_operand_union_symmetryDeficit_le {α : Type u} [Finite α]
    {R S : BinaryRel α}
    (h : (singleRelStructure R).AutSet ⊆ (singleRelStructure S).AutSet) :
    (singleRelStructure (R ∪ S)).symmetryDeficit ≤
      (singleRelStructure R).symmetryDeficit :=
  symmetryDeficit_le_of_autSet_subset (invariant_operand_union_aut_subset h)

theorem invariant_operand_inter_symmetryDeficit_le {α : Type u} [Finite α]
    {R S : BinaryRel α}
    (h : (singleRelStructure R).AutSet ⊆ (singleRelStructure S).AutSet) :
    (singleRelStructure (R ∩ S)).symmetryDeficit ≤
      (singleRelStructure R).symmetryDeficit :=
  symmetryDeficit_le_of_autSet_subset (invariant_operand_inter_aut_subset h)

theorem invariant_operand_diff_symmetryDeficit_le {α : Type u} [Finite α]
    {R S : BinaryRel α}
    (h : (singleRelStructure R).AutSet ⊆ (singleRelStructure S).AutSet) :
    (singleRelStructure (R \ S)).symmetryDeficit ≤
      (singleRelStructure R).symmetryDeficit :=
  symmetryDeficit_le_of_autSet_subset (invariant_operand_diff_aut_subset h)

end

end SymmetryMonograph
