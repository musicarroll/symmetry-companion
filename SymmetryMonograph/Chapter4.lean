import SymmetryMonograph.BinaryRelations

set_option linter.style.header false

/-!
# Chapter 4: operations as relations

Formal counterparts for the first structural statements in Chapter 4.  Binary
operations are represented by their graph ternary relations.
-/

namespace SymmetryMonograph.Chapter4

noncomputable section

variable {α : Type u}

abbrev TernaryRel (α : Type u) := Set (α × α × α)

def opGraph (μ : α → α → α) : TernaryRel α :=
  {t | t.2.2 = μ t.1 t.2.1}

def FunctionalInThirdCoordinate (T : TernaryRel α) : Prop :=
  ∀ x y, ∃! z, (x, y, z) ∈ T

def ternaryRelMap (σ : Equiv.Perm α) (T : TernaryRel α) : TernaryRel α :=
  {t | (σ.symm t.1, σ.symm t.2.1, σ.symm t.2.2) ∈ T}

def PreservesOperation (σ : Equiv.Perm α) (μ : α → α → α) : Prop :=
  ∀ x y, σ (μ x y) = μ (σ x) (σ y)

theorem opGraph_functional (μ : α → α → α) :
    FunctionalInThirdCoordinate (opGraph μ) := by
  intro x y
  refine ⟨μ x y, ?_, ?_⟩
  · rfl
  · intro z hz
    simpa [opGraph] using hz

theorem functional_iff_exists_opGraph (T : TernaryRel α) :
    FunctionalInThirdCoordinate T ↔ ∃ μ : α → α → α, opGraph μ = T := by
  constructor
  · intro hT
    classical
    let μ : α → α → α := fun x y => Classical.choose (hT x y)
    refine ⟨μ, ?_⟩
    ext t
    rcases t with ⟨x, y, z⟩
    constructor
    · intro ht
      rw [show z = μ x y by simpa [opGraph] using ht]
      exact (Classical.choose_spec (hT x y)).1
    · intro ht
      have huniq := (Classical.choose_spec (hT x y)).2 z ht
      simpa [opGraph, μ] using huniq
  · rintro ⟨μ, rfl⟩
    exact opGraph_functional μ

theorem preservesOperation_iff_preserves_opGraph
    (σ : Equiv.Perm α) (μ : α → α → α) :
    PreservesOperation σ μ ↔ ternaryRelMap σ (opGraph μ) = opGraph μ := by
  constructor
  · intro hσ
    ext t
    rcases t with ⟨x, y, z⟩
    constructor
    · intro ht
      have h := congrArg σ ht
      have hop : σ (μ (σ.symm x) (σ.symm y)) = μ x y := by
        simpa using hσ (σ.symm x) (σ.symm y)
      simpa [ternaryRelMap, opGraph, hop] using h
    · intro ht
      have h := congrArg σ.symm ht
      have hop : σ.symm (μ x y) = μ (σ.symm x) (σ.symm y) := by
        apply σ.injective
        simpa using (hσ (σ.symm x) (σ.symm y)).symm
      simpa [ternaryRelMap, opGraph, hop] using h
  · intro hgraph x y
    have hmem : (σ x, σ y, σ (μ x y)) ∈ ternaryRelMap σ (opGraph μ) := by
      simp [ternaryRelMap, opGraph]
    have hmem_graph : (σ x, σ y, σ (μ x y)) ∈ opGraph μ := by
      simpa [hgraph] using hmem
    simpa [opGraph] using hmem_graph

structure AlgRelStructure (α : Type u) where
  relations : Set (BinaryRel α)
  operations : Set (α → α → α)

def AlgRelStructure.IsAutomorphism
    (A : AlgRelStructure α) (σ : Equiv.Perm α) : Prop :=
  (∀ R, R ∈ A.relations → relMap σ R = R) ∧
    (∀ μ, μ ∈ A.operations → PreservesOperation σ μ)

def AlgRelStructure.AutSet (A : AlgRelStructure α) : Set (Equiv.Perm α) :=
  {σ | A.IsAutomorphism σ}

def AlgRelStructure.symmetryMultiplicity (A : AlgRelStructure α) : ℝ :=
  (Nat.card (Equiv.Perm α) : ℝ) / (Nat.card A.AutSet : ℝ)

def AlgRelStructure.symmetryDeficit (A : AlgRelStructure α) : ℝ :=
  Real.log A.symmetryMultiplicity

def AlgRelStructure.IsRigid (A : AlgRelStructure α) : Prop :=
  A.AutSet = {1}

def AlgRelStructure.DataContained (A₁ A₂ : AlgRelStructure α) : Prop :=
  A₁.relations ⊆ A₂.relations ∧ A₁.operations ⊆ A₂.operations

theorem one_preserves_operation (μ : α → α → α) :
    PreservesOperation (1 : Equiv.Perm α) μ := by
  intro x y
  rfl

theorem one_mem_algAutSet (A : AlgRelStructure α) :
    (1 : Equiv.Perm α) ∈ A.AutSet := by
  constructor
  · intro R _hR
    exact relMap_one R
  · intro μ _hμ
    exact one_preserves_operation μ

theorem alg_aut_card_pos [Finite α] (A : AlgRelStructure α) :
    0 < Nat.card A.AutSet := by
  rw [Nat.card_coe_set_eq, Set.ncard_pos]
  exact ⟨1, one_mem_algAutSet A⟩

theorem alg_aut_size_bound [Finite α] (A : AlgRelStructure α) :
    Nat.card A.AutSet ≤ Nat.card (Equiv.Perm α) := by
  exact Set.ncard_le_card A.AutSet

theorem alg_refinement_aut_subset {A₁ A₂ : AlgRelStructure α}
    (h : A₁.DataContained A₂) :
    A₂.AutSet ⊆ A₁.AutSet := by
  intro σ hσ
  constructor
  · intro R hR
    exact hσ.1 R (h.1 hR)
  · intro μ hμ
    exact hσ.2 μ (h.2 hμ)

theorem alg_refinement_aut_card_le [Finite α] {A₁ A₂ : AlgRelStructure α}
    (h : A₁.DataContained A₂) :
    Nat.card A₂.AutSet ≤ Nat.card A₁.AutSet := by
  exact Set.ncard_le_ncard (alg_refinement_aut_subset h)

theorem alg_symmetryMultiplicity_one_le [Finite α] (A : AlgRelStructure α) :
    1 ≤ A.symmetryMultiplicity := by
  have hcard := alg_aut_size_bound A
  have hpos : (0 : ℝ) < Nat.card A.AutSet := by exact_mod_cast alg_aut_card_pos A
  rw [AlgRelStructure.symmetryMultiplicity]
  exact (one_le_div hpos).mpr (by exact_mod_cast hcard)

theorem alg_symmetryDeficit_nonneg [Finite α] (A : AlgRelStructure α) :
    0 ≤ A.symmetryDeficit := by
  rw [AlgRelStructure.symmetryDeficit]
  exact Real.log_nonneg (alg_symmetryMultiplicity_one_le A)

theorem alg_symmetryDeficit_le_log_perm_card [Finite α] (A : AlgRelStructure α) :
    A.symmetryDeficit ≤ Real.log (Nat.card (Equiv.Perm α) : ℝ) := by
  rw [AlgRelStructure.symmetryDeficit, AlgRelStructure.symmetryMultiplicity]
  apply Real.log_le_log
  · exact div_pos (by exact_mod_cast (Nat.card_pos (α := Equiv.Perm α)))
      (by exact_mod_cast alg_aut_card_pos A)
  · have hden_pos : (0 : ℝ) < Nat.card A.AutSet := by exact_mod_cast alg_aut_card_pos A
    have hden_ge_one : (1 : ℝ) ≤ Nat.card A.AutSet := by exact_mod_cast alg_aut_card_pos A
    rw [div_le_iff₀ hden_pos]
    nlinarith [show (0 : ℝ) ≤ Nat.card (Equiv.Perm α) by positivity]

theorem alg_rigid_symmetryDeficit_eq_log_perm_card [Finite α]
    {A : AlgRelStructure α} (h : A.IsRigid) :
    A.symmetryDeficit = Real.log (Nat.card (Equiv.Perm α) : ℝ) := by
  rw [AlgRelStructure.symmetryDeficit, AlgRelStructure.symmetryMultiplicity,
    AlgRelStructure.IsRigid] at *
  rw [h]
  simp


theorem alg_symmetryDeficit_eq_zero_iff_autSet_eq_univ [Finite α]
    (A : AlgRelStructure α) : A.symmetryDeficit = 0 ↔ A.AutSet = Set.univ := by
  constructor
  · intro h
    have hm := Real.eq_one_of_pos_of_log_eq_zero
      (lt_of_lt_of_le zero_lt_one (alg_symmetryMultiplicity_one_le A)) h
    have ha : (0 : ℝ) < Nat.card A.AutSet := by exact_mod_cast alg_aut_card_pos A
    have hc : Nat.card A.AutSet = Nat.card (Equiv.Perm α) := by
      have heq := (div_eq_one_iff_eq ha.ne').mp hm
      exact_mod_cast heq.symm
    rw [Set.eq_univ_iff_ncard]
    simpa [Nat.card_coe_set_eq] using hc
  · intro h
    simp [AlgRelStructure.symmetryDeficit, AlgRelStructure.symmetryMultiplicity, h]

theorem alg_symmetryDeficit_eq_max_iff_rigid [Finite α]
    (A : AlgRelStructure α) :
    A.symmetryDeficit = Real.log (Nat.card (Equiv.Perm α) : ℝ) ↔ A.IsRigid := by
  constructor
  · intro h
    have hp : (0 : ℝ) < Nat.card (Equiv.Perm α) := by
      exact_mod_cast (Nat.card_pos (α := Equiv.Perm α))
    have ha : (0 : ℝ) < Nat.card A.AutSet := by exact_mod_cast alg_aut_card_pos A
    have heq := Real.log_injOn_pos (div_pos hp ha) hp h
    change (Nat.card (Equiv.Perm α) : ℝ) / Nat.card A.AutSet =
      Nat.card (Equiv.Perm α) at heq
    have hc : (Nat.card A.AutSet : ℝ) = 1 := by
      have := (div_eq_iff ha.ne').mp heq
      nlinarith
    exact (natCard_eq_one_iff_eq_singleton A.AutSet 1 (one_mem_algAutSet A)).mp
      (by exact_mod_cast hc)
  · exact alg_rigid_symmetryDeficit_eq_log_perm_card

end

end SymmetryMonograph.Chapter4
