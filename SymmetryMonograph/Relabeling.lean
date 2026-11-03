import SymmetryMonograph.Chapter4
import SymmetryMonograph.Chapter2

set_option linter.style.header false

/-!
# Fixed-signature relational structures and their relabeling action

Symbols are indexed, so relabeling cannot exchange two named relations.
Taking `Args i = Fin (arity i)` includes every finite arity, including zero.
Operations can be represented by their graph relations in this same model.
-/

namespace SymmetryMonograph

noncomputable section

structure RelationalModel {ι : Type*} (Args : ι → Type*) (α : Type*) where
  relation : ∀ i, Set (Args i → α)

namespace RelationalModel

variable {ι α : Type*} {Args : ι → Type*}

@[ext] theorem ext {S T : RelationalModel Args α}
    (h : ∀ i, S.relation i = T.relation i) : S = T := by
  cases S
  cases T
  congr
  exact funext h

def relabel (σ : Equiv.Perm α) (S : RelationalModel Args α) : RelationalModel Args α :=
  ⟨fun i => {t | (σ.symm ∘ t) ∈ S.relation i}⟩

instance : MulAction (Equiv.Perm α) (RelationalModel Args α) where
  smul := relabel
  one_smul S := by ext i t; rfl
  mul_smul σ τ S := by ext i t; rfl

def Aut (S : RelationalModel Args α) : Subgroup (Equiv.Perm α) :=
  MulAction.stabilizer (Equiv.Perm α) S

instance [Finite ι] [∀ i, Finite (Args i)] [Finite α] : Finite (RelationalModel Args α) :=
  Finite.of_injective RelationalModel.relation (fun _ _ h => ext (fun i => congrFun h i))

theorem mem_aut_iff (S : RelationalModel Args α) (σ : Equiv.Perm α) :
    σ ∈ S.Aut ↔ ∀ i t, (σ ∘ t) ∈ S.relation i ↔ t ∈ S.relation i := by
  change relabel σ S = S ↔ _
  constructor
  · intro h i t
    have hh := congrArg (fun T => (σ ∘ t) ∈ T.relation i) h
    simpa [relabel, Function.comp_def] using (Iff.of_eq hh).symm
  · intro h
    ext i t
    simpa [relabel, Function.comp_def] using (h i (σ.symm ∘ t)).symm

def restrict {κ : Type*} (S : RelationalModel Args α) (f : κ → ι) :
    RelationalModel (Args ∘ f) α := ⟨fun i => S.relation (f i)⟩

/-- Forgetting symbols can only enlarge the automorphism group. -/
theorem aut_le_restrict {κ : Type*} (S : RelationalModel Args α) (f : κ → ι) :
    S.Aut ≤ (S.restrict f).Aut := by
  intro σ hσ
  exact (mem_aut_iff _ σ).2 (fun i t => (mem_aut_iff S σ).1 hσ (f i) t)

def symmetryDeficit (S : RelationalModel Args α) : ℝ :=
  Real.log ((Nat.card (Equiv.Perm α) : ℝ) / Nat.card S.Aut)

theorem symmetryDeficit_eq_log_orbit [Finite α] (S : RelationalModel Args α) :
    S.symmetryDeficit = Real.log (Nat.card (MulAction.orbit (Equiv.Perm α) S)) := by
  letI := Fintype.ofFinite (Equiv.Perm α)
  letI := (Finite.finite_mulAction_orbit (M := Equiv.Perm α) S).fintype
  letI := Fintype.ofFinite (MulAction.stabilizer (Equiv.Perm α) S)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := Equiv.Perm α) (X := RelationalModel Args α) S
  have hp : (Nat.card S.Aut : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := S.Aut)).ne'
  apply congrArg Real.log
  apply (div_eq_iff hp).2
  simpa only [Nat.card_eq_fintype_card, Aut, Nat.cast_mul] using
    (congrArg (fun n : ℕ => (n : ℝ)) h).symm

theorem symmetryDeficit_eq_log_index [Finite α] (S : RelationalModel Args α) :
    S.symmetryDeficit = Real.log (S.Aut.index : ℝ) := by
  unfold symmetryDeficit
  congr 1
  apply (div_eq_iff (show (Nat.card S.Aut : ℝ) ≠ 0 by
    exact_mod_cast (Nat.card_pos (α := S.Aut)).ne')).2
  exact_mod_cast S.Aut.index_mul_card.symm

theorem symmetryDeficit_bounds [Finite α] (S : RelationalModel Args α) :
    0 ≤ S.symmetryDeficit ∧ S.symmetryDeficit ≤ Real.log (Nat.card (Equiv.Perm α)) := by
  rw [symmetryDeficit_eq_log_index]
  have hp : 0 < S.Aut.index := Nat.pos_of_ne_zero S.Aut.index_ne_zero_of_finite
  have hu : S.Aut.index ≤ Nat.card (Equiv.Perm α) :=
    Nat.le_of_dvd Nat.card_pos S.Aut.index_dvd_card
  constructor
  · exact Real.log_nonneg (by exact_mod_cast hp)
  · exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hu)

theorem symmetryDeficit_eq_zero_iff [Finite α] (S : RelationalModel Args α) :
    S.symmetryDeficit = 0 ↔ S.Aut = ⊤ := by
  rw [symmetryDeficit_eq_log_index, ← S.Aut.index_eq_one]
  have hp : (0 : ℝ) < S.Aut.index := by
    exact_mod_cast Nat.pos_of_ne_zero S.Aut.index_ne_zero_of_finite
  constructor
  · intro h
    exact_mod_cast Real.eq_one_of_pos_of_log_eq_zero hp h
  · intro h
    simp [h]

theorem symmetryDeficit_eq_max_iff [Finite α] (S : RelationalModel Args α) :
    S.symmetryDeficit = Real.log (Nat.card (Equiv.Perm α)) ↔ S.Aut = ⊥ := by
  rw [symmetryDeficit_eq_log_index]
  constructor
  · intro h
    have hi : S.Aut.index = Nat.card (Equiv.Perm α) := by
      exact_mod_cast Real.log_injOn_pos
        (by change (0 : ℝ) < S.Aut.index
            exact_mod_cast Nat.pos_of_ne_zero S.Aut.index_ne_zero_of_finite)
        (by change (0 : ℝ) < Nat.card (Equiv.Perm α)
            exact_mod_cast (Nat.card_pos (α := Equiv.Perm α))) h
    have hc : Nat.card S.Aut = 1 := by
      have hh := S.Aut.card_mul_index
      rw [hi] at hh
      nlinarith [Nat.card_pos (α := Equiv.Perm α)]
    exact Subgroup.card_eq_one.mp hc
  · intro h
    simp [h]

def degreeOfOrder (S : RelationalModel Args α) : ℕ :=
  Nat.card (Equiv.Perm α) - Nat.card S.Aut

theorem degreeOfOrder_bounds [Finite α] (S : RelationalModel Args α) :
    S.degreeOfOrder ≤ Nat.card (Equiv.Perm α) - 1 := by
  have hp := Nat.card_pos (α := S.Aut)
  unfold degreeOfOrder
  omega

theorem degreeOfOrder_eq_max_iff [Finite α] (S : RelationalModel Args α) :
    S.degreeOfOrder = Nat.card (Equiv.Perm α) - 1 ↔ S.Aut = ⊥ := by
  have hp := Nat.card_pos (α := S.Aut)
  have hu : Nat.card S.Aut ≤ Nat.card (Equiv.Perm α) := Set.ncard_le_card _
  rw [degreeOfOrder, ← Subgroup.card_eq_one]
  omega

theorem normalizedSymmetryDeficit_bounds [Finite α] (S : RelationalModel Args α)
    (h : 1 < Nat.card (Equiv.Perm α)) :
    0 ≤ S.symmetryDeficit / Real.log (Nat.card (Equiv.Perm α)) ∧
      S.symmetryDeficit / Real.log (Nat.card (Equiv.Perm α)) ≤ 1 := by
  have hp : 0 < Real.log (Nat.card (Equiv.Perm α)) := Real.log_pos (by exact_mod_cast h)
  exact ⟨div_nonneg S.symmetryDeficit_bounds.1 hp.le,
    (div_le_one hp).2 S.symmetryDeficit_bounds.2⟩

/-- An operation of any arity is a relation with one extra output coordinate.
The empty input type gives constants without a separate special case. -/
def operationModel {A : Type*} (μ : (A → α) → α) :
    RelationalModel (fun _ : Unit => Option A) α :=
  ⟨fun _ => {t | t none = μ (fun i => t (some i))}⟩

theorem operationModel_aut_iff {A : Type*} (μ : (A → α) → α) (σ : Equiv.Perm α) :
    σ ∈ (operationModel μ).Aut ↔ ∀ t, σ (μ t) = μ (σ ∘ t) := by
  rw [mem_aut_iff]
  constructor
  · intro h t
    let tuple : Option A → α := fun i => i.elim (μ t) t
    exact (h () tuple).2 rfl
  · intro h _ t
    change σ (t none) = μ (fun i => σ (t (some i))) ↔ t none = μ (fun i => t (some i))
    have hh := h (fun i => t (some i))
    dsimp [Function.comp_def] at hh
    rw [← hh]
    exact σ.injective.eq_iff

abbrev IsomorphismClass := MulAction.orbitRel.Quotient (Equiv.Perm α) (RelationalModel Args α)

/-- The class fiber is the actual orbit of a representative, not an assumed multiplicity. -/
theorem class_fiber_card (q : IsomorphismClass (Args := Args) (α := α)) :
    Nat.card {S : RelationalModel Args α // Quotient.mk'' S = q} =
      Nat.card (MulAction.orbit (Equiv.Perm α) q.out) := by
  apply Nat.card_congr (Equiv.subtypeEquivRight _)
  intro S
  nth_rw 1 [← q.out_eq]
  exact Quotient.eq''

/-- A finite labeled sum regroups by isomorphism classes with the book's
exponential symmetry-deficit multiplicity. -/
theorem labeled_partition_eq_class_partition [Finite ι] [∀ i, Finite (Args i)]
    [Finite α]
    (energy : IsomorphismClass (Args := Args) (α := α) → ℝ) (β : ℝ) :
    letI := Fintype.ofFinite (RelationalModel Args α)
    letI := Fintype.ofFinite (IsomorphismClass (Args := Args) (α := α))
    (∑ S : RelationalModel Args α, Real.exp (-β * energy (Quotient.mk'' S))) =
      ∑ q : IsomorphismClass (Args := Args) (α := α),
        Real.exp (q.out.symmetryDeficit - β * energy q) := by
  classical
  letI := Fintype.ofFinite (RelationalModel Args α)
  letI := Fintype.ofFinite (IsomorphismClass (Args := Args) (α := α))
  rw [Chapter2.partition_regroup_by_fibers]
  apply Finset.sum_congr rfl
  intro q _
  rw [class_fiber_card, symmetryDeficit_eq_log_orbit, Real.exp_sub, Real.exp_log]
  · rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
  · letI := (Finite.finite_mulAction_orbit (M := Equiv.Perm α) q.out).fintype
    haveI : Nonempty (MulAction.orbit (Equiv.Perm α) q.out) := ⟨⟨q.out, MulAction.mem_orbit_self _⟩⟩
    exact_mod_cast (Nat.card_pos (α := MulAction.orbit (Equiv.Perm α) q.out))

end RelationalModel

/-- A binary structure retains one symbol for each specified relation. -/
def RelStructure.toModel {α : Type*} (S : RelStructure α) :
    RelationalModel (fun _ : S.relations => Fin 2) α :=
  ⟨fun R => {t | (t 0, t 1) ∈ R.val}⟩

theorem RelStructure.autSet_eq_model_aut {α : Type*} (S : RelStructure α) :
    S.AutSet = (S.toModel.Aut : Set (Equiv.Perm α)) := by
  ext σ
  change σ ∈ S.AutSet ↔ σ ∈ S.toModel.Aut
  rw [RelationalModel.mem_aut_iff]
  constructor
  · intro h R t
    have heq := h R.val R.property
    have hh := Set.ext_iff.mp heq (σ (t 0), σ (t 1))
    simpa [relMap, RelStructure.toModel, Function.comp_def] using hh.symm
  · intro h R hR
    ext p
    have hh := h ⟨R, hR⟩ ![σ.symm p.1, σ.symm p.2]
    simpa [RelStructure.toModel, Function.comp_def, relMap] using hh.symm

theorem symmetryDeficit_eq_log_orbit {α : Type*} [Finite α] (S : RelStructure α) :
    S.symmetryDeficit =
      Real.log (Nat.card (MulAction.orbit (Equiv.Perm α) S.toModel)) := by
  rw [← RelationalModel.symmetryDeficit_eq_log_orbit]
  unfold RelStructure.symmetryDeficit RelStructure.symmetryMultiplicity
    RelationalModel.symmetryDeficit
  rw [S.autSet_eq_model_aut]
  rfl

namespace Chapter4

/-- Relations and operation graphs share a single indexed relational model. -/
def AlgRelStructure.toModel {α : Type*} (A : AlgRelStructure α) :
    RelationalModel (fun i : A.relations ⊕ A.operations =>
      match i with | .inl _ => Fin 2 | .inr _ => Fin 3) α :=
  ⟨fun i => match i with
    | .inl R => {t | (t 0, t 1) ∈ R.val}
    | .inr μ => {t | t 2 = μ.val (t 0) (t 1)}⟩

theorem AlgRelStructure.autSet_eq_model_aut {α : Type*} (A : AlgRelStructure α) :
    A.AutSet = (A.toModel.Aut : Set (Equiv.Perm α)) := by
  ext σ
  change σ ∈ A.AutSet ↔ σ ∈ A.toModel.Aut
  rw [RelationalModel.mem_aut_iff]
  constructor
  · intro h i
    cases i with
    | inl R =>
      intro t
      have hh := Set.ext_iff.mp (h.1 R.val R.property) (σ (t 0), σ (t 1))
      simpa [relMap, AlgRelStructure.toModel, Function.comp_def] using hh.symm
    | inr μ =>
      intro t
      change σ (t 2) = μ.val (σ (t 0)) (σ (t 1)) ↔ t 2 = μ.val (t 0) (t 1)
      rw [← h.2 μ.val μ.property]
      exact σ.injective.eq_iff
  · intro h
    constructor
    · intro R hR
      ext p
      have hh := h (.inl ⟨R, hR⟩) ![σ.symm p.1, σ.symm p.2]
      simpa [AlgRelStructure.toModel, Function.comp_def, relMap] using hh.symm
    · intro μ hμ x y
      exact (h (.inr ⟨μ, hμ⟩) ![x, y, μ x y]).2 rfl

theorem alg_autSet_eq_action_stabilizer {α : Type*} (A : AlgRelStructure α) :
    A.AutSet = (MulAction.stabilizer (Equiv.Perm α) A.toModel : Set (Equiv.Perm α)) :=
  A.autSet_eq_model_aut

def AlgRelStructure.Stabilizer {α : Type*} (A : AlgRelStructure α) : Set (Equiv.Perm α) :=
  MulAction.stabilizer (Equiv.Perm α) A.toModel

theorem alg_autSet_eq_stabilizer {α : Type*} (A : AlgRelStructure α) :
    A.AutSet = A.Stabilizer := alg_autSet_eq_action_stabilizer A

end Chapter4

end
end SymmetryMonograph
