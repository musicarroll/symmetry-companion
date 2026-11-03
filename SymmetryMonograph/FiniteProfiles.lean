import SymmetryMonograph.Chapter2

set_option linter.style.header false

namespace SymmetryMonograph.Chapter3
noncomputable section
open scoped BigOperators

/-- In disjoint blocks, a microscopic configuration chooses a subset of the
available relation positions in each block. Directed pairs and diagonal loops
are included when supplied as positions; symmetric graph constraints need a
different choice of independent positions. -/
abbrev BlockConfiguration {ι : Type*} (Positions : ι → Type*) :=
  ∀ i, Finset (Positions i)

def blockProfile {ι : Type*} {Positions : ι → Type*}
    (R : BlockConfiguration Positions) : ι → ℕ := fun i => (R i).card

theorem blockProfile_fiber_card {ι : Type*} [Fintype ι]
    (Positions : ι → Type*) [∀ i, Fintype (Positions i)] (m : ι → ℕ) :
    Nat.card {R : BlockConfiguration Positions // blockProfile R = m} =
      ∏ i, (Fintype.card (Positions i)).choose (m i) := by
  classical
  let e : {R : BlockConfiguration Positions // blockProfile R = m} ≃
      (∀ i, {s : Finset (Positions i) // s.card = m i}) := {
    toFun := fun R i => ⟨R.val i, congrFun R.property i⟩
    invFun := fun R => ⟨fun i => (R i).val, funext (fun i => (R i).property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Fintype.card_finset_len]

/-- The book's n_a n_b count is the cardinality of a directed block rectangle. -/
theorem directed_block_positions_card (na nb : ℕ) :
    Fintype.card (Fin na × Fin nb) = na * nb := by simp

end
end SymmetryMonograph.Chapter3
