import SymmetryMonograph.Chapter3Completion

set_option linter.style.header false

namespace SymmetryMonograph.Chapter3
noncomputable section
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fieldEnergy (κ a b : ℝ) (φ : ℝ → E) : ℝ :=
  ∫ x in (0 : ℝ)..1, κ / 2 * ‖deriv φ x‖ ^ 2 + radialQuartic a b ‖φ x‖

/-- Orthogonal invariance includes the derivative term, not just the potential. -/
theorem fieldEnergy_orthogonal_invariant (κ a b : ℝ) (R : E ≃ₗᵢ[ℝ] E)
    (φ : ℝ → E) (hφ : Differentiable ℝ φ) :
    fieldEnergy κ a b (fun x => R (φ x)) = fieldEnergy κ a b φ := by
  have hd : ∀ x, deriv (fun y => R (φ y)) x = R (deriv φ x) := by
    intro x
    exact (R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      x (hφ x).hasDerivAt).deriv
  unfold fieldEnergy
  congr 1
  funext x
  rw [hd, R.norm_map, R.norm_map]

/-- Exact local potential expansion, with the cubic and quartic terms retained.
Here t is the squared transverse norm. Its absence from the quadratic term is
the algebraic Goldstone conclusion; no dynamical spectral claim is made. -/
theorem radial_quartic_vacuum_expansion (a b v σ t : ℝ) (hv : a + 2 * b * v ^ 2 = 0) :
    a * ((v + σ) ^ 2 + t) + b * ((v + σ) ^ 2 + t) ^ 2 =
      a * v ^ 2 + b * v ^ 4 + (-2 * a) * σ ^ 2 +
        4 * b * v * σ * (σ ^ 2 + t) + b * (σ ^ 2 + t) ^ 2 := by
  calc
    _ = a * v ^ 2 + b * v ^ 4 + (-2 * a) * σ ^ 2 +
        4 * b * v * σ * (σ ^ 2 + t) + b * (σ ^ 2 + t) ^ 2 +
        (a + 2 * b * v ^ 2) * (2 * v * σ + 3 * σ ^ 2 + t) := by ring
    _ = _ := by rw [hv]; ring

end
end SymmetryMonograph.Chapter3
