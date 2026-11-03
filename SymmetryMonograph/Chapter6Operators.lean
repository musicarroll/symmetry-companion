import SymmetryMonograph.Chapter6

set_option linter.style.header false

namespace SymmetryMonograph.Chapter6
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every bounded operator, hence every density operator, is fixed by scalar
unitary conjugation. This applies in infinite-dimensional Hilbert spaces too. -/
theorem scalar_unitary_conjugation (T : E →L[ℂ] E) (z : ℂ) (hz : ‖z‖ = 1) :
    (z • (1 : E →L[ℂ] E)) * T * star (z • (1 : E →L[ℂ] E)) = T := by
  have hz' : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  simp only [star_smul, star_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    smul_smul]
  rw [mul_comm, hz', one_smul]

def phaseOperator (θ : ℝ) : E →L[ℂ] E :=
  Complex.exp ((θ : ℂ) * Complex.I) • 1

theorem phase_conjugation_invariant (T : E →L[ℂ] E) (θ : ℝ) :
    phaseOperator θ * T * star (phaseOperator θ) = T :=
  scalar_unitary_conjugation T _ (Complex.norm_exp_ofReal_mul_I θ)

/-- On the fixed-N sector the phase is Nθ. For the one-particle reduced
operator it is θ; both conjugations are the identity, independently of the
partial-trace construction and of any condensation hypothesis. -/
theorem number_conserving_invariance {E₁ : Type*} [NormedAddCommGroup E₁]
    [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    (Γ : E →L[ℂ] E) (γ : E₁ →L[ℂ] E₁) (N : ℕ) (θ : ℝ) :
    phaseOperator (N * θ) * Γ * star (phaseOperator (N * θ)) = Γ ∧
    phaseOperator θ * γ * star (phaseOperator θ) = γ :=
  ⟨phase_conjugation_invariant Γ _, phase_conjugation_invariant γ _⟩

end
end SymmetryMonograph.Chapter6
