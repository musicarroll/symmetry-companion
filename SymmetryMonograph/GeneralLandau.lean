import SymmetryMonograph.Chapter3Landau

set_option linter.style.header false

namespace SymmetryMonograph.Chapter3
noncomputable section
open Filter Asymptotics Set Topology

def contrastFreeEnergy (β J m d : ℝ) : ℝ :=
  -2 * β * J * d ^ 2 - binaryEntropy (m + d) - binaryEntropy (m - d)

def contrastLandauPolynomial (β J m d : ℝ) : ℝ :=
  -2 * binaryEntropy m + (1 / (m * (1 - m)) - 2 * β * J) * d ^ 2 -
    (1 / 12) * binaryEntropyFourthFormula m * d ^ 4

/-- Rescaling the centered entropy pair isolates the contribution from mass m. -/
theorem scaled_centered_entropy {m d : ℝ} (hm : 0 < m) (hd : |d| < m) :
    m * (symmetricContrastFreeEnergy 0 0 (d / (2 * m)) -
      symmetricContrastFreeEnergy 0 0 0) =
      (m + d) * Real.log (m + d) + (m - d) * Real.log (m - d) -
        2 * m * Real.log m := by
  have hm0 := hm.ne'
  have hp : m + d ≠ 0 := ne_of_gt (by linarith [(abs_lt.mp hd).1])
  have hn : m - d ≠ 0 := ne_of_gt (by linarith [(abs_lt.mp hd).2])
  have h2m : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hm0
  have ha : (1 : ℝ) / 2 + d / (2 * m) = (m + d) / (2 * m) := by field_simp
  have hb : (1 : ℝ) / 2 - d / (2 * m) = (m - d) / (2 * m) := by field_simp
  have hc : (1 : ℝ) - (1 / 2 + d / (2 * m)) = 1 / 2 - d / (2 * m) := by ring
  have he : (1 : ℝ) - (1 / 2 - d / (2 * m)) = 1 / 2 + d / (2 * m) := by ring
  simp only [symmetricContrastFreeEnergy, binaryEntropy, mul_zero, zero_mul,
    zero_sub, add_zero, sub_zero, hc, he]
  norm_num only
  rw [ha, hb, Real.log_div hp h2m, Real.log_div hn h2m,
    Real.log_mul (by norm_num) hm0]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [Real.log_one]
  field_simp
  ring

theorem contrastFreeEnergy_eq_scaled_centered {β J m d : ℝ}
    (hm : 0 < m) (hm1 : m < 1) (hd : |d| < min m (1 - m)) :
    contrastFreeEnergy β J m d = -2 * binaryEntropy m - 2 * β * J * d ^ 2 +
      m * (symmetricContrastFreeEnergy 0 0 (d / (2 * m)) -
        symmetricContrastFreeEnergy 0 0 0) +
      (1 - m) * (symmetricContrastFreeEnergy 0 0 (d / (2 * (1 - m))) -
        symmetricContrastFreeEnergy 0 0 0) := by
  rw [scaled_centered_entropy hm (lt_min_iff.mp hd).1,
    scaled_centered_entropy (by linarith) (lt_min_iff.mp hd).2]
  unfold contrastFreeEnergy binaryEntropy
  rw [show 1 - (m + d) = 1 - m - d by ring,
    show 1 - (m - d) = 1 - m + d by ring]
  ring

theorem contrastLandauRemainder_eq_scaled {β J m d : ℝ}
    (hm : 0 < m) (hm1 : m < 1) (hd : |d| < min m (1 - m)) :
    contrastFreeEnergy β J m d - contrastLandauPolynomial β J m d =
      m * symmetricContrastLandauRemainder 0 0 (d / (2 * m)) +
      (1 - m) * symmetricContrastLandauRemainder 0 0 (d / (2 * (1 - m))) := by
  rw [contrastFreeEnergy_eq_scaled_centered hm hm1 hd]
  unfold contrastLandauPolynomial symmetricContrastLandauRemainder
    symmetricContrastLandauJet landauQuadraticCoefficient landauQuarticCoefficient
  rw [← binaryEntropy_fourthFormula_eq_split hm.ne' (by linarith)]
  field_simp [hm.ne', show 1 - m ≠ 0 by linarith]
  ring

theorem scaled_symmetricRemainder_isBigO (c : ℝ) :
    (fun d => symmetricContrastLandauRemainder 0 0 (c * d)) =O[𝓝 0]
      (fun d : ℝ => d ^ 6) := by
  have ht : Tendsto (fun d : ℝ => c * d) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (fun d : ℝ => d) (𝓝 0) (𝓝 0)))
  have h := (symmetricContrastLandauRemainder_isBigO 0 0).comp_tendsto ht
  have hp : (fun d : ℝ => (c * d) ^ 6) =O[𝓝 0] (fun d : ℝ => d ^ 6) := by
    simpa only [mul_pow] using
      (isBigO_refl (fun d : ℝ => d ^ 6) (𝓝 0)).const_mul_left (c ^ 6)
  exact h.trans hp

/-- Full general-mean local Landau expansion, with an actual sixth-order remainder. -/
theorem contrastLandauRemainder_isBigO {β J m : ℝ} (hm : 0 < m) (hm1 : m < 1) :
    (fun d => contrastFreeEnergy β J m d - contrastLandauPolynomial β J m d)
      =O[𝓝 0] (fun d : ℝ => d ^ 6) := by
  have h := ((scaled_symmetricRemainder_isBigO (1 / (2 * m))).const_mul_left m).add
    ((scaled_symmetricRemainder_isBigO (1 / (2 * (1 - m)))).const_mul_left (1 - m))
  apply h.congr' _ EventuallyEq.rfl
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
    (show 0 < min m (1 - m) by exact lt_min hm (by linarith))] with d hd
  have hd' : |d| < min m (1 - m) := by simpa [Real.dist_eq] using hd
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    (contrastLandauRemainder_eq_scaled hm hm1 hd').symm

end
end SymmetryMonograph.Chapter3
