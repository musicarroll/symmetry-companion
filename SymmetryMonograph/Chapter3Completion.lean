import SymmetryMonograph.Chapter3Landau

set_option linter.style.header false

/-! Completion of the derivative, minimum, and inverse-branch correspondences. -/
namespace SymmetryMonograph.Chapter3
noncomputable section
open Filter Set Topology

/-- The unrefined centered point is stationary only at zero coupling. -/
theorem twoBlock_centered_critical_iff (β J : ℝ) :
    twoBlockCriticalEquations β J (1 / 2) (1 / 2) ↔ β * J = 0 := by
  norm_num [twoBlockCriticalEquations, logOdds]

theorem twoBlockGradient_deriv {β J p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun x => -β * J * x - logOdds x)
      (1 / (p * (1 - p)) - β * J) p := by
  have h := ((hasDerivAt_id p).const_mul (-β * J)).sub
    (hasDerivAt_logOdds_of_interior hp0 hp1)
  exact h.congr_deriv (by ring)

theorem twoBlockHessian_is_gradient_jacobian {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x => -β * J * x - logOdds x)
        (1 / (p * (1 - p)) - β * J) p ∧
    HasDerivAt (fun _ : ℝ => -β * J * p - logOdds p) 0 q ∧
    HasDerivAt (fun _ : ℝ => -β * J * q - logOdds q) 0 p ∧
    HasDerivAt (fun y => -β * J * y - logOdds y)
        (1 / (q * (1 - q)) - β * J) q :=
  ⟨twoBlockGradient_deriv hp0 hp1, hasDerivAt_const _ _,
    hasDerivAt_const _ _, twoBlockGradient_deriv hq0 hq1⟩

def twoBlockQuadraticForm (β J p q : ℝ) (v : ℝ × ℝ) : ℝ :=
  v.1 * (twoBlockHessian β J p q v).1 + v.2 * (twoBlockHessian β J p q v).2

theorem twoBlock_hessian_posDef_at_half {β J : ℝ}
    (hJ : 0 < J) (hβ : β < 4 / J) (v : ℝ × ℝ) (hv : v ≠ 0) :
    0 < twoBlockQuadraticForm β J (1 / 2) (1 / 2) v := by
  have hK : β * J < 4 := (lt_div_iff₀ hJ).mp hβ
  have hv2 : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    have hne : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
      by_contra h
      apply hv
      push Not at h
      exact Prod.ext h.1 h.2
    rcases hne with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg v.1, sq_nonneg v.2]
  have : 0 < (4 - β * J) * (v.1 ^ 2 + v.2 ^ 2) := mul_pos (by linarith) hv2
  norm_num [twoBlockQuadraticForm, twoBlockHessian]
  nlinarith

theorem twoBlock_hessian_negative_antisymmetric_at_half {β J : ℝ}
    (hJ : 0 < J) (hβ : 4 / J < β) :
    twoBlockQuadraticForm β J (1 / 2) (1 / 2) antisymmetricMode < 0 := by
  have hK : 4 < β * J := (div_lt_iff₀ hJ).mp hβ
  norm_num [twoBlockQuadraticForm, twoBlockHessian, antisymmetricMode]
  linarith

theorem hasDerivAt_quartic (A B d : ℝ) :
    HasDerivAt (quarticApproximation A B) (2 * A * d + 4 * B * d ^ 3) d := by
  have h := (((hasDerivAt_id d).pow 2).const_mul A).add
    (((hasDerivAt_id d).pow 4).const_mul B)
  exact h.congr_deriv (by norm_num; ring)

theorem quartic_zero_not_localMin {A B : ℝ} (hA : A < 0) :
    ¬ IsLocalMin (quarticApproximation A B) 0 := by
  intro hmin
  have hc : ContinuousAt (fun x : ℝ => A + B * x ^ 2) 0 := by fun_prop
  have hn : ∀ᶠ x : ℝ in 𝓝 0, A + B * x ^ 2 < 0 :=
    hc.eventually (gt_mem_nhds (by simpa using hA))
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := eventually_mem_nhdsWithin
  have both : ∀ᶠ x : ℝ in 𝓝[>] 0,
      quarticApproximation A B 0 ≤ quarticApproximation A B x ∧ A + B * x ^ 2 < 0 :=
    (hmin.and hn).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hle, hneg⟩ := (hpos.and both).exists
  have hf : quarticApproximation A B x < 0 := by
    have := mul_neg_of_pos_of_neg (sq_pos_of_pos hx) hneg
    dsimp [quarticApproximation]
    nlinarith
  have hzero : quarticApproximation A B 0 = 0 := by simp [quarticApproximation]
  rw [hzero] at hle
  linarith

theorem quartic_zero_isLocalMax {A B : ℝ} (hA : A < 0) :
    IsLocalMax (quarticApproximation A B) 0 := by
  have hc : ContinuousAt (fun x : ℝ => A + B * x ^ 2) 0 := by fun_prop
  have hn : ∀ᶠ x : ℝ in 𝓝 0, A + B * x ^ 2 < 0 :=
    hc.eventually (gt_mem_nhds (by simpa using hA))
  filter_upwards [hn] with x hx
  have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hx.le
  dsimp [quarticApproximation]
  nlinarith

theorem quartic_localMin_iff_of_pos {A B d : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IsLocalMin (quarticApproximation A B) d ↔ d = 0 := by
  constructor
  · intro h
    have hz := h.hasDerivAt_eq_zero (hasDerivAt_quartic A B d)
    have hfactor : d * (2 * A + 4 * B * d ^ 2) = 0 := by nlinarith [hz]
    have hp : 0 < 2 * A + 4 * B * d ^ 2 := by positivity
    exact (mul_eq_zero.mp hfactor).resolve_right hp.ne'
  · intro h
    have hg := (quartic_unique_min_of_quadratic_pos hA hB).mpr h
    exact Filter.Eventually.of_forall hg

theorem quartic_localMin_iff_of_neg {A B d : ℝ} (hA : A < 0) (hB : 0 < B) :
    IsLocalMin (quarticApproximation A B) d ↔ d ^ 2 = -A / (2 * B) := by
  constructor
  · intro h
    have hd : d ≠ 0 := by
      intro hd
      subst d
      exact quartic_zero_not_localMin hA h
    have hz := h.hasDerivAt_eq_zero (hasDerivAt_quartic A B d)
    have hfactor : d * (2 * A + 4 * B * d ^ 2) = 0 := by nlinarith [hz]
    have h := (mul_eq_zero.mp hfactor).resolve_left hd
    apply (eq_div_iff (by positivity : (2 : ℝ) * B ≠ 0)).mpr
    nlinarith
  · intro h
    exact Filter.Eventually.of_forall
      ((quartic_global_min_iff_sq_eq_of_quadratic_neg hA hB).mpr h)

/-- Passing from the radius to a vector is valid in any nontrivial real normed space. -/
theorem radial_vector_min_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (a b : ℝ) (x : E) :
    (∀ y : E, radialQuartic a b ‖x‖ ≤ radialQuartic a b ‖y‖) ↔
      IsGlobalMinOn (radialQuartic a b) (Ici 0) ‖x‖ := by
  constructor
  · intro h
    refine ⟨norm_nonneg x, ?_⟩
    intro r hr
    obtain ⟨y, hy⟩ := exists_norm_eq E hr
    simpa [hy] using h y
  · intro h y
    exact h.2 ‖y‖ (norm_nonneg y)

theorem radial_vector_min_iff_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : E) :
    (∀ y : E, radialQuartic a b ‖x‖ ≤ radialQuartic a b ‖y‖) ↔ x = 0 := by
  rw [radial_vector_min_iff, radial_quartic_unique_min_of_quadratic_pos ha hb, norm_eq_zero]

theorem radial_vector_min_iff_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {a b : ℝ} (ha : a < 0) (hb : 0 < b) (x : E) :
    (∀ y : E, radialQuartic a b ‖x‖ ≤ radialQuartic a b ‖y‖) ↔
      ‖x‖ = Real.sqrt (-a / (2 * b)) := by
  rw [radial_vector_min_iff, radial_quartic_global_min_iff_sq_eq_of_quadratic_neg ha hb]
  have hv : 0 ≤ -a / (2 * b) := div_nonneg (neg_nonneg.mpr ha.le) (by positivity)
  constructor
  · rintro ⟨hx, hs⟩
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg (-a / (2 * b))]
  · intro h
    exact ⟨norm_nonneg x, by rw [h, Real.sq_sqrt hv]⟩

theorem exists_exactBrokenContrast {K : ℝ} (hK : 2 < K ∧ K < 2 * Real.log 3) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 4 ∧ exactContrastCoupling d = K := by
  obtain ⟨d, hd0, hdq, hs, _⟩ := exists_exact_broken_stationary_pair
    (β := K) (J := 1) (by simpa using hK.1) (by simpa using hK.2)
  refine ⟨d, hd0, hdq, ?_⟩
  have hroot := (refinedStationary_symmetricContrast_iff (by linarith) (by linarith)).mp hs
  have heq := (symmetricContrastFirst_eq_zero_iff_coupling hd0 (by linarith)).mp hroot
  simpa using heq.symm

/-- The unique positive broken contrast on the near-critical coupling interval;
zero outside that interval is only a total-function convention. -/
def exactBrokenContrast (K : ℝ) : ℝ :=
  if hK : 2 < K ∧ K < 2 * Real.log 3 then
    Classical.choose (exists_exactBrokenContrast hK) else 0

theorem exactBrokenContrast_spec {K : ℝ} (hK : 2 < K ∧ K < 2 * Real.log 3) :
    0 < exactBrokenContrast K ∧ exactBrokenContrast K < 1 / 4 ∧
      exactContrastCoupling (exactBrokenContrast K) = K := by
  simpa only [exactBrokenContrast, dif_pos hK] using
    Classical.choose_spec (exists_exactBrokenContrast hK)

theorem critical_lt_upper : (2 : ℝ) < 2 * Real.log 3 := by
  have h := two_lt_exactContrastCoupling (d := 1 / 4) (by norm_num) (by norm_num)
  norm_num [exactContrastCoupling] at h
  linarith

theorem eventually_exactBrokenContrast_spec :
    ∀ᶠ K : ℝ in 𝓝[>] 2, 0 < exactBrokenContrast K ∧
      exactBrokenContrast K < 1 / 4 ∧ exactContrastCoupling (exactBrokenContrast K) = K := by
  have hid : Tendsto (fun K : ℝ => K) (𝓝[>] 2) (𝓝 2) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin,
    hid.eventually_lt tendsto_const_nhds critical_lt_upper] with K hK0 hK1
  exact exactBrokenContrast_spec ⟨hK0, hK1⟩

theorem tendsto_exactBrokenContrast : Tendsto exactBrokenContrast (𝓝[>] 2) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_exactBrokenContrast_spec] with K hK
    linarith [hK.1]
  · intro ε hε
    let e : ℝ := min (ε / 2) (1 / 4)
    have he0 : 0 < e := lt_min (by linarith) (by norm_num)
    have hehalf : e < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have heε : e < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hc := two_lt_exactContrastCoupling he0 hehalf
    have hid : Tendsto (fun K : ℝ => K) (𝓝[>] 2) (𝓝 2) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards [eventually_exactBrokenContrast_spec,
      hid.eventually_lt tendsto_const_nhds hc] with K hK hKe
    have hd : exactBrokenContrast K < e := by
      by_contra h
      have hmono := exactContrastCoupling_strictMonoOn.monotoneOn
        ⟨he0, hehalf⟩ ⟨hK.1, by linarith [hK.2.1]⟩ (le_of_not_gt h)
      rw [hK.2.2] at hmono
      linarith
    exact hd.trans heε

/-- The book's limit in the coupling variable, including the inverse-branch step. -/
theorem tendsto_exactBrokenContrast_sq_div_sub_two :
    Tendsto (fun K : ℝ => exactBrokenContrast K ^ 2 / (K - 2))
      (𝓝[>] 2) (𝓝 (3 / 8)) := by
  have hin : Tendsto exactBrokenContrast (𝓝[>] 2) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_exactBrokenContrast,
      eventually_exactBrokenContrast_spec.mono (fun _ h => h.1)⟩
  apply (tendsto_exactContrast_sq_div_coupling_sub_two.comp hin).congr'
  filter_upwards [eventually_exactBrokenContrast_spec] with K hK
  simp only [Function.comp_def, hK.2.2]

end
end SymmetryMonograph.Chapter3
