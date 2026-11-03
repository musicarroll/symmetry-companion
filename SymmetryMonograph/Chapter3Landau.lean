import SymmetryMonograph.Chapter3
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

set_option linter.style.header false

/-!
# Chapter 3: the exact Landau jet of the refined two-block model

This file connects the algebraic coefficients used in the Landau discussion to
actual successive derivatives, proves a controlled sixth-order remainder, and
uses the exact stationarity equation to establish a symmetry-related nonzero
stationary pair immediately above the critical coupling.
-/

namespace SymmetryMonograph.Chapter3

open Filter Asymptotics Set
open scoped BigOperators Topology

noncomputable section

/-- The third derivative formula for binary entropy on the open unit interval. -/
def binaryEntropyThirdFormula (u : ℝ) : ℝ :=
  1 / u ^ 2 - 1 / (1 - u) ^ 2

/-- The refined free energy restricted to the symmetric contrast line
`(p, q) = (1 / 2 + d, 1 / 2 - d)`. -/
def symmetricContrastFreeEnergy (β J d : ℝ) : ℝ :=
  -2 * β * J * d ^ 2 -
    binaryEntropy (1 / 2 + d) - binaryEntropy (1 / 2 - d)

/-- The first derivative formula for the symmetric contrast slice. -/
def symmetricContrastFirst (β J d : ℝ) : ℝ :=
  -4 * β * J * d - logOdds (1 / 2 + d) + logOdds (1 / 2 - d)

/-- The second derivative formula for the symmetric contrast slice. -/
def symmetricContrastSecond (β J d : ℝ) : ℝ :=
  -4 * β * J - binaryEntropySecondFormula (1 / 2 + d) -
    binaryEntropySecondFormula (1 / 2 - d)

/-- The third derivative formula for the symmetric contrast slice. -/
def symmetricContrastThird (d : ℝ) : ℝ :=
  -binaryEntropyThirdFormula (1 / 2 + d) +
    binaryEntropyThirdFormula (1 / 2 - d)

/-- The fourth derivative formula for the symmetric contrast slice. -/
def symmetricContrastFourth (d : ℝ) : ℝ :=
  -binaryEntropyFourthFormula (1 / 2 + d) -
    binaryEntropyFourthFormula (1 / 2 - d)

/-- The quadratic coefficient in the Landau polynomial at the symmetric state. -/
def landauQuadraticCoefficient (β J : ℝ) : ℝ :=
  4 - 2 * β * J

/-- The quartic coefficient in the Landau polynomial at the symmetric state. -/
def landauQuarticCoefficient : ℝ :=
  8 / 3

/-- The fourth-order Landau jet of the symmetric contrast slice at `d = 0`. -/
def symmetricContrastLandauJet (β J d : ℝ) : ℝ :=
  symmetricContrastFreeEnergy β J 0 +
    landauQuadraticCoefficient β J * d ^ 2 + landauQuarticCoefficient * d ^ 4

/-- The difference between the exact symmetric contrast free energy and its
fourth-order Landau jet. -/
def symmetricContrastLandauRemainder (β J d : ℝ) : ℝ :=
  symmetricContrastFreeEnergy β J d - symmetricContrastLandauJet β J d

/-- The exact first derivative of the Landau remainder on `|d| < 1 / 2`.
It is independent of the parameters because the energy term is quadratic. -/
def symmetricContrastLandauRemainderFirst (d : ℝ) : ℝ :=
  2 * Real.log ((1 + 2 * d) / (1 - 2 * d)) - 8 * d - (32 / 3) * d ^ 3

/-- The first coordinate of the gradient of the refined two-block free energy. -/
def refinedGradientP (β J p q : ℝ) : ℝ :=
  -β * J * (p - q) - logOdds p

/-- The second coordinate of the gradient of the refined two-block free energy. -/
def refinedGradientQ (β J p q : ℝ) : ℝ :=
  β * J * (p - q) - logOdds q

theorem symmetricContrastFreeEnergy_eq_refined (β J d : ℝ) :
    symmetricContrastFreeEnergy β J d =
      refinedTwoBlockFreeEnergy β J (1 / 2 + d) (1 / 2 - d) := by
  unfold symmetricContrastFreeEnergy refinedTwoBlockFreeEnergy
  ring

theorem hasDerivAt_binaryEntropySecondFormula {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt binaryEntropySecondFormula (binaryEntropyThirdFormula u) u := by
  have hu : u ≠ 0 := ne_of_gt h0
  have h1u : 1 - u ≠ 0 := by linarith
  have hg : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * u) u := by
    have h := (hasDerivAt_id u).mul
      ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u))
    rw [show id * ((fun _ : ℝ => 1) - id) =
        (fun x : ℝ => x * (1 - x)) by funext x; rfl] at h
    exact h.congr_deriv (by simp [id]; ring)
  have hgne : u * (1 - u) ≠ 0 := mul_ne_zero hu h1u
  have hinv := hg.inv hgne
  have hneg := hinv.neg
  rw [show (-(fun x : ℝ => x * (1 - x))⁻¹) = binaryEntropySecondFormula by
    funext x
    simp [binaryEntropySecondFormula, div_eq_mul_inv]] at hneg
  exact hneg.congr_deriv (by
    unfold binaryEntropyThirdFormula
    field_simp [hu, h1u]
    ring)

theorem hasDerivAt_binaryEntropyThirdFormula {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt binaryEntropyThirdFormula (binaryEntropyFourthFormula u) u := by
  have hu : u ≠ 0 := ne_of_gt h0
  have h1u : 1 - u ≠ 0 := by linarith
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have h1u2 : (1 - u) ^ 2 ≠ 0 := pow_ne_zero 2 h1u
  have hleftDen : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    have h := (hasDerivAt_id u).pow 2
    rw [show id ^ 2 = (fun x : ℝ => x ^ 2) by funext x; rfl] at h
    exact h.congr_deriv (by simp [id])
  have hleft : HasDerivAt (fun x : ℝ => 1 / x ^ 2) (-2 / u ^ 3) u := by
    have h := (hasDerivAt_const u (1 : ℝ)).div hleftDen hu2
    rw [show (fun _ : ℝ => 1) / (fun x : ℝ => x ^ 2) =
        (fun x : ℝ => 1 / x ^ 2) by funext x; rfl] at h
    exact h.congr_deriv (by field_simp [hu]; ring)
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    have h := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
    rw [show (fun _ : ℝ => 1) - id = (fun x : ℝ => 1 - x) by funext x; rfl] at h
    simpa using h
  have hrightDen :
      HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (-2 * (1 - u)) u := by
    have h := hsub.pow 2
    rw [show (fun x : ℝ => 1 - x) ^ 2 =
        (fun x : ℝ => (1 - x) ^ 2) by funext x; rfl] at h
    exact h.congr_deriv (by ring)
  have hright :
      HasDerivAt (fun x : ℝ => 1 / (1 - x) ^ 2) (2 / (1 - u) ^ 3) u := by
    have h := (hasDerivAt_const u (1 : ℝ)).div hrightDen h1u2
    rw [show (fun _ : ℝ => 1) / (fun x : ℝ => (1 - x) ^ 2) =
        (fun x : ℝ => 1 / (1 - x) ^ 2) by funext x; rfl] at h
    exact h.congr_deriv (by field_simp [h1u]; ring)
  have hdiff := hleft.sub hright
  rw [show (fun x : ℝ => 1 / x ^ 2) - (fun x : ℝ => 1 / (1 - x) ^ 2) =
      binaryEntropyThirdFormula by funext x; rfl] at hdiff
  exact hdiff.congr_deriv (by
    rw [← binaryEntropy_fourthFormula_eq_split hu h1u])

theorem binaryEntropy_successive_derivatives_through_four {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt binaryEntropy (logOdds u) u ∧
      HasDerivAt logOdds (binaryEntropySecondFormula u) u ∧
      HasDerivAt binaryEntropySecondFormula (binaryEntropyThirdFormula u) u ∧
      HasDerivAt binaryEntropyThirdFormula (binaryEntropyFourthFormula u) u := by
  exact ⟨hasDerivAt_binaryEntropy_of_interior h0 h1,
    hasDerivAt_logOdds_binaryEntropySecondFormula h0 h1,
    hasDerivAt_binaryEntropySecondFormula h0 h1,
    hasDerivAt_binaryEntropyThirdFormula h0 h1⟩

theorem refinedGradientP_deriv_p {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun x => refinedGradientP β J x q)
      (1 / (p * (1 - p)) - β * J) p := by
  have hlinear : HasDerivAt (fun x : ℝ => -β * J * (x - q)) (-β * J) p := by
    have hsub : HasDerivAt (fun x : ℝ => x - q) 1 p := by
      have h := (hasDerivAt_id p).sub (hasDerivAt_const p q)
      rw [show id - (fun _ : ℝ => q) = (fun x : ℝ => x - q) by funext x; rfl] at h
      simpa using h
    exact (hsub.const_mul (-β * J)).congr_deriv (by ring)
  have hlog := hasDerivAt_logOdds_binaryEntropySecondFormula hp0 hp1
  have h := hlinear.sub hlog
  rw [show (fun x : ℝ => -β * J * (x - q)) - logOdds =
      (fun x => refinedGradientP β J x q) by funext x; rfl] at h
  exact h.congr_deriv (by
    unfold binaryEntropySecondFormula
    ring)

theorem refinedGradientP_deriv_q (β J p q : ℝ) :
    HasDerivAt (fun y => refinedGradientP β J p y) (β * J) q := by
  have hsub : HasDerivAt (fun y : ℝ => p - y) (-1) q := by
    have h := (hasDerivAt_const q p).sub (hasDerivAt_id q)
    rw [show (fun _ : ℝ => p) - id = (fun y : ℝ => p - y) by funext y; rfl] at h
    simpa using h
  have hlinear := hsub.const_mul (-β * J)
  have h := hlinear.sub (hasDerivAt_const q (logOdds p))
  rw [show (fun y : ℝ => -β * J * (p - y)) - (fun _ : ℝ => logOdds p) =
      (fun y => refinedGradientP β J p y) by funext y; rfl] at h
  exact h.congr_deriv (by ring)

theorem refinedGradientQ_deriv_p (β J p q : ℝ) :
    HasDerivAt (fun x => refinedGradientQ β J x q) (β * J) p := by
  have hsub : HasDerivAt (fun x : ℝ => x - q) 1 p := by
    have h := (hasDerivAt_id p).sub (hasDerivAt_const p q)
    rw [show id - (fun _ : ℝ => q) = (fun x : ℝ => x - q) by funext x; rfl] at h
    simpa using h
  have hlinear := hsub.const_mul (β * J)
  have h := hlinear.sub (hasDerivAt_const p (logOdds q))
  rw [show (fun x : ℝ => β * J * (x - q)) - (fun _ : ℝ => logOdds q) =
      (fun x => refinedGradientQ β J x q) by funext x; rfl] at h
  exact h.congr_deriv (by ring)

theorem refinedGradientQ_deriv_q {β J p q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun y => refinedGradientQ β J p y)
      (1 / (q * (1 - q)) - β * J) q := by
  have hlinear : HasDerivAt (fun y : ℝ => β * J * (p - y)) (-β * J) q := by
    have hsub : HasDerivAt (fun y : ℝ => p - y) (-1) q := by
      have h := (hasDerivAt_const q p).sub (hasDerivAt_id q)
      rw [show (fun _ : ℝ => p) - id = (fun y : ℝ => p - y) by funext y; rfl] at h
      simpa using h
    exact (hsub.const_mul (β * J)).congr_deriv (by ring)
  have hlog := hasDerivAt_logOdds_binaryEntropySecondFormula hq0 hq1
  have h := hlinear.sub hlog
  rw [show (fun y : ℝ => β * J * (p - y)) - logOdds =
      (fun y => refinedGradientQ β J p y) by funext y; rfl] at h
  exact h.congr_deriv (by
    unfold binaryEntropySecondFormula
    ring)

theorem refinedHessian_is_gradient_jacobian {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x => refinedGradientP β J x q)
        (1 / (p * (1 - p)) - β * J) p ∧
      HasDerivAt (fun y => refinedGradientP β J p y) (β * J) q ∧
      HasDerivAt (fun x => refinedGradientQ β J x q) (β * J) p ∧
      HasDerivAt (fun y => refinedGradientQ β J p y)
        (1 / (q * (1 - q)) - β * J) q := by
  exact ⟨refinedGradientP_deriv_p hp0 hp1, refinedGradientP_deriv_q β J p q,
    refinedGradientQ_deriv_p β J p q, refinedGradientQ_deriv_q hq0 hq1⟩

theorem hasDerivAt_symmetricContrastFreeEnergy {β J d : ℝ}
    (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    HasDerivAt (symmetricContrastFreeEnergy β J)
      (symmetricContrastFirst β J d) d := by
  have hp0 : 0 < 1 / 2 + d := by linarith
  have hp1 : 1 / 2 + d < 1 := by linarith
  have hq0 : 0 < 1 / 2 - d := by linarith
  have hq1 : 1 / 2 - d < 1 := by linarith
  have hpCurve : HasDerivAt (fun x : ℝ => 1 / 2 + x) 1 d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).add (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) + id =
        (fun x : ℝ => 1 / 2 + x) by funext x; rfl] at h
    simpa using h
  have hqCurve : HasDerivAt (fun x : ℝ => 1 / 2 - x) (-1) d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) - id =
        (fun x : ℝ => 1 / 2 - x) by funext x; rfl] at h
    simpa using h
  have hpEntropy := (hasDerivAt_binaryEntropy_of_interior hp0 hp1).comp d hpCurve
  have hqEntropy := (hasDerivAt_binaryEntropy_of_interior hq0 hq1).comp d hqCurve
  have hsquare : HasDerivAt (fun x : ℝ => x ^ 2) (2 * d) d := by
    have h := (hasDerivAt_id d).pow 2
    rw [show id ^ 2 = (fun x : ℝ => x ^ 2) by funext x; rfl] at h
    exact h.congr_deriv (by simp [id])
  have henergy := hsquare.const_mul (-2 * β * J)
  have h := (henergy.sub hpEntropy).sub hqEntropy
  rw [show (fun y : ℝ => -2 * β * J * y ^ 2) -
      binaryEntropy ∘ (fun x : ℝ => 1 / 2 + x) -
      binaryEntropy ∘ (fun x : ℝ => 1 / 2 - x) =
      symmetricContrastFreeEnergy β J by funext x; rfl] at h
  exact h.congr_deriv (by unfold symmetricContrastFirst; ring)

theorem hasDerivAt_symmetricContrastFirst {β J d : ℝ}
    (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    HasDerivAt (symmetricContrastFirst β J)
      (symmetricContrastSecond β J d) d := by
  have hp0 : 0 < 1 / 2 + d := by linarith
  have hp1 : 1 / 2 + d < 1 := by linarith
  have hq0 : 0 < 1 / 2 - d := by linarith
  have hq1 : 1 / 2 - d < 1 := by linarith
  have hpCurve : HasDerivAt (fun x : ℝ => 1 / 2 + x) 1 d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).add (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) + id =
        (fun x : ℝ => 1 / 2 + x) by funext x; rfl] at h
    simpa using h
  have hqCurve : HasDerivAt (fun x : ℝ => 1 / 2 - x) (-1) d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) - id =
        (fun x : ℝ => 1 / 2 - x) by funext x; rfl] at h
    simpa using h
  have hpLog := (hasDerivAt_logOdds_binaryEntropySecondFormula hp0 hp1).comp d hpCurve
  have hqLog := (hasDerivAt_logOdds_binaryEntropySecondFormula hq0 hq1).comp d hqCurve
  have hlinear : HasDerivAt (fun x : ℝ => -4 * β * J * x) (-4 * β * J) d := by
    exact ((hasDerivAt_id d).const_mul (-4 * β * J)).congr_deriv (by ring)
  have h := (hlinear.sub hpLog).add hqLog
  rw [show (fun x : ℝ => -4 * β * J * x) -
      logOdds ∘ (fun x : ℝ => 1 / 2 + x) +
      logOdds ∘ (fun x : ℝ => 1 / 2 - x) =
      symmetricContrastFirst β J by funext x; rfl] at h
  exact h.congr_deriv (by unfold symmetricContrastSecond; ring)

theorem hasDerivAt_symmetricContrastSecond {β J d : ℝ}
    (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    HasDerivAt (symmetricContrastSecond β J)
      (symmetricContrastThird d) d := by
  have hp0 : 0 < 1 / 2 + d := by linarith
  have hp1 : 1 / 2 + d < 1 := by linarith
  have hq0 : 0 < 1 / 2 - d := by linarith
  have hq1 : 1 / 2 - d < 1 := by linarith
  have hpCurve : HasDerivAt (fun x : ℝ => 1 / 2 + x) 1 d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).add (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) + id =
        (fun x : ℝ => 1 / 2 + x) by funext x; rfl] at h
    simpa using h
  have hqCurve : HasDerivAt (fun x : ℝ => 1 / 2 - x) (-1) d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) - id =
        (fun x : ℝ => 1 / 2 - x) by funext x; rfl] at h
    simpa using h
  have hpThird := (hasDerivAt_binaryEntropySecondFormula hp0 hp1).comp d hpCurve
  have hqThird := (hasDerivAt_binaryEntropySecondFormula hq0 hq1).comp d hqCurve
  have hconst : HasDerivAt (fun _ : ℝ => -4 * β * J) 0 d :=
    hasDerivAt_const d (-4 * β * J)
  have h := (hconst.sub hpThird).sub hqThird
  rw [show (fun _ : ℝ => -4 * β * J) -
      binaryEntropySecondFormula ∘ (fun x : ℝ => 1 / 2 + x) -
      binaryEntropySecondFormula ∘ (fun x : ℝ => 1 / 2 - x) =
      symmetricContrastSecond β J by funext x; rfl] at h
  exact h.congr_deriv (by unfold symmetricContrastThird; ring)

theorem hasDerivAt_symmetricContrastThird {d : ℝ}
    (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    HasDerivAt symmetricContrastThird (symmetricContrastFourth d) d := by
  have hp0 : 0 < 1 / 2 + d := by linarith
  have hp1 : 1 / 2 + d < 1 := by linarith
  have hq0 : 0 < 1 / 2 - d := by linarith
  have hq1 : 1 / 2 - d < 1 := by linarith
  have hpCurve : HasDerivAt (fun x : ℝ => 1 / 2 + x) 1 d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).add (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) + id =
        (fun x : ℝ => 1 / 2 + x) by funext x; rfl] at h
    simpa using h
  have hqCurve : HasDerivAt (fun x : ℝ => 1 / 2 - x) (-1) d := by
    have h := (hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)
    rw [show (fun _ : ℝ => 1 / 2) - id =
        (fun x : ℝ => 1 / 2 - x) by funext x; rfl] at h
    simpa using h
  have hpFourth := (hasDerivAt_binaryEntropyThirdFormula hp0 hp1).comp d hpCurve
  have hqFourth := (hasDerivAt_binaryEntropyThirdFormula hq0 hq1).comp d hqCurve
  have h := hpFourth.neg.add hqFourth
  rw [show -(binaryEntropyThirdFormula ∘ (fun x : ℝ => 1 / 2 + x)) +
      binaryEntropyThirdFormula ∘ (fun x : ℝ => 1 / 2 - x) =
      symmetricContrastThird by funext x; rfl] at h
  exact h.congr_deriv (by unfold symmetricContrastFourth; ring)

theorem binaryEntropy_derivative_formulas_at_half :
    binaryEntropySecondFormula (1 / 2) = -4 ∧
      binaryEntropyThirdFormula (1 / 2) = 0 ∧
      binaryEntropyFourthFormula (1 / 2) = -32 := by
  norm_num [binaryEntropySecondFormula, binaryEntropyThirdFormula,
    binaryEntropyFourthFormula]

theorem symmetricContrast_landau_jet (β J : ℝ) :
    symmetricContrastFirst β J 0 = 0 ∧
      symmetricContrastSecond β J 0 = 2 * landauQuadraticCoefficient β J ∧
      symmetricContrastThird 0 = 0 ∧
      symmetricContrastFourth 0 = 24 * landauQuarticCoefficient := by
  norm_num [symmetricContrastFirst, symmetricContrastSecond, symmetricContrastThird,
    symmetricContrastFourth, logOdds, binaryEntropySecondFormula,
    binaryEntropyThirdFormula, binaryEntropyFourthFormula,
    landauQuadraticCoefficient, landauQuarticCoefficient]
  ring

theorem symmetricContrastLandauJet_eq (β J d : ℝ) :
    symmetricContrastLandauJet β J d =
      symmetricContrastFreeEnergy β J 0 +
        (4 - 2 * β * J) * d ^ 2 + (8 / 3) * d ^ 4 := by
  rfl

theorem symmetricContrastFreeEnergy_even (β J d : ℝ) :
    symmetricContrastFreeEnergy β J (-d) = symmetricContrastFreeEnergy β J d := by
  unfold symmetricContrastFreeEnergy
  rw [show 1 / 2 + -d = 1 / 2 - d by ring,
    show 1 / 2 - -d = 1 / 2 + d by ring]
  ring

theorem symmetricContrastLandauJet_even (β J d : ℝ) :
    symmetricContrastLandauJet β J (-d) = symmetricContrastLandauJet β J d := by
  unfold symmetricContrastLandauJet
  ring

theorem symmetricContrastFirst_eq_log_ratio {β J d : ℝ}
    (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    symmetricContrastFirst β J d =
      -4 * β * J * d + 2 * Real.log ((1 + 2 * d) / (1 - 2 * d)) := by
  have hplus : 1 + 2 * d ≠ 0 := ne_of_gt (by linarith)
  have hminus : 1 - 2 * d ≠ 0 := ne_of_gt (by linarith)
  unfold symmetricContrastFirst logOdds
  rw [show (1 - (1 / 2 + d)) / (1 / 2 + d) =
      (1 - 2 * d) / (1 + 2 * d) by field_simp; ring]
  rw [show (1 - (1 / 2 - d)) / (1 / 2 - d) =
      (1 + 2 * d) / (1 - 2 * d) by field_simp; ring]
  rw [Real.log_div hminus hplus, Real.log_div hplus hminus]
  ring

theorem hasDerivAt_symmetricContrastLandauJet (β J d : ℝ) :
    HasDerivAt (symmetricContrastLandauJet β J)
      (2 * landauQuadraticCoefficient β J * d +
        4 * landauQuarticCoefficient * d ^ 3) d := by
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * d) d := by
    exact (hasDerivAt_pow 2 d).congr_deriv (by norm_num)
  have h4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * d ^ 3) d := by
    exact (hasDerivAt_pow 4 d).congr_deriv (by norm_num)
  have h := ((hasDerivAt_const d (symmetricContrastFreeEnergy β J 0)).add
    (h2.const_mul (landauQuadraticCoefficient β J))).add
    (h4.const_mul landauQuarticCoefficient)
  rw [show ((fun _ : ℝ => symmetricContrastFreeEnergy β J 0) +
      (fun x : ℝ => landauQuadraticCoefficient β J * x ^ 2)) +
      (fun x : ℝ => landauQuarticCoefficient * x ^ 4) =
      symmetricContrastLandauJet β J by funext x; rfl] at h
  exact h.congr_deriv (by ring)

theorem hasDerivAt_symmetricContrastLandauRemainder {β J d : ℝ}
    (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    HasDerivAt (symmetricContrastLandauRemainder β J)
      (symmetricContrastLandauRemainderFirst d) d := by
  have h := (hasDerivAt_symmetricContrastFreeEnergy (β := β) (J := J) hleft hright).sub
    (hasDerivAt_symmetricContrastLandauJet β J d)
  rw [show symmetricContrastFreeEnergy β J - symmetricContrastLandauJet β J =
      symmetricContrastLandauRemainder β J by funext x; rfl] at h
  rw [symmetricContrastFirst_eq_log_ratio hleft hright] at h
  exact h.congr_deriv (by
    unfold symmetricContrastLandauRemainderFirst landauQuadraticCoefficient
      landauQuarticCoefficient
    ring)

/-- The derivative of the Landau remainder is explicitly of order five.
The denominator remains positive on the physical contrast domain. -/
theorem abs_symmetricContrastLandauRemainderFirst_le {d : ℝ}
    (hd : |d| < 1 / 2) :
    |symmetricContrastLandauRemainderFirst d| ≤
      128 * |d| ^ 5 / (1 - 4 * d ^ 2) := by
  have h2d : |2 * d| < 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have h := Real.sum_range_sub_log_div_le (x := 2 * d) h2d 2
  have hsum :
      (∑ i ∈ Finset.range 2, (2 * d) ^ (2 * i + 1) / (2 * i + 1)) =
        2 * d + (2 * d) ^ 3 / 3 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  calc
    |symmetricContrastLandauRemainderFirst d| =
        4 * |1 / 2 * Real.log ((1 + 2 * d) / (1 - 2 * d)) -
          (2 * d + (2 * d) ^ 3 / 3)| := by
            unfold symmetricContrastLandauRemainderFirst
            rw [show 2 * Real.log ((1 + 2 * d) / (1 - 2 * d)) - 8 * d -
                32 / 3 * d ^ 3 =
                4 * (1 / 2 * Real.log ((1 + 2 * d) / (1 - 2 * d)) -
                  (2 * d + (2 * d) ^ 3 / 3)) by ring]
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ 4 * (|2 * d| ^ 5 / (1 - (2 * d) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 128 * |d| ^ 5 / (1 - 4 * d ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- Explicit pointwise sixth-order remainder control for the symmetric contrast
Landau expansion. -/
theorem abs_symmetricContrastLandauRemainder_le {β J d : ℝ}
    (hd : |d| < 1 / 2) :
    |symmetricContrastLandauRemainder β J d| ≤
      128 * |d| ^ 6 / (1 - 4 * d ^ 2) := by
  let C : ℝ := 128 * |d| ^ 5 / (1 - 4 * d ^ 2)
  have hinside : Icc (-|d|) |d| ⊆ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hbound : ∀ y ∈ Icc (-|d|) |d|,
      ‖symmetricContrastLandauRemainderFirst y‖ ≤ C := by
    intro y hy
    have hyabs : |y| ≤ |d| := abs_le.2 hy
    have hyhalf : |y| < 1 / 2 := lt_of_le_of_lt hyabs hd
    have hysq : y ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      rw [sq_lt_sq]
      simpa using hyhalf
    have hone_y : 0 < 1 - 4 * y ^ 2 := by nlinarith
    have hdsq : d ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      rw [sq_lt_sq]
      simpa using hd
    have hone_d : 0 < 1 - 4 * d ^ 2 := by
      nlinarith
    calc
      ‖symmetricContrastLandauRemainderFirst y‖ =
          |symmetricContrastLandauRemainderFirst y| := Real.norm_eq_abs _
      _ ≤ 128 * |y| ^ 5 / (1 - 4 * y ^ 2) :=
        abs_symmetricContrastLandauRemainderFirst_le hyhalf
      _ ≤ C := by
        dsimp [C]
        apply div_le_div₀
        · positivity
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg y) hyabs 5) (by norm_num)
        · exact hone_d
        · nlinarith [sq_le_sq.mpr hyabs]
  have hmvt :
      ‖symmetricContrastLandauRemainder β J d -
          symmetricContrastLandauRemainder β J 0‖ ≤ C * ‖d - 0‖ := by
    refine (convex_Icc (-|d|) |d|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => ?_) hbound
        ⟨by linarith [abs_nonneg d], abs_nonneg d⟩
        ⟨neg_abs_le d, le_abs_self d⟩
    exact (hasDerivAt_symmetricContrastLandauRemainder
      (hinside hy).1 (hinside hy).2).hasDerivWithinAt
  have hzero : symmetricContrastLandauRemainder β J 0 = 0 := by
    simp [symmetricContrastLandauRemainder, symmetricContrastLandauJet]
  rw [hzero, sub_zero] at hmvt
  simpa [C, Real.norm_eq_abs, pow_succ,
    mul_assoc, div_mul_eq_mul_div] using hmvt

/-- Uniform sixth-order remainder control on every closed contrast interval
strictly inside the physical domain. -/
theorem abs_symmetricContrastLandauRemainder_le_on {β J r d : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1 / 2) (hd : |d| ≤ r) :
    |symmetricContrastLandauRemainder β J d| ≤
      128 * |d| ^ 6 / (1 - 4 * r ^ 2) := by
  have hdhalf : |d| < 1 / 2 := lt_of_le_of_lt hd hr
  have hdsq : d ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    simpa using hdhalf
  have hden_d : 0 < 1 - 4 * d ^ 2 := by
    nlinarith
  have hden_r : 0 < 1 - 4 * r ^ 2 := by nlinarith
  calc
    |symmetricContrastLandauRemainder β J d| ≤
        128 * |d| ^ 6 / (1 - 4 * d ^ 2) :=
      abs_symmetricContrastLandauRemainder_le hdhalf
    _ ≤ 128 * |d| ^ 6 / (1 - 4 * r ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) hden_r
      have hdr : |d| ≤ |r| := by simpa [abs_of_nonneg hr0] using hd
      nlinarith [sq_le_sq.mpr hdr]

/-- The exact symmetric contrast free energy differs from its fourth-order
Landau jet by `O(d^6)` at the symmetric state. -/
theorem symmetricContrastLandauRemainder_isBigO (β J : ℝ) :
    (symmetricContrastLandauRemainder β J) =O[𝓝 0] (fun d : ℝ => d ^ 6) := by
  refine .of_bound (512 / 3) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)] with d hd
  have hdabs : |d| < 1 / 4 := by simpa [Real.dist_eq] using hd
  have h := abs_symmetricContrastLandauRemainder_le_on
    (β := β) (J := J) (r := 1 / 4) (d := d) (by norm_num) (by norm_num) hdabs.le
  norm_num at h ⊢
  calc
    |symmetricContrastLandauRemainder β J d| ≤ 128 * |d| ^ 6 / (3 / 4) := h
    _ = 512 / 3 * |d| ^ 6 := by ring

/-- The derivative of the symmetric contrast slice is odd. -/
theorem symmetricContrastFirst_odd (β J d : ℝ) :
    symmetricContrastFirst β J (-d) = -symmetricContrastFirst β J d := by
  unfold symmetricContrastFirst
  rw [show 1 / 2 + -d = 1 / 2 - d by ring,
    show 1 / 2 - -d = 1 / 2 + d by ring]
  ring

/-- On the physical part of the symmetric contrast line, the two gradient
coordinates are negatives of one another. -/
theorem refinedGradientQ_eq_neg_refinedGradientP_on_symmetricContrast
    {β J d : ℝ} (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    refinedGradientQ β J (1 / 2 + d) (1 / 2 - d) =
      -refinedGradientP β J (1 / 2 + d) (1 / 2 - d) := by
  have hplus : 1 + 2 * d ≠ 0 := ne_of_gt (by linarith)
  have hminus : 1 - 2 * d ≠ 0 := ne_of_gt (by linarith)
  unfold refinedGradientP refinedGradientQ logOdds
  rw [show (1 - (1 / 2 + d)) / (1 / 2 + d) =
      (1 - 2 * d) / (1 + 2 * d) by field_simp; ring]
  rw [show (1 - (1 / 2 - d)) / (1 / 2 - d) =
      (1 + 2 * d) / (1 - 2 * d) by field_simp; ring]
  rw [Real.log_div hminus hplus, Real.log_div hplus hminus]
  ring

/-- The derivative along the symmetric contrast line is twice the first
coordinate of the full refined gradient. -/
theorem symmetricContrastFirst_eq_two_refinedGradientP
    {β J d : ℝ} (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    symmetricContrastFirst β J d =
      2 * refinedGradientP β J (1 / 2 + d) (1 / 2 - d) := by
  have hq := refinedGradientQ_eq_neg_refinedGradientP_on_symmetricContrast
    (β := β) (J := J) hleft hright
  unfold refinedGradientP refinedGradientQ at hq
  unfold symmetricContrastFirst refinedGradientP
  rw [show 1 / 2 + d - (1 / 2 - d) = 2 * d by ring] at hq ⊢
  linarith

/-- A zero of the derivative along the physical symmetric contrast line is
equivalent to stationarity for the full two-variable refined free energy. -/
theorem refinedStationary_symmetricContrast_iff
    {β J d : ℝ} (hleft : -(1 / 2 : ℝ) < d) (hright : d < 1 / 2) :
    refinedStationary β J (1 / 2 + d) (1 / 2 - d) ↔
      symmetricContrastFirst β J d = 0 := by
  change refinedGradientP β J (1 / 2 + d) (1 / 2 - d) = 0 ∧
      refinedGradientQ β J (1 / 2 + d) (1 / 2 - d) = 0 ↔ _
  have hq := refinedGradientQ_eq_neg_refinedGradientP_on_symmetricContrast
    (β := β) (J := J) hleft hright
  have hp := symmetricContrastFirst_eq_two_refinedGradientP
    (β := β) (J := J) hleft hright
  constructor
  · rintro ⟨hP, _hQ⟩
    rw [hp, hP]
    norm_num
  · intro hfirst
    have hP : refinedGradientP β J (1 / 2 + d) (1 / 2 - d) = 0 := by
      rw [hp] at hfirst
      linarith
    exact ⟨hP, by rw [hq, hP]; norm_num⟩

/-- Immediately above the critical coupling, the exact refined free energy has
a symmetry-related pair of nonzero stationary points. -/
theorem exists_exact_broken_stationary_pair
    {β J : ℝ} (hsupercritical : 2 < β * J)
    (hnear : β * J < 2 * Real.log 3) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 4 ∧
      refinedStationary β J (1 / 2 + d) (1 / 2 - d) ∧
      refinedStationary β J (1 / 2 - d) (1 / 2 + d) := by
  let H : ℝ → ℝ := symmetricContrastFirst β J
  have hderiv0 : HasDerivAt H (8 - 4 * (β * J)) 0 := by
    have h := hasDerivAt_symmetricContrastFirst (β := β) (J := J) (d := 0)
      (by norm_num) (by norm_num)
    exact h.congr_deriv (by
      norm_num [symmetricContrastSecond, binaryEntropySecondFormula]
      ring)
  have hderivneg : 8 - 4 * (β * J) < 0 := by linarith
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (H (0 + t) - H 0) < 0 := by
    have hlim := hderiv0.tendsto_slope_zero_right
    have hevent := hlim.eventually_lt tendsto_const_nhds hderivneg
    simpa [smul_eq_mul] using hevent
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 / 4 :=
    hid.eventually_lt tendsto_const_nhds (by norm_num)
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  have hwitness : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ t < 1 / 4 ∧ t⁻¹ * (H (0 + t) - H 0) < 0 := by
    filter_upwards [hpositive, hsmall, hslope] with t ht0 htq hts
    exact ⟨ht0, htq, hts⟩
  rcases hwitness.exists with ⟨t, ht0, htquarter, htslope⟩
  have hH0 : H 0 = 0 := by
    simp [H, symmetricContrastFirst, logOdds]
  have htneg : H t < 0 := by
    have hprod : t⁻¹ * H t < 0 := by simpa [hH0] using htslope
    rcases (mul_neg_iff.mp hprod) with hgood | hbad
    · exact hgood.2
    · exact (not_lt_of_ge (inv_pos.mpr ht0).le hbad.1).elim
  have hquarter_formula : H (1 / 4) = -β * J + 2 * Real.log 3 := by
    dsimp [H]
    rw [symmetricContrastFirst_eq_log_ratio (by norm_num) (by norm_num)]
    norm_num
    ring
  have hquarterpos : 0 < H (1 / 4) := by
    rw [hquarter_formula]
    linarith
  have hcontinuous : ContinuousOn H (Icc t (1 / 4)) := by
    intro y hy
    exact (hasDerivAt_symmetricContrastFirst (β := β) (J := J)
      (by linarith [ht0, hy.1]) (by linarith [hy.2])).continuousAt.continuousWithinAt
  have hzero_mem : (0 : ℝ) ∈ Icc (H t) (H (1 / 4)) := ⟨htneg.le, hquarterpos.le⟩
  rcases intermediate_value_Icc htquarter.le hcontinuous hzero_mem with
    ⟨d, hdinterval, hdroot⟩
  have hdpos : 0 < d := lt_of_lt_of_le ht0 hdinterval.1
  have hdquarter : d < 1 / 4 := by
    apply lt_of_le_of_ne hdinterval.2
    intro hdeq
    subst d
    linarith
  have hdleft : -(1 / 2 : ℝ) < d := by linarith
  have hdright : d < 1 / 2 := by linarith
  have hstationaryPos : refinedStationary β J (1 / 2 + d) (1 / 2 - d) :=
    (refinedStationary_symmetricContrast_iff hdleft hdright).2 hdroot
  have hnegroot : symmetricContrastFirst β J (-d) = 0 := by
    change symmetricContrastFirst β J d = 0 at hdroot
    rw [symmetricContrastFirst_odd, hdroot, neg_zero]
  have hstationaryNeg : refinedStationary β J (1 / 2 - d) (1 / 2 + d) := by
    have hleftneg : -(1 / 2 : ℝ) < -d := by linarith
    have hrightneg : -d < 1 / 2 := by linarith
    simpa only [sub_eq_add_neg, neg_neg] using
      (refinedStationary_symmetricContrast_iff hleftneg hrightneg).2 hnegroot
  exact ⟨d, hdpos, hdquarter, hstationaryPos, hstationaryNeg⟩

/-- The exact coupling corresponding to a positive contrast `d`. -/
def exactContrastCoupling (d : ℝ) : ℝ :=
  Real.log ((1 + 2 * d) / (1 - 2 * d)) / (2 * d)

theorem symmetricContrastFirst_eq_zero_iff_coupling
    {β J d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    symmetricContrastFirst β J d = 0 ↔ β * J = exactContrastCoupling d := by
  rw [symmetricContrastFirst_eq_log_ratio (by linarith) hdhalf]
  unfold exactContrastCoupling
  constructor <;> intro h
  · field_simp
    nlinarith
  · field_simp at h
    nlinarith

theorem half_log_ratio_lt_tangent {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 / 2 * Real.log ((1 + x) / (1 - x)) < x / (1 - x ^ 2) := by
  have hupper := Real.log_div_le_sum_range_add hx0.le hx1 2
  have hsum :
      (∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1)) =
        x + x ^ 3 / 3 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hupper
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hstrict : x + x ^ 3 / 3 + x ^ 5 / (1 - x ^ 2) <
      x / (1 - x ^ 2) := by
    rw [lt_div_iff₀ hden]
    field_simp
    nlinarith [sq_pos_of_pos hx0]
  exact hupper.trans_lt hstrict

theorem hasDerivAt_exactContrastCoupling {d : ℝ}
    (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    HasDerivAt exactContrastCoupling
      (((4 / (1 - 4 * d ^ 2)) * (2 * d) -
        Real.log ((1 + 2 * d) / (1 - 2 * d)) * 2) / (2 * d) ^ 2) d := by
  unfold exactContrastCoupling
  have hnum : HasDerivAt
      (fun x : ℝ => Real.log ((1 + 2 * x) / (1 - 2 * x)))
      (4 / (1 - 4 * d ^ 2)) d := by
    have hbase := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
      0 (show -(1 : ℝ) < 2 * d by linarith) (show 2 * d < 1 by linarith)
    have hcurve : HasDerivAt (fun x : ℝ => 2 * x) 2 d := by
      simpa [id] using (hasDerivAt_id d).const_mul 2
    have hcomp := (hbase.comp d hcurve).const_mul 2
    have hderiv :
        2 * (((2 * d) ^ 2) ^ 0 / (1 - (2 * d) ^ 2) * 2) =
          4 / (1 - 4 * d ^ 2) := by
      norm_num
      rw [show 1 - (2 * d) ^ 2 = 1 - 4 * d ^ 2 by ring]
      ring
    apply (hcomp.congr_deriv hderiv).congr_of_eventuallyEq
    filter_upwards [] with x
    norm_num [Finset.sum_range_succ, Function.comp_def]
    ring
  have hden : HasDerivAt (fun x : ℝ => 2 * x) 2 d := by
    simpa [id] using (hasDerivAt_id d).const_mul 2
  exact hnum.div hden (by positivity)

theorem exactContrastCoupling_deriv_pos {d : ℝ}
    (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    0 < deriv exactContrastCoupling d := by
  rw [(hasDerivAt_exactContrastCoupling hd0 hdhalf).deriv]
  have htangent := half_log_ratio_lt_tangent (show 0 < 2 * d by positivity)
    (show 2 * d < 1 by linarith)
  rw [show 1 - (2 * d) ^ 2 = 1 - 4 * d ^ 2 by ring] at htangent
  have hden : 0 < (2 * d) ^ 2 := sq_pos_of_pos (by positivity)
  apply div_pos
  · rw [show 4 / (1 - 4 * d ^ 2) * (2 * d) -
        Real.log ((1 + 2 * d) / (1 - 2 * d)) * 2 =
        4 * (2 * d / (1 - 4 * d ^ 2) -
          1 / 2 * Real.log ((1 + 2 * d) / (1 - 2 * d))) by ring]
    positivity
  · exact hden

/-- The exact coupling is strictly increasing with positive contrast. -/
theorem exactContrastCoupling_strictMonoOn :
    StrictMonoOn exactContrastCoupling (Ioo 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (1 / 2))
  · intro d hd
    exact (hasDerivAt_exactContrastCoupling hd.1 hd.2).continuousAt.continuousWithinAt
  · intro d hd
    rw [interior_Ioo] at hd
    exact exactContrastCoupling_deriv_pos hd.1 hd.2

theorem two_lt_exactContrastCoupling {d : ℝ}
    (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    2 < exactContrastCoupling d := by
  have hlower := Real.sum_range_le_log_div
    (show 0 ≤ 2 * d by positivity) (show 2 * d < 1 by linarith) 2
  have hsum :
      (∑ i ∈ Finset.range 2, (2 * d) ^ (2 * i + 1) / (2 * i + 1)) =
        2 * d + (2 * d) ^ 3 / 3 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hlower
  unfold exactContrastCoupling
  rw [lt_div_iff₀ (show 0 < 2 * d by positivity)]
  nlinarith [sq_pos_of_pos hd0]

theorem exactContrastCoupling_stationary {d : ℝ}
    (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    refinedStationary (exactContrastCoupling d) 1
      (1 / 2 + d) (1 / 2 - d) := by
  apply (refinedStationary_symmetricContrast_iff (by linarith) hdhalf).2
  exact (symmetricContrastFirst_eq_zero_iff_coupling hd0 hdhalf).2 (by simp)

/-- There is at most one positive exact stationary contrast at fixed coupling. -/
theorem positive_symmetricContrast_root_unique
    {β J d e : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    (he0 : 0 < e) (hehalf : e < 1 / 2)
    (hdroot : symmetricContrastFirst β J d = 0)
    (heroot : symmetricContrastFirst β J e = 0) : d = e := by
  have hdK := (symmetricContrastFirst_eq_zero_iff_coupling hd0 hdhalf).1 hdroot
  have heK := (symmetricContrastFirst_eq_zero_iff_coupling he0 hehalf).1 heroot
  exact exactContrastCoupling_strictMonoOn.injOn
    ⟨hd0, hdhalf⟩ ⟨he0, hehalf⟩ (hdK.symm.trans heK)

theorem symmetricContrastSecond_pos_at_positive_root
    {β J d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    (hdroot : symmetricContrastFirst β J d = 0) :
    0 < symmetricContrastSecond β J d := by
  have hK := (symmetricContrastFirst_eq_zero_iff_coupling hd0 hdhalf).1 hdroot
  have htangent := half_log_ratio_lt_tangent (show 0 < 2 * d by positivity)
    (show 2 * d < 1 by linarith)
  have hp : 0 < 1 / 2 + d := by linarith
  have hq : 0 < 1 / 2 - d := by linarith
  have hformula : symmetricContrastSecond β J d =
      -4 * (β * J) + 8 / (1 - 4 * d ^ 2) := by
    unfold symmetricContrastSecond binaryEntropySecondFormula
    rw [show (1 / 2 + d) * (1 - (1 / 2 + d)) = 1 / 4 - d ^ 2 by ring,
      show (1 / 2 - d) * (1 - (1 / 2 - d)) = 1 / 4 - d ^ 2 by ring]
    field_simp [show 1 / 4 - d ^ 2 ≠ 0 by nlinarith,
      show 1 - 4 * d ^ 2 ≠ 0 by nlinarith]
    ring
  have hKlt : exactContrastCoupling d < 2 / (1 - 4 * d ^ 2) := by
    unfold exactContrastCoupling
    rw [show 1 - (2 * d) ^ 2 = 1 - 4 * d ^ 2 by ring] at htangent
    rw [div_lt_iff₀ (show 0 < 2 * d by positivity)]
    rw [show 2 / (1 - 4 * d ^ 2) * (2 * d) =
      2 * (2 * d / (1 - 4 * d ^ 2)) by ring]
    nlinarith
  rw [hformula, hK]
  calc
    0 < 4 * (2 / (1 - 4 * d ^ 2) - exactContrastCoupling d) := by positivity
    _ = -4 * exactContrastCoupling d + 8 / (1 - 4 * d ^ 2) := by ring

/-- A positive exact contrast root is a local minimum on the symmetric slice. -/
theorem symmetricContrastFreeEnergy_isLocalMin_at_positive_root
    {β J d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    (hdroot : symmetricContrastFirst β J d = 0) :
    IsLocalMin (symmetricContrastFreeEnergy β J) d := by
  apply isLocalMin_of_deriv_deriv_pos
  · have hevent : deriv (symmetricContrastFreeEnergy β J) =ᶠ[𝓝 d]
        symmetricContrastFirst β J := by
      filter_upwards [Ioo_mem_nhds (show -(1 / 2 : ℝ) < d by linarith) hdhalf] with x hx
      exact (hasDerivAt_symmetricContrastFreeEnergy hx.1 hx.2).deriv
    rw [hevent.deriv_eq, (hasDerivAt_symmetricContrastFirst (by linarith) hdhalf).deriv]
    exact symmetricContrastSecond_pos_at_positive_root hd0 hdhalf hdroot
  · rw [(hasDerivAt_symmetricContrastFreeEnergy (by linarith) hdhalf).deriv]
    exact hdroot
  · exact (hasDerivAt_symmetricContrastFreeEnergy (by linarith) hdhalf).continuousAt

theorem binaryEntropy_eq_real_binEntropy (u : ℝ) :
    binaryEntropy u = Real.binEntropy u := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [binaryEntropy, Real.negMulLog]
  ring

/-- At fixed contrast, centering the two probabilities around `1 / 2`
maximizes their entropy sum. -/
theorem centered_entropy_sum_ge {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binaryEntropy p + binaryEntropy q ≤
      binaryEntropy (1 / 2 + (p - q) / 2) +
        binaryEntropy (1 / 2 - (p - q) / 2) := by
  rw [binaryEntropy_eq_real_binEntropy, binaryEntropy_eq_real_binEntropy,
    binaryEntropy_eq_real_binEntropy, binaryEntropy_eq_real_binEntropy]
  have hc := Real.strictConcave_binEntropy.concaveOn
  have h1 := hc.2 (show p ∈ Icc (0 : ℝ) 1 from ⟨hp0, hp1⟩)
      (show 1 - q ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have h2 := hc.2 (show q ∈ Icc (0 : ℝ) 1 from ⟨hq0, hq1⟩)
      (show 1 - p ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, Real.binEntropy_one_sub] at h1 h2
  have heq1 : (1 / 2 : ℝ) * p + 1 / 2 * (1 - q) = 1 / 2 + (p - q) / 2 := by ring
  have heq2 : (1 / 2 : ℝ) * q + 1 / 2 * (1 - p) = 1 / 2 - (p - q) / 2 := by ring
  rw [heq1] at h1
  rw [heq2] at h2
  linarith

theorem refinedTwoBlockFreeEnergy_centered_le {β J p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    refinedTwoBlockFreeEnergy β J
        (1 / 2 + (p - q) / 2) (1 / 2 - (p - q) / 2) ≤
      refinedTwoBlockFreeEnergy β J p q := by
  have hent := centered_entropy_sum_ge hp0 hp1 hq0 hq1
  unfold refinedTwoBlockFreeEnergy
  rw [show 1 / 2 + (p - q) / 2 - (1 / 2 - (p - q) / 2) = p - q by ring]
  linarith

/-- A positive exact contrast root gives a local minimum of the full
two-variable refined free energy. -/
theorem refinedTwoBlockFreeEnergy_isLocalMin_at_positive_root
    {β J d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    (hdroot : symmetricContrastFirst β J d = 0) :
    IsLocalMin (fun x : ℝ × ℝ => refinedTwoBlockFreeEnergy β J x.1 x.2)
      (1 / 2 + d, 1 / 2 - d) := by
  have hslice := symmetricContrastFreeEnergy_isLocalMin_at_positive_root
    hd0 hdhalf hdroot
  have hcontrast : Tendsto (fun x : ℝ × ℝ => (x.1 - x.2) / 2)
      (𝓝 (1 / 2 + d, 1 / 2 - d)) (𝓝 d) := by
    have hc : ContinuousAt (fun x : ℝ × ℝ => (x.1 - x.2) / (2 : ℝ))
        (1 / 2 + d, 1 / 2 - d) :=
      ((continuous_fst.sub continuous_snd).div_const (2 : ℝ)).continuousAt
    change Tendsto (fun x : ℝ × ℝ => (x.1 - x.2) / (2 : ℝ))
      (𝓝 (1 / 2 + d, 1 / 2 - d))
      (𝓝 ((1 / 2 + d - (1 / 2 - d)) / (2 : ℝ))) at hc
    simpa only [show (1 / 2 + d - (1 / 2 - d)) / (2 : ℝ) = d by ring] using hc
  have hslice' : ∀ᶠ x : ℝ × ℝ in 𝓝 (1 / 2 + d, 1 / 2 - d),
      symmetricContrastFreeEnergy β J d ≤
        symmetricContrastFreeEnergy β J ((x.1 - x.2) / 2) :=
    hcontrast.eventually hslice
  have hp : ∀ᶠ x : ℝ × ℝ in 𝓝 (1 / 2 + d, 1 / 2 - d),
      x.1 ∈ Icc (0 : ℝ) 1 :=
    continuous_fst.continuousAt.eventually
      (Icc_mem_nhds (by linarith) (by linarith))
  have hq : ∀ᶠ x : ℝ × ℝ in 𝓝 (1 / 2 + d, 1 / 2 - d),
      x.2 ∈ Icc (0 : ℝ) 1 :=
    continuous_snd.continuousAt.eventually
      (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [hslice', hp, hq] with x hx hxp hxq
  calc
    refinedTwoBlockFreeEnergy β J (1 / 2 + d) (1 / 2 - d) =
        symmetricContrastFreeEnergy β J d :=
      (symmetricContrastFreeEnergy_eq_refined β J d).symm
    _ ≤ symmetricContrastFreeEnergy β J ((x.1 - x.2) / 2) := hx
    _ = refinedTwoBlockFreeEnergy β J
          (1 / 2 + (x.1 - x.2) / 2) (1 / 2 - (x.1 - x.2) / 2) :=
      symmetricContrastFreeEnergy_eq_refined β J _
    _ ≤ refinedTwoBlockFreeEnergy β J x.1 x.2 :=
      refinedTwoBlockFreeEnergy_centered_le hxp.1 hxp.2 hxq.1 hxq.2

theorem refinedTwoBlockFreeEnergy_swap (β J p q : ℝ) :
    refinedTwoBlockFreeEnergy β J q p = refinedTwoBlockFreeEnergy β J p q := by
  unfold refinedTwoBlockFreeEnergy
  ring

theorem refinedTwoBlockFreeEnergy_isLocalMin_at_negative_root
    {β J d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    (hdroot : symmetricContrastFirst β J d = 0) :
    IsLocalMin (fun x : ℝ × ℝ => refinedTwoBlockFreeEnergy β J x.1 x.2)
      (1 / 2 - d, 1 / 2 + d) := by
  have hpos := refinedTwoBlockFreeEnergy_isLocalMin_at_positive_root
    hd0 hdhalf hdroot
  have hswap : ContinuousAt (fun x : ℝ × ℝ => (x.2, x.1))
      (1 / 2 - d, 1 / 2 + d) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  have hcomp := IsLocalMin.comp_continuous
    (g := fun x : ℝ × ℝ => (x.2, x.1))
    (b := (1 / 2 - d, 1 / 2 + d)) hpos hswap
  apply hcomp.congr
  · filter_upwards [] with x
    exact refinedTwoBlockFreeEnergy_swap β J x.1 x.2

/-- Every interior stationary point of the refined model lies on the centered
line `p + q = 1`. -/
theorem refinedStationary_sum_eq_one {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hstationary : refinedStationary β J p q) : p + q = 1 := by
  rcases hstationary with ⟨hP, hQ⟩
  have hlogs : Real.log ((1 - p) / p) + Real.log ((1 - q) / q) = 0 := by
    linarith
  have hpOdds : 0 < (1 - p) / p := div_pos (by linarith) hp0
  have hqOdds : 0 < (1 - q) / q := div_pos (by linarith) hq0
  have hlogprod : Real.log (((1 - p) / p) * ((1 - q) / q)) = 0 := by
    rw [Real.log_mul hpOdds.ne' hqOdds.ne']
    exact hlogs
  have hprod := Real.eq_one_of_pos_of_log_eq_zero (mul_pos hpOdds hqOdds) hlogprod
  field_simp at hprod
  nlinarith

/-- Relative to one positive root, every nonsymmetric interior stationary point
is one of the two block-swapped broken points. -/
theorem refined_nontrivial_stationary_eq_broken_pair
    {β J d p q : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    (hdroot : symmetricContrastFirst β J d = 0)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hstationary : refinedStationary β J p q) (hpq : p ≠ q) :
    (p = 1 / 2 + d ∧ q = 1 / 2 - d) ∨
      (p = 1 / 2 - d ∧ q = 1 / 2 + d) := by
  have hsum := refinedStationary_sum_eq_one hp0 hp1 hq0 hq1 hstationary
  let e : ℝ := (p - q) / 2
  have hpform : p = 1 / 2 + e := by dsimp [e]; linarith
  have hqform : q = 1 / 2 - e := by dsimp [e]; linarith
  have he0 : e ≠ 0 := by
    dsimp [e]
    intro he
    have : p - q = 0 := by linarith
    exact hpq (sub_eq_zero.mp this)
  have heleft : -(1 / 2 : ℝ) < e := by dsimp [e]; linarith
  have heright : e < 1 / 2 := by dsimp [e]; linarith
  have heroot : symmetricContrastFirst β J e = 0 := by
    apply (refinedStationary_symmetricContrast_iff heleft heright).1
    simpa only [← hpform, ← hqform] using hstationary
  rcases lt_or_gt_of_ne he0 with heneg | hepos
  · have hnegroot : symmetricContrastFirst β J (-e) = 0 := by
      rw [symmetricContrastFirst_odd, heroot, neg_zero]
    have hde : d = -e := positive_symmetricContrast_root_unique
      hd0 hdhalf (neg_pos.mpr heneg) (by linarith [heleft]) hdroot hnegroot
    right
    constructor <;> linarith
  · have hde : d = e := positive_symmetricContrast_root_unique
      hd0 hdhalf hepos heright hdroot heroot
    left
    constructor <;> linarith

/-- In the explicit near-critical interval, the broken pair is the unique
nonsymmetric interior stationary pair and both points are full local minima. -/
theorem exists_unique_exact_broken_local_min_pair
    {β J : ℝ} (hsupercritical : 2 < β * J)
    (hnear : β * J < 2 * Real.log 3) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 4 ∧
      refinedStationary β J (1 / 2 + d) (1 / 2 - d) ∧
      refinedStationary β J (1 / 2 - d) (1 / 2 + d) ∧
      IsLocalMin (fun x : ℝ × ℝ => refinedTwoBlockFreeEnergy β J x.1 x.2)
        (1 / 2 + d, 1 / 2 - d) ∧
      IsLocalMin (fun x : ℝ × ℝ => refinedTwoBlockFreeEnergy β J x.1 x.2)
        (1 / 2 - d, 1 / 2 + d) ∧
      ∀ p q : ℝ, 0 < p → p < 1 → 0 < q → q < 1 →
        refinedStationary β J p q → p ≠ q →
        (p = 1 / 2 + d ∧ q = 1 / 2 - d) ∨
          (p = 1 / 2 - d ∧ q = 1 / 2 + d) := by
  rcases exists_exact_broken_stationary_pair hsupercritical hnear with
    ⟨d, hd0, hdquarter, hstatPos, hstatNeg⟩
  have hdhalf : d < 1 / 2 := by linarith
  have hdroot : symmetricContrastFirst β J d = 0 :=
    (refinedStationary_symmetricContrast_iff (by linarith) hdhalf).1 hstatPos
  exact ⟨d, hd0, hdquarter, hstatPos, hstatNeg,
    refinedTwoBlockFreeEnergy_isLocalMin_at_positive_root hd0 hdhalf hdroot,
    refinedTwoBlockFreeEnergy_isLocalMin_at_negative_root hd0 hdhalf hdroot,
    fun p q hp0 hp1 hq0 hq1 hstat hpq =>
      refined_nontrivial_stationary_eq_broken_pair hd0 hdhalf hdroot
        hp0 hp1 hq0 hq1 hstat hpq⟩

theorem exactContrastCoupling_sub_two_eq {d : ℝ} (hd : d ≠ 0) :
    exactContrastCoupling d - 2 =
      (8 / 3) * d ^ 2 + symmetricContrastLandauRemainderFirst d / (4 * d) := by
  unfold exactContrastCoupling symmetricContrastLandauRemainderFirst
  field_simp
  ring

/-- The normalized exact coupling differs from its leading coefficient by an
explicit quantity that tends to zero with the contrast. -/
theorem abs_exactContrastCoupling_normalized_sub_le {d : ℝ}
    (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    |(exactContrastCoupling d - 2) / d ^ 2 - 8 / 3| ≤
      32 * d ^ 2 / (1 - 4 * d ^ 2) := by
  have hrem := abs_symmetricContrastLandauRemainderFirst_le
    (show |d| < 1 / 2 by simpa [abs_of_pos hd0] using hdhalf)
  rw [exactContrastCoupling_sub_two_eq hd0.ne']
  have hden : 0 < 4 * d ^ 3 := by positivity
  have hdenmain : 0 < 1 - 4 * d ^ 2 := by nlinarith
  rw [show ((8 / 3) * d ^ 2 + symmetricContrastLandauRemainderFirst d / (4 * d)) /
        d ^ 2 - 8 / 3 = symmetricContrastLandauRemainderFirst d / (4 * d ^ 3) by
      field_simp
      ring]
  rw [abs_div, abs_of_pos hden]
  calc
    |symmetricContrastLandauRemainderFirst d| / (4 * d ^ 3) ≤
        (128 * |d| ^ 5 / (1 - 4 * d ^ 2)) / (4 * d ^ 3) :=
      div_le_div_of_nonneg_right hrem hden.le
    _ = 32 * d ^ 2 / (1 - 4 * d ^ 2) := by
      rw [abs_of_pos hd0]
      field_simp
      ring

theorem tendsto_exactContrastCoupling_normalized :
    Tendsto (fun d : ℝ => (exactContrastCoupling d - 2) / d ^ 2)
      (𝓝[>] 0) (𝓝 (8 / 3)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound_zero : Tendsto (fun d : ℝ => 32 * d ^ 2 / (1 - 4 * d ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun d : ℝ => 32 * d ^ 2 / (1 - 4 * d ^ 2)) 0 := by
      fun_prop (disch := norm_num)
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := eventually_mem_nhdsWithin
  have hid : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsmall : ∀ᶠ d : ℝ in 𝓝[>] 0, d < 1 / 2 :=
    hid.eventually_lt tendsto_const_nhds (by norm_num)
  apply squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _)
  · filter_upwards [hpositive, hsmall] with d hd0 hdhalf
    simpa [Real.norm_eq_abs] using
      abs_exactContrastCoupling_normalized_sub_le hd0 hdhalf
  · exact hbound_zero

/-- Along the exact branch, positive contrasts tend to zero at the critical
coupling `2`. -/
theorem tendsto_exactContrastCoupling :
    Tendsto exactContrastCoupling (𝓝[>] 0) (𝓝 2) := by
  have hid : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hprod := (hid.pow 2).mul tendsto_exactContrastCoupling_normalized
  have hconst : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] 0) (𝓝 2) :=
    tendsto_const_nhds
  have hsum := hconst.add hprod
  convert hsum.congr' ?_ using 1 <;> norm_num
  have hpositive : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := eventually_mem_nhdsWithin
  filter_upwards [hpositive] with d hd0
  field_simp
  ring

/-- Exact square-root critical scaling on the unique positive broken branch:
`d^2 / (βJ - 2) → 3/8`. -/
theorem tendsto_exactContrast_sq_div_coupling_sub_two :
    Tendsto (fun d : ℝ => d ^ 2 / (exactContrastCoupling d - 2))
      (𝓝[>] 0) (𝓝 (3 / 8)) := by
  have h := tendsto_exactContrastCoupling_normalized.inv₀ (by norm_num)
  rw [show (3 / 8 : ℝ) = (8 / 3)⁻¹ by norm_num]
  apply h.congr'
  have hpositive : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := eventually_mem_nhdsWithin
  filter_upwards [hpositive] with d hd0
  field_simp

end

end SymmetryMonograph.Chapter3
