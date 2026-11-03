import SymmetryMonograph.Chapter2

set_option linter.style.header false

/-!
# Chapter 3: finite algebraic pieces of the bifurcation analysis

This file records small formal statements from Chapter 3 that can be isolated
from the heavier variational-calculus development.
-/

namespace SymmetryMonograph.Chapter3

noncomputable section

def refinedAsymEigenvalue (β J : ℝ) : ℝ :=
  4 - 2 * β * J

def refinedSymEigenvalue (_β _J : ℝ) : ℝ :=
  4

def refinedHessianAtSymmetricPoint (β J : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((4 - β * J) * v.1 + β * J * v.2,
    β * J * v.1 + (4 - β * J) * v.2)

def symmetricMode : ℝ × ℝ :=
  (1, 1)

def antisymmetricMode : ℝ × ℝ :=
  (1, -1)

def pairScalarMul (c : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (c * v.1, c * v.2)

def IsGlobalMinOn {α : Type u} (f : α → ℝ) (s : Set α) (x : α) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, f x ≤ f y

def IsGlobalMin (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y, f x ≤ f y

def quarticApproximation (A B d : ℝ) : ℝ :=
  A * d ^ 2 + B * d ^ 4

def radialQuartic (a b r : ℝ) : ℝ :=
  a * r ^ 2 + b * r ^ 4

def binaryEntropy (u : ℝ) : ℝ :=
  -u * Real.log u - (1 - u) * Real.log (1 - u)

def logOdds (u : ℝ) : ℝ :=
  Real.log ((1 - u) / u)

def binaryEntropySecondFormula (u : ℝ) : ℝ :=
  -(1 / (u * (1 - u)))

def binaryEntropyFourthFormula (u : ℝ) : ℝ :=
  -2 * (1 - 3 * u + 3 * u ^ 2) / (u ^ 3 * (1 - u) ^ 3)

def HasPartialP (F : ℝ → ℝ → ℝ) (p q c : ℝ) : Prop :=
  HasDerivAt (fun x => F x q) c p

def HasPartialQ (F : ℝ → ℝ → ℝ) (p q c : ℝ) : Prop :=
  HasDerivAt (fun y => F p y) c q

def IsTwoVariableCritical (F : ℝ → ℝ → ℝ) (p q : ℝ) : Prop :=
  ∀ cp cq, HasPartialP F p q cp → HasPartialQ F p q cq → cp = 0 ∧ cq = 0

def twoBlockFreeEnergy (β J p q : ℝ) : ℝ :=
  -(β * J) / 2 * (p ^ 2 + q ^ 2) - binaryEntropy p - binaryEntropy q

def twoBlockStationary (β J p q : ℝ) : Prop :=
  β * J * p = -logOdds p ∧ β * J * q = -logOdds q

def twoBlockCriticalEquations (β J p q : ℝ) : Prop :=
  -β * J * p - logOdds p = 0 ∧ -β * J * q - logOdds q = 0

def twoBlockEigenvalue (β J r : ℝ) : ℝ :=
  1 / (r * (1 - r)) - β * J

def twoBlockHessian (β J p q : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 / (p * (1 - p)) - β * J) * v.1,
    (1 / (q * (1 - q)) - β * J) * v.2)

def twoBlockHessianAtSymmetricPoint (β J r : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (twoBlockEigenvalue β J r * v.1, twoBlockEigenvalue β J r * v.2)

def refinedTwoBlockFreeEnergy (β J p q : ℝ) : ℝ :=
  -(β * J) / 2 * (p - q) ^ 2 - binaryEntropy p - binaryEntropy q

def refinedStationary (β J p q : ℝ) : Prop :=
  -β * J * (p - q) - Real.log ((1 - p) / p) = 0 ∧
    β * J * (p - q) - Real.log ((1 - q) / q) = 0

def refinedHessian (β J p q : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 / (p * (1 - p)) - β * J) * v.1 + β * J * v.2,
    β * J * v.1 + (1 / (q * (1 - q)) - β * J) * v.2)

def updateMatrixEntry {k : ℕ} (ρ : Fin k → Fin k → ℝ)
    (a b : Fin k) (t : ℝ) : Fin k → Fin k → ℝ :=
  Function.update ρ a (Function.update (ρ a) b t)

def coordCurve {k : ℕ} (ρ : Fin k → Fin k → ℝ)
    (a b : Fin k) (t : ℝ) : Fin k → Fin k → ℝ :=
  updateMatrixEntry ρ a b t

def HasCoordDerivAt {k : ℕ} (F : (Fin k → Fin k → ℝ) → ℝ)
    (ρ : Fin k → Fin k → ℝ) (a b : Fin k) (c : ℝ) : Prop :=
  HasDerivAt (fun t => F (coordCurve ρ a b t)) c (ρ a b)

def IsInteriorBlockDensity {k : ℕ} (ρ : Fin k → Fin k → ℝ) : Prop :=
  ∀ a b, 0 < ρ a b ∧ ρ a b < 1

def kBlockEntropy {k : ℕ} (α : Fin k → ℝ) (ρ : Fin k → Fin k → ℝ) : ℝ :=
  ∑ a, ∑ b, α a * α b * binaryEntropy (ρ a b)

def kBlockFreeEnergy {k : ℕ} (β : ℝ)
    (Φ : (Fin k → Fin k → ℝ) → ℝ) (α : Fin k → ℝ)
    (ρ : Fin k → Fin k → ℝ) : ℝ :=
  β * Φ ρ - kBlockEntropy α ρ

def IsCoordCritical {k : ℕ} (F : (Fin k → Fin k → ℝ) → ℝ)
    (ρ : Fin k → Fin k → ℝ) : Prop :=
  ∀ a b c, HasCoordDerivAt F ρ a b c → c = 0

theorem refined_hessian_symmetric_mode (β J : ℝ) :
  refinedHessianAtSymmetricPoint β J symmetricMode =
      pairScalarMul (refinedSymEigenvalue β J) symmetricMode := by
  ext <;> simp [refinedHessianAtSymmetricPoint, symmetricMode, pairScalarMul,
    refinedSymEigenvalue]

theorem refined_hessian_antisymmetric_mode (β J : ℝ) :
    refinedHessianAtSymmetricPoint β J antisymmetricMode =
      pairScalarMul (refinedAsymEigenvalue β J) antisymmetricMode := by
  ext <;> simp [refinedHessianAtSymmetricPoint, antisymmetricMode, pairScalarMul,
    refinedAsymEigenvalue] <;> ring

theorem twoBlock_hessian_at_symmetric_point_eq (β J r : ℝ) :
    twoBlockHessian β J r r = twoBlockHessianAtSymmetricPoint β J r := by
  funext v
  ext <;> simp [twoBlockHessian, twoBlockHessianAtSymmetricPoint, twoBlockEigenvalue]

theorem twoBlock_hessian_symmetric_mode (β J r : ℝ) :
    twoBlockHessianAtSymmetricPoint β J r symmetricMode =
      pairScalarMul (twoBlockEigenvalue β J r) symmetricMode := by
  ext <;> simp [twoBlockHessianAtSymmetricPoint, symmetricMode, pairScalarMul]

theorem twoBlock_hessian_antisymmetric_mode (β J r : ℝ) :
    twoBlockHessianAtSymmetricPoint β J r antisymmetricMode =
      pairScalarMul (twoBlockEigenvalue β J r) antisymmetricMode := by
  ext <;> simp [twoBlockHessianAtSymmetricPoint, antisymmetricMode, pairScalarMul]

theorem refinedHessian_at_half_eq (β J : ℝ) :
    refinedHessian β J (1 / 2) (1 / 2) =
      refinedHessianAtSymmetricPoint β J := by
  funext v
  ext <;> norm_num [refinedHessian, refinedHessianAtSymmetricPoint]

theorem updateMatrixEntry_same {k : ℕ} (ρ : Fin k → Fin k → ℝ)
    (a b : Fin k) (t : ℝ) :
    updateMatrixEntry ρ a b t a b = t := by
  simp [updateMatrixEntry]

theorem updateMatrixEntry_of_row_ne {k : ℕ} (ρ : Fin k → Fin k → ℝ)
    {a a' b b' : Fin k} (h : a' ≠ a) (t : ℝ) :
    updateMatrixEntry ρ a b t a' b' = ρ a' b' := by
  simp [updateMatrixEntry, h]

theorem updateMatrixEntry_of_col_ne {k : ℕ} (ρ : Fin k → Fin k → ℝ)
    {a b b' : Fin k} (h : b' ≠ b) (t : ℝ) :
    updateMatrixEntry ρ a b t a b' = ρ a b' := by
  simp [updateMatrixEntry, h]

theorem coordCurve_same {k : ℕ} (ρ : Fin k → Fin k → ℝ)
    (a b : Fin k) :
    (fun t => coordCurve ρ a b t a b) = fun t => t := by
  ext t
  simp [coordCurve, updateMatrixEntry]

theorem hasCoordDerivAt_const {k : ℕ}
    (F : (Fin k → Fin k → ℝ) → ℝ) (ρ : Fin k → Fin k → ℝ)
    (a b : Fin k) (c : ℝ)
    (hF : ∀ t, F (coordCurve ρ a b t) = c) :
    HasCoordDerivAt F ρ a b 0 := by
  unfold HasCoordDerivAt
  simpa [hF] using hasDerivAt_const (ρ a b) c

theorem hasCoordDerivAt_kBlockEntropy
    {k : ℕ} (α : Fin k → ℝ) (ρ : Fin k → Fin k → ℝ)
    (a b : Fin k)
    (hentropy : HasDerivAt binaryEntropy (logOdds (ρ a b)) (ρ a b)) :
    HasCoordDerivAt (kBlockEntropy α) ρ a b
      (α a * α b * logOdds (ρ a b)) := by
  unfold HasCoordDerivAt kBlockEntropy coordCurve updateMatrixEntry
  classical
  have hsum :
      HasDerivAt
        (fun t =>
          ∑ i, ∑ j,
            α i * α j *
              binaryEntropy ((Function.update ρ a (Function.update (ρ a) b t)) i j))
        (∑ i, ∑ j,
          if hia : i = a then
            if hjb : j = b then α a * α b * logOdds (ρ a b) else 0
          else 0)
        (ρ a b) := by
    refine HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ) (x := ρ a b)
      (u := (Finset.univ : Finset (Fin k))) ?_
    intro i _hi
    refine HasDerivAt.fun_sum (𝕜 := ℝ) (F := ℝ) (x := ρ a b)
      (u := (Finset.univ : Finset (Fin k))) ?_
    intro j _hj
    by_cases hia : i = a
    · subst i
      by_cases hjb : j = b
      · subst j
        simpa using hentropy.const_mul (α a * α b)
      · simpa [hjb] using
          hasDerivAt_const (ρ a b) (α a * α j * binaryEntropy (ρ a j))
    · simpa [hia] using
        hasDerivAt_const (ρ a b) (α i * α j * binaryEntropy (ρ i j))
  convert hsum using 1
  · simp

theorem hasDerivAt_binaryEntropy_of_interior {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt binaryEntropy (logOdds u) u := by
  have hu_ne : u ≠ 0 := ne_of_gt h0
  have h1u_ne : 1 - u ≠ 0 := by linarith
  have hleft :
      HasDerivAt (fun x : ℝ => Real.negMulLog x) (-Real.log u - 1) u :=
    Real.hasDerivAt_negMulLog hu_ne
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - id) (-1) u
    simpa using (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
  have hright :
      HasDerivAt (fun x : ℝ => Real.negMulLog (1 - x))
        (Real.log (1 - u) + 1) u := by
    have hcomp := (Real.hasDerivAt_negMulLog h1u_ne).comp u hsub
    simpa [Function.comp_def, add_comm] using hcomp
  have hsum := hleft.add hright
  have hderiv_eq :
      logOdds u = -Real.log u - 1 + (Real.log (1 - u) + 1) := by
    unfold logOdds
    rw [Real.log_div h1u_ne hu_ne]
    ring
  have hfun :
      binaryEntropy =
        ((fun x : ℝ => Real.negMulLog x) +
          fun x : ℝ => Real.negMulLog (1 - x)) := by
    funext x
    simp [binaryEntropy, Real.negMulLog_eq_neg]
    ring
  rw [hderiv_eq, hfun]
  exact hsum

theorem hasDerivAt_logOdds_of_interior {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt logOdds (-(1 / (u * (1 - u)))) u := by
  unfold logOdds
  have hu_ne : u ≠ 0 := ne_of_gt h0
  have h1u_ne : 1 - u ≠ 0 := by linarith
  have hquot_ne : (1 - u) / u ≠ 0 := div_ne_zero h1u_ne hu_ne
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - id) (-1) u
    simpa using (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
  have hquot :
      HasDerivAt (fun x : ℝ => (1 - x) / x) (-(1 / u ^ 2)) u := by
    have h := hsub.div (hasDerivAt_id u) hu_ne
    rw [show (fun x : ℝ => (1 - x) / x) =
        ((fun x : ℝ => 1 - x) / id) by
      funext x
      rfl]
    rw [show -(1 / u ^ 2) = (-1 * u - (1 - u) * 1) / u ^ 2 by
      field_simp [hu_ne]
      ring]
    exact h
  have h := hquot.log hquot_ne
  rw [show -(1 / (u * (1 - u))) = -(1 / u ^ 2) / ((1 - u) / u) by
    field_simp [hu_ne, h1u_ne]]
  exact h

theorem hasDerivAt_logOdds_binaryEntropySecondFormula {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt logOdds (binaryEntropySecondFormula u) u := by
  simpa [binaryEntropySecondFormula] using hasDerivAt_logOdds_of_interior h0 h1

theorem binaryEntropy_fourthFormula_eq_split {u : ℝ}
    (h0 : u ≠ 0) (h1 : 1 - u ≠ 0) :
    -2 / u ^ 3 - 2 / (1 - u) ^ 3 = binaryEntropyFourthFormula u := by
  unfold binaryEntropyFourthFormula
  field_simp [h0, h1]
  ring

theorem kBlockEulerLagrange_of_coordCritical
    {k : ℕ} (β : ℝ)
    (Φ : (Fin k → Fin k → ℝ) → ℝ) (α : Fin k → ℝ)
    (ρ : Fin k → Fin k → ℝ) (a b : Fin k) (dΦ : ℝ)
    (hΦ : HasCoordDerivAt Φ ρ a b dΦ)
    (hentropy : HasDerivAt binaryEntropy (logOdds (ρ a b)) (ρ a b))
    (hcrit : IsCoordCritical (kBlockFreeEnergy β Φ α) ρ) :
    β * dΦ = α a * α b * logOdds (ρ a b) := by
  have hS := hasCoordDerivAt_kBlockEntropy α ρ a b hentropy
  have hF :
      HasCoordDerivAt (kBlockFreeEnergy β Φ α) ρ a b
        (β * dΦ - α a * α b * logOdds (ρ a b)) := by
    unfold HasCoordDerivAt at hΦ hS ⊢
    unfold kBlockFreeEnergy
    change HasDerivAt
      ((fun t => β * Φ (coordCurve ρ a b t)) -
        fun t => kBlockEntropy α (coordCurve ρ a b t))
      (β * dΦ - α a * α b * logOdds (ρ a b)) (ρ a b)
    exact (hΦ.const_mul β).sub hS
  have hzero := hcrit a b (β * dΦ - α a * α b * logOdds (ρ a b)) hF
  linarith

theorem kBlockEulerLagrange_of_interior_coordCritical
    {k : ℕ} (β : ℝ)
    (Φ : (Fin k → Fin k → ℝ) → ℝ) (α : Fin k → ℝ)
    (ρ : Fin k → Fin k → ℝ) (a b : Fin k) (dΦ : ℝ)
    (hρ : IsInteriorBlockDensity ρ)
    (hΦ : HasCoordDerivAt Φ ρ a b dΦ)
    (hcrit : IsCoordCritical (kBlockFreeEnergy β Φ α) ρ) :
    β * dΦ = α a * α b * logOdds (ρ a b) := by
  exact kBlockEulerLagrange_of_coordCritical β Φ α ρ a b dΦ hΦ
    (hasDerivAt_binaryEntropy_of_interior (hρ a b).1 (hρ a b).2) hcrit

theorem hasPartialP_twoBlockFreeEnergy {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasPartialP (twoBlockFreeEnergy β J) p q (-β * J * p - logOdds p) := by
  unfold HasPartialP twoBlockFreeEnergy
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2 + q ^ 2) (2 * p) p := by
    have h := ((hasDerivAt_id p).pow 2).add (hasDerivAt_const p (q ^ 2))
    rw [show (fun x : ℝ => x ^ 2 + q ^ 2) =
        (id ^ 2 + fun _ : ℝ => q ^ 2) by
      funext x
      simp [id]]
    simpa using h
  have hquad :
      HasDerivAt (fun x : ℝ => -(β * J) / 2 * (x ^ 2 + q ^ 2))
        (-(β * J) * p) p := by
    have h := hsq.const_mul (-(β * J) / 2)
    rw [show -(β * J) * p = -(β * J) / 2 * (2 * p) by ring_nf]
    exact h
  have hpent := hasDerivAt_binaryEntropy_of_interior hp0 hp1
  have hconst : HasDerivAt (fun _ : ℝ => binaryEntropy q) 0 p :=
    hasDerivAt_const p (binaryEntropy q)
  have h := (hquad.sub hpent).sub hconst
  rw [show
      (fun x : ℝ =>
        -(β * J) / 2 * (x ^ 2 + q ^ 2) - binaryEntropy x - binaryEntropy q) =
      ((fun x : ℝ => -(β * J) / 2 * (x ^ 2 + q ^ 2)) -
        binaryEntropy - fun _ : ℝ => binaryEntropy q) by
    funext x
    dsimp]
  rw [show -β * J * p - logOdds p = -(β * J) * p - logOdds p - 0 by ring]
  exact h

theorem hasPartialQ_twoBlockFreeEnergy {β J p q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasPartialQ (twoBlockFreeEnergy β J) p q (-β * J * q - logOdds q) := by
  unfold HasPartialQ twoBlockFreeEnergy
  have hsq : HasDerivAt (fun y : ℝ => p ^ 2 + y ^ 2) (2 * q) q := by
    have h := (hasDerivAt_const q (p ^ 2)).add ((hasDerivAt_id q).pow 2)
    rw [show (fun y : ℝ => p ^ 2 + y ^ 2) =
        ((fun _ : ℝ => p ^ 2) + id ^ 2) by
      funext y
      simp [id]]
    simpa using h
  have hquad :
      HasDerivAt (fun y : ℝ => -(β * J) / 2 * (p ^ 2 + y ^ 2))
        (-(β * J) * q) q := by
    have h := hsq.const_mul (-(β * J) / 2)
    rw [show -(β * J) * q = -(β * J) / 2 * (2 * q) by ring_nf]
    exact h
  have hqent := hasDerivAt_binaryEntropy_of_interior hq0 hq1
  have hconst : HasDerivAt (fun _ : ℝ => binaryEntropy p) 0 q :=
    hasDerivAt_const q (binaryEntropy p)
  have h := (hquad.sub hconst).sub hqent
  rw [show
      (fun y : ℝ =>
        -(β * J) / 2 * (p ^ 2 + y ^ 2) - binaryEntropy p - binaryEntropy y) =
      ((fun y : ℝ => -(β * J) / 2 * (p ^ 2 + y ^ 2)) -
        (fun _ : ℝ => binaryEntropy p) - binaryEntropy) by
    funext y
    dsimp]
  rw [show -β * J * q - logOdds q = -(β * J) * q - 0 - logOdds q by ring]
  exact h

theorem twoBlock_eulerLagrange_of_critical {β J p q : ℝ}
    (hcrit : IsTwoVariableCritical (twoBlockFreeEnergy β J) p q)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    twoBlockCriticalEquations β J p q := by
  exact hcrit
    (-β * J * p - logOdds p)
    (-β * J * q - logOdds q)
    (hasPartialP_twoBlockFreeEnergy hp0 hp1)
    (hasPartialQ_twoBlockFreeEnergy hq0 hq1)

theorem twoBlock_criticalEquations_iff_neg_logOdds {β J p q : ℝ} :
    twoBlockCriticalEquations β J p q ↔
      β * J * p = -logOdds p ∧ β * J * q = -logOdds q := by
  unfold twoBlockCriticalEquations
  constructor
  · intro h
    constructor <;> linarith
  · intro h
    constructor <;> linarith

theorem hasPartialP_refinedTwoBlockFreeEnergy {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasPartialP (refinedTwoBlockFreeEnergy β J) p q
      (-β * J * (p - q) - logOdds p) := by
  unfold HasPartialP refinedTwoBlockFreeEnergy
  have hsub : HasDerivAt (fun x : ℝ => x - q) 1 p := by
    change HasDerivAt (id - fun _ : ℝ => q) 1 p
    simpa using (hasDerivAt_id p).sub (hasDerivAt_const p q)
  have hsquare : HasDerivAt (fun x : ℝ => (x - q) ^ 2) (2 * (p - q)) p := by
    have h := hsub.pow 2
    rw [show (fun x : ℝ => (x - q) ^ 2) = ((fun x : ℝ => x - q) ^ 2) by rfl]
    simpa using h
  have hquad :
      HasDerivAt (fun x : ℝ => -(β * J) / 2 * (x - q) ^ 2)
        (-β * J * (p - q)) p := by
    have h := hsquare.const_mul (-(β * J) / 2)
    rw [show -β * J * (p - q) = -(β * J) / 2 * (2 * (p - q)) by ring_nf]
    exact h
  have hpent := hasDerivAt_binaryEntropy_of_interior hp0 hp1
  have hconst : HasDerivAt (fun _ : ℝ => binaryEntropy q) 0 p :=
    hasDerivAt_const p (binaryEntropy q)
  have h := (hquad.sub hpent).sub hconst
  rw [show
      (fun x : ℝ =>
        -(β * J) / 2 * (x - q) ^ 2 - binaryEntropy x - binaryEntropy q) =
      ((fun x : ℝ => -(β * J) / 2 * (x - q) ^ 2) -
        binaryEntropy - fun _ : ℝ => binaryEntropy q) by
    funext x
    dsimp]
  simpa using h

theorem hasPartialQ_refinedTwoBlockFreeEnergy {β J p q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasPartialQ (refinedTwoBlockFreeEnergy β J) p q
      (β * J * (p - q) - logOdds q) := by
  unfold HasPartialQ refinedTwoBlockFreeEnergy
  have hsub : HasDerivAt (fun y : ℝ => p - y) (-1) q := by
    change HasDerivAt ((fun _ : ℝ => p) - id) (-1) q
    simpa using (hasDerivAt_const q p).sub (hasDerivAt_id q)
  have hsquare : HasDerivAt (fun y : ℝ => (p - y) ^ 2) (-2 * (p - q)) q := by
    have h := hsub.pow 2
    rw [show (fun y : ℝ => (p - y) ^ 2) = ((fun y : ℝ => p - y) ^ 2) by rfl]
    simpa [mul_assoc] using h
  have hquad :
      HasDerivAt (fun y : ℝ => -(β * J) / 2 * (p - y) ^ 2)
        (β * J * (p - q)) q := by
    have h := hsquare.const_mul (-(β * J) / 2)
    rw [show β * J * (p - q) = -(β * J) / 2 * (-2 * (p - q)) by ring_nf]
    exact h
  have hqent := hasDerivAt_binaryEntropy_of_interior hq0 hq1
  have hconst : HasDerivAt (fun _ : ℝ => binaryEntropy p) 0 q :=
    hasDerivAt_const q (binaryEntropy p)
  have h := (hquad.sub hconst).sub hqent
  rw [show
      (fun y : ℝ =>
        -(β * J) / 2 * (p - y) ^ 2 - binaryEntropy p - binaryEntropy y) =
      ((fun y : ℝ => -(β * J) / 2 * (p - y) ^ 2) -
        (fun _ : ℝ => binaryEntropy p) - binaryEntropy) by
    funext y
    dsimp]
  simpa using h

theorem refined_first_derivatives {β J p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    HasPartialP (refinedTwoBlockFreeEnergy β J) p q
        (-β * J * (p - q) - logOdds p) ∧
      HasPartialQ (refinedTwoBlockFreeEnergy β J) p q
        (β * J * (p - q) - logOdds q) := by
  exact ⟨hasPartialP_refinedTwoBlockFreeEnergy hp0 hp1,
    hasPartialQ_refinedTwoBlockFreeEnergy hq0 hq1⟩

theorem quartic_unique_min_of_quadratic_pos {A B d : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    IsGlobalMin (quarticApproximation A B) d ↔ d = 0 := by
  constructor
  · intro hmin
    have hle : quarticApproximation A B d ≤ quarticApproximation A B 0 := hmin 0
    have hnonneg : 0 ≤ quarticApproximation A B d := by
      unfold quarticApproximation
      positivity
    have hzero : quarticApproximation A B d = 0 := by
      have h0 : quarticApproximation A B 0 = 0 := by simp [quarticApproximation]
      linarith
    have hsq : d ^ 2 = 0 := by
      unfold quarticApproximation at hzero
      have hsq_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
      have hquart_nonneg : 0 ≤ B * d ^ 4 := by positivity
      nlinarith
    nlinarith
  · intro hd y
    subst d
    unfold quarticApproximation
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have hy4 : 0 ≤ y ^ 4 := by positivity
    nlinarith [mul_nonneg hA.le hy2, mul_nonneg hB.le hy4]

theorem quartic_global_min_iff_sq_eq_of_quadratic_neg {A B d : ℝ}
    (hA : A < 0) (hB : 0 < B) :
    IsGlobalMin (quarticApproximation A B) d ↔ d ^ 2 = -A / (2 * B) := by
  constructor
  · intro hmin
    let v := -A / (2 * B)
    have hle : quarticApproximation A B d ≤
        quarticApproximation A B (Real.sqrt v) :=
      hmin (Real.sqrt v)
    have hv_nonneg : 0 ≤ v := by
      dsimp [v]
      have hnegA : 0 < -A := neg_pos.mpr hA
      positivity
    have hsqrt_sq : (Real.sqrt v) ^ 2 = v := by
      rw [Real.sq_sqrt]
      exact hv_nonneg
    have hdiff : quarticApproximation A B d -
        quarticApproximation A B (Real.sqrt v) = B * (d ^ 2 - v) ^ 2 := by
      unfold quarticApproximation
      rw [hsqrt_sq]
      rw [show (Real.sqrt v) ^ 4 = v ^ 2 by nlinarith [hsqrt_sq]]
      dsimp [v]
      field_simp [hB.ne']
      ring_nf
    have hnonneg : 0 ≤ B * (d ^ 2 - v) ^ 2 := by positivity
    have hsquare_zero : B * (d ^ 2 - v) ^ 2 = 0 := by
      linarith
    have : (d ^ 2 - v) ^ 2 = 0 := by
      exact mul_eq_zero.mp hsquare_zero |>.resolve_left hB.ne'
    dsimp [v] at this
    nlinarith
  · intro hd y
    have hdiff : quarticApproximation A B y - quarticApproximation A B d =
        B * (y ^ 2 - d ^ 2) ^ 2 := by
      unfold quarticApproximation
      rw [show d ^ 4 = (d ^ 2) ^ 2 by ring]
      rw [hd]
      field_simp [hB.ne']
      ring_nf
    have hnonneg : 0 ≤ B * (y ^ 2 - d ^ 2) ^ 2 := by positivity
    linarith

theorem radial_quartic_unique_min_of_quadratic_pos {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IsGlobalMinOn (radialQuartic a b) (Set.Ici 0) r ↔ r = 0 := by
  constructor
  · intro hmin
    have hr_nonneg : 0 ≤ r := hmin.1
    have hle : radialQuartic a b r ≤ radialQuartic a b 0 := hmin.2 0 (by simp)
    have hnonneg : 0 ≤ radialQuartic a b r := by
      unfold radialQuartic
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      have hr4 : 0 ≤ r ^ 4 := by positivity
      nlinarith [mul_nonneg ha.le hr2, mul_nonneg hb.le hr4]
    have hzero : radialQuartic a b r = 0 := by
      have h0 : radialQuartic a b 0 = 0 := by simp [radialQuartic]
      linarith
    have hsq : r ^ 2 = 0 := by
      unfold radialQuartic at hzero
      have hsq_nonneg : 0 ≤ r ^ 2 := sq_nonneg r
      have hquart_nonneg : 0 ≤ b * r ^ 4 := by positivity
      nlinarith
    nlinarith
  · intro hr
    subst r
    constructor
    · simp
    · intro y hy
      unfold radialQuartic
      have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
      have hy4 : 0 ≤ y ^ 4 := by positivity
      nlinarith [mul_nonneg ha.le hy2, mul_nonneg hb.le hy4]

theorem radial_quartic_global_min_iff_sq_eq_of_quadratic_neg {a b r : ℝ}
    (ha : a < 0) (hb : 0 < b) :
    IsGlobalMinOn (radialQuartic a b) (Set.Ici 0) r ↔
      0 ≤ r ∧ r ^ 2 = -a / (2 * b) := by
  constructor
  · intro hmin
    refine ⟨hmin.1, ?_⟩
    let v := -a / (2 * b)
    have hle : radialQuartic a b r ≤
        radialQuartic a b (Real.sqrt v) :=
      hmin.2 (Real.sqrt v) (Real.sqrt_nonneg v)
    have hv_nonneg : 0 ≤ v := by
      dsimp [v]
      have hnega : 0 < -a := neg_pos.mpr ha
      positivity
    have hsqrt_sq : (Real.sqrt v) ^ 2 = v := by
      rw [Real.sq_sqrt]
      exact hv_nonneg
    have hdiff : radialQuartic a b r -
        radialQuartic a b (Real.sqrt v) = b * (r ^ 2 - v) ^ 2 := by
      unfold radialQuartic
      rw [hsqrt_sq]
      rw [show (Real.sqrt v) ^ 4 = v ^ 2 by nlinarith [hsqrt_sq]]
      dsimp [v]
      field_simp [hb.ne']
      ring_nf
    have hnonneg : 0 ≤ b * (r ^ 2 - v) ^ 2 := by positivity
    have hsquare_zero : b * (r ^ 2 - v) ^ 2 = 0 := by
      linarith
    have : (r ^ 2 - v) ^ 2 = 0 := by
      exact mul_eq_zero.mp hsquare_zero |>.resolve_left hb.ne'
    dsimp [v] at this
    nlinarith
  · rintro ⟨hr_nonneg, hr_sq⟩
    constructor
    · exact hr_nonneg
    · intro y hy
      have hdiff : radialQuartic a b y - radialQuartic a b r =
          b * (y ^ 2 - r ^ 2) ^ 2 := by
        unfold radialQuartic
        rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
        rw [hr_sq]
        field_simp [hb.ne']
        ring_nf
      have hnonneg : 0 ≤ b * (y ^ 2 - r ^ 2) ^ 2 := by positivity
      linarith

theorem twoBlock_diagonal_branch {β J p : ℝ}
    (hp : β * J * p = -logOdds p) :
    twoBlockStationary β J p p := by
  exact ⟨hp, hp⟩

theorem twoBlock_unstable_iff (β J r : ℝ) :
    twoBlockEigenvalue β J r < 0 ↔ β * J > 1 / (r * (1 - r)) := by
  unfold twoBlockEigenvalue
  constructor <;> intro h <;> linarith

theorem twoBlock_critical_threshold_at_half {β J : ℝ} (hJ : 0 < J) :
    twoBlockEigenvalue β J (1 / 2) < 0 ↔ β > 4 / J := by
  rw [twoBlock_unstable_iff]
  norm_num
  exact (div_lt_iff₀ hJ).symm

theorem log_odds_eq_zero_iff_eq_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.log ((1 - p) / p) = 0 ↔ p = 1 / 2 := by
  constructor
  · intro hlog
    have hratio : (1 - p) / p = 1 := by
      rcases Real.log_eq_zero.mp hlog with hzero | hone | hneg
      · have hpos : 0 < (1 - p) / p := by positivity
        linarith
      · exact hone
      · have hpos : 0 < (1 - p) / p := by positivity
        linarith
    have hp_ne : p ≠ 0 := ne_of_gt hp0
    have : 1 - p = p := (div_eq_one_iff_eq hp_ne).mp hratio
    linarith
  · intro hp
    subst p
    norm_num

theorem refined_symmetric_branch_iff {β J p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    refinedStationary β J p p ↔ p = 1 / 2 := by
  constructor
  · intro hstat
    apply (log_odds_eq_zero_iff_eq_half hp0 hp1).mp
    linarith [hstat.1]
  · intro hp
    subst p
    constructor <;> norm_num [refinedStationary]

theorem refined_antisymmetric_mode_unstable_iff {β J : ℝ} (hJ : 0 < J) :
    refinedAsymEigenvalue β J < 0 ↔ β > 2 / J := by
  constructor
  · intro h
    unfold refinedAsymEigenvalue at h
    have hmul : 2 < β * J := by nlinarith
    exact (div_lt_iff₀ hJ).mpr hmul
  · intro h
    have hmul : 2 < β * J := (div_lt_iff₀ hJ).mp h
    unfold refinedAsymEigenvalue
    nlinarith

end

end SymmetryMonograph.Chapter3
