import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Jacobi theta functions in the CKMRV normalization

CKMRV Section 2.1 uses `U = θ₃⁴`, `V = θ₂⁴`, `W = θ₄⁴`. We define the three theta
functions through the pinned two-variable `jacobiTheta₂`, check their usual series, and
prove the translation and inversion laws pointwise from `jacobiTheta₂_functional_equation`.
Fourth powers remove every square-root branch: only `((-iτ)^(1/2))^4 = (-iτ)^2` is used.
Holomorphy on `ℍ` and the limits at `i∞` close the file; the limits use Tannery's theorem
with the explicit summable majorant `‖jacobiTheta₂_term n z I‖`.

The route follows the Apache-2.0 sources math-inc/Sphere-Packing-Lean (1e98fb49,
`SpherePacking/ModularForms/JacobiTheta.lean`) and its LeanPool port. The statements are
restated pointwise for the pinned Mathlib; no upstream file is imported.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups

/-- `θ₃(τ) = ∑ₙ exp(π i n² τ)`. -/
def thetaThree (τ : ℂ) : ℂ := jacobiTheta₂ 0 τ

/-- `θ₄(τ) = ∑ₙ (-1)ⁿ exp(π i n² τ)`. -/
def thetaFour (τ : ℂ) : ℂ := jacobiTheta₂ (1 / 2) τ

/-- `θ₂(τ) = ∑ₙ exp(π i (n + 1/2)² τ)`, written as `exp(π i τ / 4) θ(τ / 2, τ)`. -/
def thetaTwo (τ : ℂ) : ℂ := cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ

theorem thetaThree_eq_tsum (τ : ℂ) :
    thetaThree τ = ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ) := by
  unfold thetaThree jacobiTheta₂
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  ring_nf

theorem thetaFour_eq_tsum (τ : ℂ) :
    thetaFour τ = ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ) := by
  unfold thetaFour jacobiTheta₂
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, ← Complex.exp_add]
  ring_nf

theorem thetaTwo_eq_tsum (τ : ℂ) :
    thetaTwo τ = ∑' n : ℤ, cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) := by
  unfold thetaTwo jacobiTheta₂
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

/-! ## Translation -/

private theorem exists_sq_eq_add_two_mul (n : ℤ) : ∃ m : ℤ, n ^ 2 = n + 2 * m := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · exact ⟨2 * k ^ 2 - k, by ring⟩
  · exact ⟨2 * k ^ 2 + k, by ring⟩

theorem thetaThree_add_one (τ : ℂ) : thetaThree (τ + 1) = thetaFour τ := by
  unfold thetaThree thetaFour jacobiTheta₂
  refine tsum_congr fun n => ?_
  obtain ⟨m, hm⟩ := exists_sq_eq_add_two_mul n
  have hm' : (n : ℂ) ^ 2 = n + 2 * m := by exact_mod_cast hm
  simp only [jacobiTheta₂_term]
  have h : (2 * π * I * n * 0 + π * I * n ^ 2 * (τ + 1) : ℂ) =
      (2 * π * I * n * (1 / 2) + π * I * n ^ 2 * τ) + m * (2 * π * I) := by
    rw [hm']
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem thetaFour_add_one (τ : ℂ) : thetaFour (τ + 1) = thetaThree τ := by
  rw [← thetaThree_add_one (τ + 1)]
  unfold thetaThree
  rw [add_assoc, one_add_one_eq_two, jacobiTheta₂_add_right]

private theorem jacobiTheta₂_half_add_one (τ : ℂ) :
    jacobiTheta₂ ((τ + 1) / 2) (τ + 1) = jacobiTheta₂ (τ / 2) τ := by
  unfold jacobiTheta₂
  refine tsum_congr fun n => ?_
  obtain ⟨m, hm⟩ := exists_sq_eq_add_two_mul n
  have hm' : (n : ℂ) ^ 2 = n + 2 * m := by exact_mod_cast hm
  simp only [jacobiTheta₂_term]
  have h : (2 * π * I * n * ((τ + 1) / 2) + π * I * n ^ 2 * (τ + 1) : ℂ) =
      (2 * π * I * n * (τ / 2) + π * I * n ^ 2 * τ) + ((n + m : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    rw [hm']
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem thetaTwo_add_one (τ : ℂ) : thetaTwo (τ + 1) = cexp (π * I / 4) * thetaTwo τ := by
  unfold thetaTwo
  rw [jacobiTheta₂_half_add_one]
  have h : cexp (π * I * (τ + 1) / 4) = cexp (π * I / 4) * cexp (π * I * τ / 4) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [h, mul_assoc]

/-! ## Inversion

Fourth powers make every inversion law branch-free. -/

private theorem cpow_half_pow_four (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 4 = x ^ 2 := by
  rw [← Complex.cpow_nat_mul]
  norm_num

theorem thetaThree_neg_inv_pow_four {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree (-1 / τ) ^ 4 = -τ ^ 2 * thetaThree τ ^ 4 := by
  have h := jacobiTheta₂_functional_equation 0 (-1 / τ)
  have h1 : -I * (-1 / τ) = I / τ := by ring
  have h2 : (-1 : ℂ) / (-1 / τ) = τ := by field_simp
  rw [h1, h2, zero_div] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h
  unfold thetaThree
  rw [h, mul_pow, div_pow, one_pow, cpow_half_pow_four, div_pow, Complex.I_sq]
  field_simp

theorem thetaTwo_eq_mul_thetaFour_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * thetaFour (-1 / τ) := by
  unfold thetaTwo thetaFour
  rw [jacobiTheta₂_functional_equation (τ / 2) τ]
  have h1 : τ / 2 / τ = 1 / 2 := by field_simp
  have h2 : -π * I * (τ / 2) ^ 2 / τ = -(π * I * τ / 4) := by field_simp; ring
  rw [h1, h2, Complex.exp_neg]
  have he : cexp (π * I * τ / 4) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem thetaFour_neg_inv_pow_four {τ : ℂ} (hτ : τ ≠ 0) :
    thetaFour (-1 / τ) ^ 4 = -τ ^ 2 * thetaTwo τ ^ 4 := by
  rw [thetaTwo_eq_mul_thetaFour_neg_inv hτ, mul_pow, div_pow, one_pow, cpow_half_pow_four]
  have h : (-I * τ) ^ 2 = -τ ^ 2 := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  rw [h]
  field_simp

theorem thetaTwo_neg_inv_pow_four {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo (-1 / τ) ^ 4 = -τ ^ 2 * thetaFour τ ^ 4 := by
  have hτ' : (-1 / τ) ≠ 0 := div_ne_zero (by norm_num) hτ
  have h := thetaFour_neg_inv_pow_four hτ'
  have h2 : (-1 : ℂ) / (-1 / τ) = τ := by field_simp
  rw [h2] at h
  rw [h]
  field_simp

/-! ## The fourth powers on the upper half-plane -/

/-- `U = θ₃⁴`. -/
def thetaU (τ : ℍ) : ℂ := thetaThree τ ^ 4

/-- `V = θ₂⁴`. -/
def thetaV (τ : ℍ) : ℂ := thetaTwo τ ^ 4

/-- `W = θ₄⁴`. -/
def thetaW (τ : ℍ) : ℂ := thetaFour τ ^ 4

theorem coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div]

theorem thetaU_T (τ : ℍ) : thetaU (ModularGroup.T • τ) = thetaW τ := by
  rw [thetaU, thetaW, coe_T_smul, thetaThree_add_one]

theorem thetaW_T (τ : ℍ) : thetaW (ModularGroup.T • τ) = thetaU τ := by
  rw [thetaW, thetaU, coe_T_smul, thetaFour_add_one]

theorem thetaV_T (τ : ℍ) : thetaV (ModularGroup.T • τ) = -thetaV τ := by
  rw [thetaV, thetaV, coe_T_smul, thetaTwo_add_one, mul_pow, ← Complex.exp_nat_mul]
  have h : ((4 : ℕ) : ℂ) * (π * I / 4) = π * I := by push_cast; ring
  rw [h, Complex.exp_pi_mul_I]
  ring

theorem thetaU_S (τ : ℍ) : thetaU (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * thetaU τ := by
  rw [thetaU, thetaU, coe_S_smul, thetaThree_neg_inv_pow_four τ.ne_zero]

theorem thetaV_S (τ : ℍ) : thetaV (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * thetaW τ := by
  rw [thetaV, thetaW, coe_S_smul, thetaTwo_neg_inv_pow_four τ.ne_zero]

theorem thetaW_S (τ : ℍ) : thetaW (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * thetaV τ := by
  rw [thetaW, thetaV, coe_S_smul, thetaFour_neg_inv_pow_four τ.ne_zero]

/-! ## Holomorphy -/

theorem differentiableAt_thetaThree {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaThree τ :=
  differentiableAt_jacobiTheta₂_snd 0 hτ

theorem differentiableAt_thetaFour {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaFour τ :=
  differentiableAt_jacobiTheta₂_snd (1 / 2) hτ

theorem differentiableAt_thetaTwo {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaTwo τ := by
  have hθ : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ := by
    have hg := (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
    have hf : DifferentiableAt ℂ (fun t : ℂ => (t / 2, t)) τ :=
      (differentiableAt_id.div_const 2).prodMk differentiableAt_id
    exact DifferentiableAt.comp (f := fun t : ℂ => (t / 2, t)) τ hg hf
  exact ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp.mul hθ

private theorem mdifferentiable_of_pow_four {θ : ℂ → ℂ}
    (hθ : ∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ θ τ) :
    MDiff (fun τ : ℍ => θ τ ^ 4) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ => θ z ^ 4) ?_ ?_
  · intro z hz
    exact ((hθ z hz).pow 4).differentiableWithinAt
  · intro z hz
    simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem mdifferentiable_thetaU : MDiff thetaU :=
  mdifferentiable_of_pow_four fun _ h => differentiableAt_thetaThree h

theorem mdifferentiable_thetaV : MDiff thetaV :=
  mdifferentiable_of_pow_four fun _ h => differentiableAt_thetaTwo h

theorem mdifferentiable_thetaW : MDiff thetaW :=
  mdifferentiable_of_pow_four fun _ h => differentiableAt_thetaFour h

/-! ## Limits at `i∞`

Tannery's theorem with the majorant `‖jacobiTheta₂_term n z I‖`, valid once `1 ≤ Im τ`. -/

theorem tendsto_upperHalfPlaneIm_atImInfty : Tendsto UpperHalfPlane.im atImInfty atTop :=
  tendsto_comap

private theorem tendsto_exp_neg_mul_im {c : ℝ} (hc : 0 < c) :
    Tendsto (fun τ : ℍ => Real.exp (-(c * τ.im))) atImInfty (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_upperHalfPlaneIm_atImInfty.const_mul_atTop hc)

private theorem tendsto_term_zero_of_pos {n : ℤ} {z : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hnorm : ∀ τ : ℍ, ‖jacobiTheta₂_term n (z τ) τ‖ = Real.exp (-(c * τ.im))) :
    Tendsto (fun τ : ℍ => jacobiTheta₂_term n (z τ) τ) atImInfty (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hnorm] using tendsto_exp_neg_mul_im hc

private theorem summable_norm_term (z : ℂ) :
    Summable fun n : ℤ => ‖jacobiTheta₂_term n z I‖ :=
  summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff z I).mpr (by simp))

private theorem eventually_one_le_im : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
  tendsto_upperHalfPlaneIm_atImInfty.eventually_ge_atTop 1

theorem tendsto_thetaThree_atImInfty :
    Tendsto (fun τ : ℍ => thetaThree τ) atImInfty (𝓝 1) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty)
    (f := fun (τ : ℍ) (n : ℤ) => jacobiTheta₂_term n 0 τ)
    (g := fun n : ℤ => if n = 0 then (1 : ℂ) else 0)
    (bound := fun n : ℤ => ‖jacobiTheta₂_term n 0 I‖) (summable_norm_term 0) ?_ ?_
  · simpa [thetaThree, jacobiTheta₂] using h
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp [jacobiTheta₂_term]
    · simp only [hn, if_false]
      have hpos : 0 < π * (n : ℝ) ^ 2 :=
        mul_pos Real.pi_pos (by positivity)
      refine tendsto_term_zero_of_pos hpos fun τ => ?_
      rw [norm_jacobiTheta₂_term]
      congr 1
      simp
  · filter_upwards [eventually_one_le_im] with τ hτ n
    rw [norm_jacobiTheta₂_term, norm_jacobiTheta₂_term, Real.exp_le_exp]
    have hsq : 0 ≤ π * (n : ℝ) ^ 2 := by positivity
    simp only [Complex.zero_im, Complex.I_im, mul_zero, sub_zero, mul_one,
      UpperHalfPlane.coe_im]
    nlinarith

theorem tendsto_thetaFour_atImInfty :
    Tendsto (fun τ : ℍ => thetaFour τ) atImInfty (𝓝 1) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty)
    (f := fun (τ : ℍ) (n : ℤ) => jacobiTheta₂_term n (1 / 2) τ)
    (g := fun n : ℤ => if n = 0 then (1 : ℂ) else 0)
    (bound := fun n : ℤ => ‖jacobiTheta₂_term n 0 I‖) (summable_norm_term 0) ?_ ?_
  · simpa [thetaFour, jacobiTheta₂] using h
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp [jacobiTheta₂_term]
    · simp only [hn, if_false]
      have hpos : 0 < π * (n : ℝ) ^ 2 :=
        mul_pos Real.pi_pos (by positivity)
      refine tendsto_term_zero_of_pos hpos fun τ => ?_
      rw [norm_jacobiTheta₂_term]
      congr 1
      simp
  · filter_upwards [eventually_one_le_im] with τ hτ n
    rw [norm_jacobiTheta₂_term, norm_jacobiTheta₂_term, Real.exp_le_exp]
    have hsq : 0 ≤ π * (n : ℝ) ^ 2 := by positivity
    simp only [Complex.zero_im, Complex.I_im, mul_zero, sub_zero, mul_one,
      UpperHalfPlane.coe_im]
    norm_num
    nlinarith

private theorem int_sq_add_self_nonneg (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
  have h : 0 ≤ n ^ 2 + n := by nlinarith
  exact_mod_cast h

private theorem int_sq_add_self_pos {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ -1) :
    0 < (n : ℝ) ^ 2 + n := by
  have h : 0 < n ^ 2 + n := by
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have : n ≤ -2 := by omega
      nlinarith
    · exact absurd hn h0
    · nlinarith
  exact_mod_cast h

/-- The `q^(1/8)`-normalized `θ₂` tends to `2`: only `n = 0, -1` survive. -/
theorem tendsto_jacobiTheta₂_half_atImInfty :
    Tendsto (fun τ : ℍ => jacobiTheta₂ ((τ : ℂ) / 2) τ) atImInfty (𝓝 2) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty)
    (f := fun (τ : ℍ) (n : ℤ) => jacobiTheta₂_term n ((τ : ℂ) / 2) τ)
    (g := fun n : ℤ => (if n = 0 then (1 : ℂ) else 0) + (if n = -1 then (1 : ℂ) else 0))
    (bound := fun n : ℤ => ‖jacobiTheta₂_term n (I / 2) I‖) (summable_norm_term (I / 2)) ?_ ?_
  · have hsum : (∑' n : ℤ, ((if n = 0 then (1 : ℂ) else 0) + (if n = -1 then (1 : ℂ) else 0)))
        = 2 := by
      rw [((hasSum_ite_eq 0 (1 : ℂ)).add (hasSum_ite_eq (-1) (1 : ℂ))).tsum_eq]
      norm_num
    rw [hsum] at h
    simpa [jacobiTheta₂] using h
  · intro n
    by_cases h0 : n = 0
    · subst h0
      simp [jacobiTheta₂_term]
    by_cases h1 : n = -1
    · subst h1
      have hc : ∀ τ : ℍ, jacobiTheta₂_term (-1) ((τ : ℂ) / 2) τ = 1 := by
        intro τ
        rw [jacobiTheta₂_term]
        push_cast
        ring_nf
        exact Complex.exp_zero
      simp [hc]
    · simp only [h0, h1, if_false, add_zero]
      have hpos : 0 < π * ((n : ℝ) ^ 2 + n) := mul_pos Real.pi_pos (int_sq_add_self_pos h0 h1)
      refine tendsto_term_zero_of_pos hpos fun τ => ?_
      rw [norm_jacobiTheta₂_term]
      congr 1
      simp
      ring
  · filter_upwards [eventually_one_le_im] with τ hτ n
    rw [norm_jacobiTheta₂_term, norm_jacobiTheta₂_term, Real.exp_le_exp]
    have hq : 0 ≤ π * ((n : ℝ) ^ 2 + n) := mul_nonneg Real.pi_pos.le (int_sq_add_self_nonneg n)
    have him : ((τ : ℂ) / 2).im = τ.im / 2 := by simp
    rw [him]
    simp only [Complex.div_im, Complex.I_im, Complex.I_re, mul_one]
    norm_num
    nlinarith

theorem tendsto_thetaTwo_atImInfty :
    Tendsto (fun τ : ℍ => thetaTwo τ) atImInfty (𝓝 0) := by
  have he : Tendsto (fun τ : ℍ => cexp (π * I * τ / 4)) atImInfty (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpos : (0 : ℝ) < π / 4 := by positivity
    refine (tendsto_exp_neg_mul_im hpos).congr fun τ => ?_
    rw [Complex.norm_exp]
    congr 1
    simp
    ring
  simpa [thetaTwo] using he.mul tendsto_jacobiTheta₂_half_atImInfty

theorem tendsto_thetaU_atImInfty : Tendsto thetaU atImInfty (𝓝 1) := by
  have h := tendsto_thetaThree_atImInfty.pow 4
  rw [one_pow] at h
  exact h

theorem tendsto_thetaW_atImInfty : Tendsto thetaW atImInfty (𝓝 1) := by
  have h := tendsto_thetaFour_atImInfty.pow 4
  rw [one_pow] at h
  exact h

theorem tendsto_thetaV_atImInfty : Tendsto thetaV atImInfty (𝓝 0) := by
  have h := tendsto_thetaTwo_atImInfty.pow 4
  rw [zero_pow (by norm_num)] at h
  exact h

end E8Leech
