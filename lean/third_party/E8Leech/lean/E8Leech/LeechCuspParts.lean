import E8Leech.LeechContourBounds
import E8Leech.CKMRVContourAssembly

/-!
# The cusp parts of `𝒦̂⁽²⁴⁾(iy, ·)` at the cusps `±1`

In dimension 24 the kernel `𝒦(iy, it)` grows like `f(t) = e^{2πt}(A t + B)` at `t → ∞`. Through
`𝒦̂ = 𝒦 |_{−10} STS` and `𝒦̂ = 𝒦 |_{−10} TST` the kernel `𝒦̂(iy, ·)` therefore blows up at the cusps
`1` and `−1` of the two ideal triangles, with the singular parts

`P₁(z) = (z − 1)¹⁰ f(−i z/(1 − z))`,  `P₋₁(z) = (z + 1)¹⁰ f(−i z/(z + 1))`

(`cuspPartPlus`, `cuspPartMinus`). These are holomorphic in the upper half-plane. This file
evaluates them on the sides of the triangles and bounds them away from their own cusp.

* on the imaginary axis they are the integrands of `cusp_contour_shift` (`σ = ±i`);
* on the lines `Re z = ±1`: `P₁(1 + is) = −s¹⁰ f(1/s + i)`, `P₋₁(is − 1) = −s¹⁰ f(1/s − i)`, whose
  mean is `−s¹⁰ f(1/s)`;
* on the semicircles: `P₁(v(t)) = (v(t) − 1)¹⁰ f(t)`, `P₋₁(u(t)) = (u(t) + 1)¹⁰ f(t)`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open scoped Real

/-- The cusp part of `𝒦̂⁽²⁴⁾` at the cusp `1`. -/
def cuspPartPlus (A B : ℂ) (z : ℂ) : ℂ := (z - 1) ^ 10 * growthC A B (-I * (z / (1 - z)))

/-- The cusp part of `𝒦̂⁽²⁴⁾` at the cusp `−1`. -/
def cuspPartMinus (A B : ℂ) (z : ℂ) : ℂ := (z + 1) ^ 10 * growthC A B (-I * (z / (z + 1)))

theorem differentiableAt_cuspPartPlus (A B : ℂ) {z : ℂ} (hz : 1 - z ≠ 0) :
    DifferentiableAt ℂ (cuspPartPlus A B) z := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -I * (z / (1 - z))) z :=
    (differentiableAt_fun_id.div ((differentiableAt_const _).sub differentiableAt_fun_id)
      hz).const_mul _
  have h2 : DifferentiableAt ℂ (fun z : ℂ => growthC A B (-I * (z / (1 - z)))) z :=
    (differentiable_growthC A B).differentiableAt.comp z h1
  exact ((differentiableAt_fun_id.sub_const 1).pow 10).mul h2

theorem differentiableAt_cuspPartMinus (A B : ℂ) {z : ℂ} (hz : z + 1 ≠ 0) :
    DifferentiableAt ℂ (cuspPartMinus A B) z := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z + 1) z := differentiableAt_fun_id.add_const 1
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -I * (z / (z + 1))) z :=
    (differentiableAt_fun_id.div hd hz).const_mul _
  have h2 : DifferentiableAt ℂ (fun z : ℂ => growthC A B (-I * (z / (z + 1)))) z :=
    (differentiable_growthC A B).differentiableAt.comp z h1
  exact (hd.pow 10).mul h2

/-! ## The sides of the triangles -/

theorem I_pow_ten : (I : ℂ) ^ 10 = -1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, Complex.I_sq]
  norm_num

theorem cuspPartPlus_I_mul (A B : ℂ) (s : ℝ) :
    cuspPartPlus A B (I * s) = (1 - I * s) ^ 10 * growthC A B (s / (1 - I * s)) := by
  have h1 : (1 : ℂ) - I * s ≠ 0 := one_sub_I_mul_ne_zero s
  rw [cuspPartPlus, show I * (s : ℂ) - 1 = -(1 - I * s) by ring, Even.neg_pow (by decide)]
  congr 2
  rw [mul_div_assoc', eq_div_iff h1, div_mul_cancel₀ _ h1]
  linear_combination (-(s : ℂ)) * Complex.I_sq

theorem cuspPartMinus_I_mul (A B : ℂ) (s : ℝ) :
    cuspPartMinus A B (I * s) = (1 - -I * s) ^ 10 * growthC A B (s / (1 - -I * s)) := by
  have h1 : (1 : ℂ) + I * s ≠ 0 := one_add_I_mul_ne_zero s
  have e : (1 : ℂ) - -I * s = 1 + I * s := by ring
  rw [cuspPartMinus, e, add_comm (I * (s : ℂ)) 1]
  congr 2
  rw [mul_div_assoc', eq_div_iff h1, div_mul_cancel₀ _ h1]
  linear_combination (-(s : ℂ)) * Complex.I_sq

theorem cuspPartPlus_one_add_I_mul (A B : ℂ) {s : ℝ} (hs : s ≠ 0) :
    cuspPartPlus A B (1 + I * s) = -(s : ℂ) ^ 10 * growthC A B ((s⁻¹ : ℝ) + I) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have h1 : (1 : ℂ) - (1 + I * s) ≠ 0 := by
    rw [show (1 : ℂ) - (1 + I * s) = -(I * s) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero I_ne_zero hs0)
  rw [cuspPartPlus, show (1 : ℂ) + I * s - 1 = I * s by ring, mul_pow, I_pow_ten]
  congr 2
  · ring
  · rw [mul_div_assoc', div_eq_iff h1]
    push_cast
    field_simp
    ring

theorem cuspPartMinus_I_mul_sub_one (A B : ℂ) {s : ℝ} (hs : s ≠ 0) :
    cuspPartMinus A B (I * s - 1) = -(s : ℂ) ^ 10 * growthC A B ((s⁻¹ : ℝ) - I) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have h1 : I * (s : ℂ) - 1 + 1 ≠ 0 := by
    rw [sub_add_cancel]
    exact mul_ne_zero I_ne_zero hs0
  rw [cuspPartMinus, sub_add_cancel, mul_pow, I_pow_ten]
  congr 2
  · ring
  · rw [mul_div_assoc', div_eq_iff (mul_ne_zero I_ne_zero hs0)]
    push_cast
    field_simp
    ring

/-- The mean of the two cusp parts on the lines `Re z = ±1` is `−s¹⁰ f(1/s)`. -/
theorem cuspPart_add_cuspPart (A B : ℂ) {s : ℝ} (hs : s ≠ 0) :
    cuspPartPlus A B (1 + I * s) + cuspPartMinus A B (I * s - 1) =
      -(2 * (s : ℂ) ^ 10 * growthC A B ((s⁻¹ : ℝ) : ℂ)) := by
  rw [cuspPartPlus_one_add_I_mul A B hs, cuspPartMinus_I_mul_sub_one A B hs]
  linear_combination (-(s : ℂ) ^ 10) * growthC_add_I_add_sub_I A B ((s⁻¹ : ℝ) : ℂ)

theorem cuspPartPlus_vPath (A B : ℂ) (t : ℝ) :
    cuspPartPlus A B (vPath t) = (vPath t - 1) ^ 10 * growthC A B t := by
  rw [cuspPartPlus, vPath_div_one_sub]
  congr 2
  linear_combination (-(t : ℂ)) * Complex.I_sq

theorem cuspPartMinus_uPath (A B : ℂ) (t : ℝ) :
    cuspPartMinus A B (uPath t) = (uPath t + 1) ^ 10 * growthC A B t := by
  rw [cuspPartMinus, uPath_div_add_one]
  congr 2
  linear_combination (-(t : ℂ)) * Complex.I_sq

/-! ## Bounds away from the cusp -/

theorem norm_growthC_le (A B : ℂ) {t : ℂ} {T : ℝ} (ht : ‖t‖ ≤ T) :
    ‖growthC A B t‖ ≤ Real.exp (2 * π * T) * (‖A‖ * T + ‖B‖) := by
  rw [norm_growthC]
  have hre : t.re ≤ T := (le_abs_self _).trans ((Complex.abs_re_le_norm t).trans ht)
  have h1 : Real.exp (2 * π * t.re) ≤ Real.exp (2 * π * T) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h2 : ‖A * t + B‖ ≤ ‖A‖ * T + ‖B‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left ht (norm_nonneg _)) le_rfl
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le

/-- `P₁` is bounded near `0`. -/
theorem norm_cuspPartPlus_le_of_norm_le (A B : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖cuspPartPlus A B z‖ ≤ (3 / 2) ^ 10 * (Real.exp (2 * π * 1) * (‖A‖ * 1 + ‖B‖)) := by
  have h1 : 1 / 2 ≤ ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at this
    linarith
  have h2 : ‖z - 1‖ ≤ 3 / 2 := by
    have := norm_sub_le z 1
    rw [norm_one] at this
    linarith
  have h3 : ‖-I * (z / (1 - z))‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div, div_le_one (by linarith)]
    linarith
  rw [cuspPartPlus, norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h2 10) (norm_growthC_le A B h3)
    (norm_nonneg _) (by positivity)

/-- `P₋₁` is bounded near `0`. -/
theorem norm_cuspPartMinus_le_of_norm_le (A B : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖cuspPartMinus A B z‖ ≤ (3 / 2) ^ 10 * (Real.exp (2 * π * 1) * (‖A‖ * 1 + ‖B‖)) := by
  have h1 : 1 / 2 ≤ ‖z + 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-z)
    rw [norm_one, norm_neg, sub_neg_eq_add, add_comm] at this
    linarith
  have h2 : ‖z + 1‖ ≤ 3 / 2 := by
    have := norm_add_le z 1
    rw [norm_one] at this
    linarith
  have h3 : ‖-I * (z / (z + 1))‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div, div_le_one (by linarith)]
    linarith
  rw [cuspPartMinus, norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h2 10) (norm_growthC_le A B h3)
    (norm_nonneg _) (by positivity)

/-- `P₁` grows at most like `(1 + Im z)¹⁰` at `i∞` in the strip `0 ≤ Re z ≤ 1`. -/
theorem norm_cuspPartPlus_le_top (A B : ℂ) {z : ℂ} (hz1 : 1 ≤ z.im) (hre0 : 0 ≤ z.re)
    (hre1 : z.re ≤ 1) :
    ‖cuspPartPlus A B z‖ ≤ (1 + z.im) ^ 10 * (Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖)) := by
  have h1 : 1 ≤ ‖1 - z‖ := by
    have := Complex.abs_im_le_norm (1 - z)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    exact hz1.trans ((le_abs_self _).trans this)
  have hne : (1 : ℂ) - z ≠ 0 := norm_pos_iff.mp (by linarith)
  have h2 : ‖z - 1‖ ≤ 1 + z.im := by
    have := Complex.norm_le_abs_re_add_abs_im (z - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  have h3 : ‖-I * (z / (1 - z))‖ ≤ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have e : z / (1 - z) = -1 + 1 / (1 - z) := by
      field_simp
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_one, norm_div, norm_one]
    have : 1 / ‖(1 : ℂ) - z‖ ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact h1
    linarith
  rw [cuspPartPlus, norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h2 10) (norm_growthC_le A B h3)
    (norm_nonneg _) (by positivity)

/-- `P₋₁` grows at most like `(1 + Im z)¹⁰` at `i∞` in the strip `−1 ≤ Re z ≤ 0`. -/
theorem norm_cuspPartMinus_le_top (A B : ℂ) {z : ℂ} (hz1 : 1 ≤ z.im) (hre0 : -1 ≤ z.re)
    (hre1 : z.re ≤ 0) :
    ‖cuspPartMinus A B z‖ ≤ (1 + z.im) ^ 10 * (Real.exp (2 * π * 2) * (‖A‖ * 2 + ‖B‖)) := by
  have h1 : 1 ≤ ‖z + 1‖ := by
    have := Complex.abs_im_le_norm (z + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero] at this
    exact hz1.trans ((le_abs_self _).trans this)
  have hne : z + 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have h2 : ‖z + 1‖ ≤ 1 + z.im := by
    have := Complex.norm_le_abs_re_add_abs_im (z + 1)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  have h3 : ‖-I * (z / (z + 1))‖ ≤ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have e : z / (z + 1) = 1 + -(1 / (z + 1)) := by
      field_simp
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_neg, norm_div, norm_one]
    have : 1 / ‖z + 1‖ ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact h1
    linarith
  rw [cuspPartMinus, norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h2 10) (norm_growthC_le A B h3)
    (norm_nonneg _) (by positivity)

theorem exists_pow_twelve_mul_exp_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 0 ≤ v → (1 + v) ^ 12 * Real.exp (-(c * v)) ≤ K := by
  obtain ⟨K, hK⟩ := SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul 12 hc
  have hK0 : 0 ≤ K := by simpa using hK 0 le_rfl
  refine ⟨K * Real.exp c, mul_nonneg hK0 (Real.exp_pos _).le, fun v hv => ?_⟩
  have h := hK (1 + v) (by linarith)
  have e : Real.exp (-(c * v)) = Real.exp (-c * (1 + v)) * Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

end E8Leech
