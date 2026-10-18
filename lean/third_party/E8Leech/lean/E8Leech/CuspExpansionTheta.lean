import E8Leech.CuspExpansion
import E8Leech.CKMRVKernelResidues
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Second-order cusp expansions of the theta quantities

With `s = e^{πiτ}`:
`θ₃ = 1 + 2s + O(s³)`, `θ₄ = 1 - 2s + O(s³)`, `Σₙ s^{n²+n} = 2 + 2s² + O(s³)`, hence
`U = 1 + 8s + 24s²`, `W = 1 - 8s + 24s²`, `V = 16s` (mod `s³`), and by CKMRV (2.12)
`E₄ = 1 + 240s²`, `E₆ = 1 - 504s²`, `Δ = s²`. The logarithms satisfy
`L - πiτ - 4 log 2 = -8s + 12s²` and `L_S = -16s` (mod `s³`).
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Norms of the series terms -/

theorem norm_cexp_pi_I_mul (w : ℂ) (m : ℝ) :
    ‖cexp (π * I * m * w)‖ = Real.exp (-π * w.im) ^ m := by
  rw [Complex.norm_exp, ← Real.exp_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem geom_tail_bound {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (k : ℕ) :
    HasSum (fun n : ℕ => r ^ k * r ^ n) (r ^ k * (1 - r)⁻¹) :=
  (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left (r ^ k)

theorem tail_le_two_mul {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (k : ℕ) :
    r ^ k * (1 - r)⁻¹ ≤ 2 * r ^ k := by
  have h : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [pow_nonneg hr0 k]

/-! ## `θ₃`, `θ₄` and `Σ s^{n² + n}` -/

theorem norm_thetaThree_sub_le {w : ℂ} (hw : 0 < w.im) (hr : Real.exp (-π * w.im) ≤ 1 / 2) :
    ‖thetaThree w - (1 + 2 * cexp (π * I * w))‖ ≤ 4 * Real.exp (-π * w.im) ^ 3 := by
  set r := Real.exp (-π * w.im) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hS := hasSum_nat_jacobiTheta hw
  have hS1 := (hasSum_nat_add_iff' 1).mpr hS
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_pow, mul_one] at hS1
  have hb : ∀ n : ℕ, ‖cexp (π * I * (((n + 1 : ℕ) : ℂ) + 1) ^ 2 * w)‖ ≤ r ^ 4 * r ^ n := by
    intro n
    have h1 : cexp (π * I * (((n + 1 : ℕ) : ℂ) + 1) ^ 2 * w) =
        cexp (π * I * (((n + 2) ^ 2 : ℕ) : ℝ) * w) := by
      congr 1
      push_cast
      ring
    rw [h1, norm_cexp_pi_I_mul, ← hrdef, Real.rpow_natCast]
    have hexp : r ^ ((n + 2) ^ 2) ≤ r ^ (4 + n) :=
      pow_le_pow_of_le_one hr0 (by linarith) (by nlinarith)
    rw [pow_add] at hexp
    exact hexp
  have hle := hS1.norm_le_of_bounded (geom_tail_bound hr0 hr 4) hb
  have hrw : thetaThree w - (1 + 2 * cexp (π * I * w)) =
      2 * ((jacobiTheta w - 1) / 2 - cexp (π * I * w)) := by
    rw [jacobiTheta_eq_jacobiTheta₂, thetaThree]
    ring
  rw [hrw, norm_mul, Complex.norm_two]
  calc 2 * ‖(jacobiTheta w - 1) / 2 - cexp (π * I * w)‖ ≤ 2 * (r ^ 4 * (1 - r)⁻¹) := by
        gcongr
    _ ≤ 2 * (2 * r ^ 4) := mul_le_mul_of_nonneg_left (tail_le_two_mul hr0 hr 4) (by norm_num)
    _ ≤ 4 * r ^ 3 := by nlinarith [pow_nonneg hr0 3]

theorem norm_jacobiTheta₂_half_sub_le {w : ℂ} (hw : 0 < w.im)
    (hr : Real.exp (-π * w.im) ≤ 1 / 2) :
    ‖jacobiTheta₂ (w / 2) w - (2 + 2 * cexp (π * I * w) ^ 2)‖ ≤
      4 * Real.exp (-π * w.im) ^ 3 := by
  set r := Real.exp (-π * w.im) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hS := (hasSum_jacobiTheta₂_term (w / 2) hw).nat_add_neg_add_one
  have hterm : ∀ n : ℕ, jacobiTheta₂_term n (w / 2) w + jacobiTheta₂_term (-(n + 1)) (w / 2) w =
      2 * cexp (π * I * (((n * (n + 1) : ℕ) : ℝ)) * w) := by
    intro n
    simp only [jacobiTheta₂_term]
    have h1 : 2 * π * I * (n : ℤ) * (w / 2) + π * I * ((n : ℤ) : ℂ) ^ 2 * w =
        π * I * (((n * (n + 1) : ℕ) : ℝ)) * w := by push_cast; ring
    have h2 : 2 * π * I * ((-(n + 1) : ℤ) : ℂ) * (w / 2) + π * I * ((-(n + 1) : ℤ) : ℂ) ^ 2 * w =
        π * I * (((n * (n + 1) : ℕ) : ℝ)) * w := by push_cast; ring
    rw [h1, h2]
    ring
  simp_rw [hterm] at hS
  have hS2 := (hasSum_nat_add_iff' 2).mpr hS
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hS2
  have hb : ∀ n : ℕ, ‖2 * cexp (π * I * ((((n + 2) * (n + 2 + 1) : ℕ) : ℝ)) * w)‖ ≤
      2 * r ^ 3 * r ^ n := by
    intro n
    rw [norm_mul, Complex.norm_two, norm_cexp_pi_I_mul, ← hrdef, Real.rpow_natCast]
    have hexp : r ^ ((n + 2) * (n + 2 + 1)) ≤ r ^ (3 + n) :=
      pow_le_pow_of_le_one hr0 (by linarith) (by nlinarith)
    rw [pow_add] at hexp
    calc 2 * r ^ ((n + 2) * (n + 2 + 1)) ≤ 2 * (r ^ 3 * r ^ n) := by gcongr
      _ = 2 * r ^ 3 * r ^ n := by ring
  have hg : HasSum (fun n : ℕ => 2 * r ^ 3 * r ^ n) (2 * r ^ 3 * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left (2 * r ^ 3)
  have hle := hS2.norm_le_of_bounded hg hb
  have hrw : jacobiTheta₂ (w / 2) w - (2 + 2 * cexp (π * I * w) ^ 2) =
      jacobiTheta₂ (w / 2) w -
        (2 * cexp (π * I * (((0 * (0 + 1) : ℕ) : ℝ)) * w) +
          2 * cexp (π * I * (((1 * (1 + 1) : ℕ) : ℝ)) * w)) := by
    have h0 : cexp (π * I * (((0 * (0 + 1) : ℕ) : ℝ)) * w) = 1 := by simp
    have h1 : cexp (π * I * (((1 * (1 + 1) : ℕ) : ℝ)) * w) = cexp (π * I * w) ^ 2 := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h0, h1]
    ring
  rw [hrw]
  have hJ : jacobiTheta₂ (w / 2) w = ∑' n : ℤ, jacobiTheta₂_term n (w / 2) w := rfl
  calc _ ≤ 2 * r ^ 3 * (1 - r)⁻¹ := hle
    _ ≤ 2 * r ^ 3 * 2 := by gcongr; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    _ = 4 * r ^ 3 := by ring

/-! ## Expansions on `ℍ` -/

theorem cuspS_eq (τ : ℍ) : cuspS τ = cexp (π * I * (τ : ℂ)) := rfl

theorem hasExp3_thetaThree : HasExp3 (fun τ : ℍ => thetaThree τ) 1 2 0 := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_norm_cuspS_le_half] with τ hτ
  have hr : Real.exp (-π * (τ : ℂ).im) ≤ 1 / 2 := by
    rw [UpperHalfPlane.coe_im, ← norm_cuspS]
    exact hτ
  have h := norm_thetaThree_sub_le τ.im_pos hr
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_cuspS]
  simpa [cuspS] using h

theorem hasExp3_thetaFour : HasExp3 (fun τ : ℍ => thetaFour τ) 1 (-2) 0 := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_norm_cuspS_le_half] with τ hτ
  have hw : 0 < ((τ : ℂ) + 1).im := by simpa using τ.im_pos
  have hr : Real.exp (-π * ((τ : ℂ) + 1).im) ≤ 1 / 2 := by
    rw [show ((τ : ℂ) + 1).im = τ.im by simp, ← norm_cuspS]
    exact hτ
  have h := norm_thetaThree_sub_le hw hr
  rw [thetaThree_add_one] at h
  have hs : cexp (π * I * ((τ : ℂ) + 1)) = -cuspS τ := by
    rw [cuspS, mul_add, Complex.exp_add, mul_one, Complex.exp_pi_mul_I]
    ring
  rw [hs] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_cuspS]
  have him : ((τ : ℂ) + 1).im = τ.im := by simp
  rw [him] at h
  calc ‖thetaFour τ - (1 + -2 * cuspS τ + 0 * cuspS τ ^ 2)‖
      = ‖thetaFour τ - (1 + 2 * -cuspS τ)‖ := by ring_nf
    _ ≤ 4 * Real.exp (-π * τ.im) ^ 3 := h

/-- `J₂(τ) = jacobiTheta₂ (τ/2) τ = Σₙ s^{n²+n}`. -/
theorem hasExp3_jacobiTheta₂_half :
    HasExp3 (fun τ : ℍ => jacobiTheta₂ ((τ : ℂ) / 2) τ) 2 0 2 := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_norm_cuspS_le_half] with τ hτ
  have hr : Real.exp (-π * (τ : ℂ).im) ≤ 1 / 2 := by
    rw [UpperHalfPlane.coe_im, ← norm_cuspS]
    exact hτ
  have h := norm_jacobiTheta₂_half_sub_le τ.im_pos hr
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_cuspS]
  simpa [cuspS] using h

theorem thetaV_eq_cuspS_mul (τ : ℍ) :
    thetaV τ = cuspS τ * jacobiTheta₂ ((τ : ℂ) / 2) τ ^ 4 := by
  rw [thetaV, thetaTwo, mul_pow, cuspS, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hasExp3_thetaU : HasExp3 thetaU 1 8 24 :=
  (hasExp3_thetaThree.pow.pow).congr_fun (fun τ => by simp only [thetaU]; ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_thetaW : HasExp3 thetaW 1 (-8) 24 :=
  (hasExp3_thetaFour.pow.pow).congr_fun (fun τ => by simp only [thetaW]; ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_thetaV : HasExp3 thetaV 0 16 0 :=
  (HasExp3.cuspS'.mul (hasExp3_jacobiTheta₂_half.pow.pow)).congr_fun
    (fun τ => by rw [thetaV_eq_cuspS_mul]; ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

/-! ## Eisenstein series and the discriminant -/

theorem hasExp3_eisensteinFour : HasExp3 (fun τ : ℍ => ModularForm.E₄ τ) 1 0 240 :=
  ((((hasExp3_thetaU.pow).add (hasExp3_thetaV.pow)).add (hasExp3_thetaW.pow)).const_mul
    (1 / 2 : ℂ)).congr_fun (fun τ => by rw [eisensteinFour_eq_theta]; ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_eisensteinSix : HasExp3 (fun τ : ℍ => ModularForm.E₆ τ) 1 0 (-504) :=
  ((((hasExp3_thetaU.add hasExp3_thetaV).mul (hasExp3_thetaU.add hasExp3_thetaW)).mul
    (hasExp3_thetaW.sub hasExp3_thetaV)).const_mul (1 / 2 : ℂ)).congr_fun
    (fun τ => by rw [eisensteinSix_eq_theta]; ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_discriminant :
    HasExp3 (fun τ : ℍ => ModularForm.discriminant τ) 0 0 1 :=
  ((((hasExp3_thetaU.mul hasExp3_thetaV).mul hasExp3_thetaW).pow).const_mul
    (1 / 256 : ℂ)).congr_fun
    (fun τ => by
      have h := thetaProductSq_eq_discriminant τ
      simp only [thetaProductSq] at h
      linear_combination (1 / 256 : ℂ) * h)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

/-! ## The logarithms -/

/-- `μ = λ / (16 s) = J₂⁴ / (16 U)`. -/
theorem hasExp3_lambdaRatio :
    HasExp3 (fun τ : ℍ => jacobiTheta₂ ((τ : ℂ) / 2) τ ^ 4 / 16 * (thetaU τ)⁻¹) 1 (-8) 44 :=
  (((hasExp3_jacobiTheta₂_half.pow.pow).const_mul (1 / 16 : ℂ)).mul
    (hasExp3_thetaU.inv one_ne_zero)).congr_fun (fun τ => by ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

/-- `L - πiτ - 4 log 2 = -8 s + 12 s² + O(s³)`. -/
theorem hasExp3_ckmrvL_sub :
    HasExp3 (fun τ : ℍ => ckmrvL τ - π * I * τ - 4 * Real.log 2) 0 (-8) 12 := by
  refine (hasExp3_lambdaRatio.log_of_exp (fun τ => ?_) ?_).congr_coeff rfl rfl (by norm_num)
  · have hU : thetaU τ ≠ 0 := thetaU_ne_zero τ
    have hs : cuspS τ ≠ 0 := cuspS_ne_zero τ
    rw [Complex.exp_sub, Complex.exp_sub, exp_ckmrvL, modularLambda, thetaV_eq_cuspS_mul]
    have h2 : cexp (4 * (Real.log 2 : ℂ)) = 16 := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
      rw [show (4 : ℝ) * Real.log 2 = Real.log 16 by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num]
      rw [Real.exp_log (by norm_num)]
      norm_num
    rw [h2, ← cuspS_eq]
    field_simp
  · simpa using tendsto_ckmrvL_sub_atImInfty.sub_const (4 * Real.log 2 : ℂ)

/-- `L_S = -16 s + O(s³)`. -/
theorem hasExp3_ckmrvLS : HasExp3 ckmrvLS 0 (-16) 0 := by
  have hWU : HasExp3 (fun τ : ℍ => thetaW τ * (thetaU τ)⁻¹) 1 (-16) 128 :=
    (hasExp3_thetaW.mul (hasExp3_thetaU.inv one_ne_zero)).congr_coeff
      (by norm_num) (by norm_num) (by norm_num)
  refine (hWU.log_of_exp (fun τ => ?_) tendsto_ckmrvLS_atImInfty).congr_coeff rfl rfl
    (by norm_num)
  rw [exp_ckmrvLS, one_sub_modularLambda, div_eq_mul_inv]

end E8Leech
