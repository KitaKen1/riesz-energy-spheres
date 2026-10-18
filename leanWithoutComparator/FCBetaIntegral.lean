import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
noncomputable section
open Set MeasureTheory
namespace RieszSphereFC

theorem real_beta_scaled {u v a : ℝ} (hu : 0 < u) (hv : 0 < v) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, x ^ (u - 1) * (a - x) ^ (v - 1)) =
      a ^ (u + v - 1) * Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  have hL : (∫ x in (0 : ℝ)..a, (x : ℂ) ^ ((u : ℂ) - 1) *
      ((a : ℂ) - x) ^ ((v : ℂ) - 1)) =
      ((∫ x in (0 : ℝ)..a, x ^ (u - 1) * (a - x) ^ (v - 1) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_of_le ha.le,
      ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
    push_cast
    rfl
  apply Complex.ofReal_injective
  rw [← hL, Complex.betaIntegral_scaled _ _ ha,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hu) (by simpa using hv)]
  have he : (u : ℂ) + v - 1 = ((u + v - 1 : ℝ) : ℂ) := by push_cast; rfl
  have hs : (u : ℂ) + v = ((u + v : ℝ) : ℂ) := by push_cast; rfl
  rw [he, hs, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_cpow ha.le]
  push_cast
  ring

theorem pole_beta_riesz_integral (k : ℕ) {s : ℝ} (hs : s < 2 * (k : ℝ) + 2) :
    (∫ v in Ioo (0 : ℝ) 2, (2 * v) ^ (-s / 2) * v ^ k * (2 - v) ^ k) =
      2 ^ (2 * (k : ℝ) + 1 - s) * Real.Gamma ((k : ℝ) + 1 - s / 2) *
        Real.Gamma ((k : ℝ) + 1) / Real.Gamma (2 * (k : ℝ) + 2 - s / 2) := by
  let u : ℝ := (k : ℝ) + 1 - s / 2
  let w : ℝ := (k : ℝ) + 1
  have hu : 0 < u := by dsimp [u]; linarith
  have hw : 0 < w := by dsimp [w]; positivity
  have hb := real_beta_scaled hu hw (show (0 : ℝ) < 2 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 by norm_num), integral_Ioc_eq_integral_Ioo] at hb
  have he : (∫ v in Ioo (0 : ℝ) 2, (2 * v) ^ (-s / 2) * v ^ k * (2 - v) ^ k) =
      2 ^ (-s / 2) * ∫ v in Ioo (0 : ℝ) 2, v ^ (u - 1) * (2 - v) ^ (w - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    have hu' : u - 1 = -s / 2 + (k : ℝ) := by dsimp [u]; ring
    have hw' : w - 1 = (k : ℝ) := by dsimp [w]; ring
    dsimp only
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hv.1.le, hu', hw',
      Real.rpow_add hv.1, Real.rpow_natCast, Real.rpow_natCast]
    ring
  rw [he, hb]
  have hExp : -s / 2 + (u + w - 1) = 2 * (k : ℝ) + 1 - s := by dsimp [u, w]; ring
  have hSum : u + w = 2 * (k : ℝ) + 2 - s / 2 := by dsimp [u, w]; ring
  calc
    _ = (2 ^ (-s / 2) * 2 ^ (u + w - 1)) * Real.Gamma u * Real.Gamma w /
        Real.Gamma (u + w) := by ring
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hExp, hSum]

end RieszSphereFC
