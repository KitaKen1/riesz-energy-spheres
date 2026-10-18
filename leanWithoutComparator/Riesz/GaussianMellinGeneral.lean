import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! Gaussian Mellin representation of every positive Riesz power.

`r^(-s) = π^(s/2) / Γ(s/2) * ∫_0^∞ t^(s/2-1) exp(-π r² t) dt` for `s > 0`, `r > 0`.
This is the exponent-general form of `inverse_fourth_gaussian_integral` (`s = 4`),
needed for the all-exponent stages (HP, P24). No Epstein continuation is used. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz

theorem rpow_neg_gaussian_mellin_integral {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi 0, t^(s/2-1) * Real.exp (-(Real.pi*r^2*t)) =
      Real.Gamma (s/2) * Real.pi^(-(s/2)) * r^(-s) := by
  have hpr : 0 < Real.pi*r^2 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s/2) (r := Real.pi*r^2)
    (by positivity) hpr
  rw [h, one_div, Real.inv_rpow hpr.le, Real.mul_rpow Real.pi_pos.le (sq_nonneg r)]
  have hr2 : (r^2)^(s/2) = r^s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
    ring_nf
  rw [hr2, mul_inv, Real.rpow_neg Real.pi_pos.le, Real.rpow_neg hr.le]
  ring

/-- The normalized Mellin representation `r^(-s) = π^(s/2)/Γ(s/2) ∫ t^(s/2-1) e^(-π r² t) dt`. -/
theorem rpow_neg_eq_gaussian_mellin {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    r^(-s) = Real.pi^(s/2) / Real.Gamma (s/2) *
      ∫ t : ℝ in Set.Ioi 0, t^(s/2-1) * Real.exp (-(Real.pi*r^2*t)) := by
  rw [rpow_neg_gaussian_mellin_integral hs hr]
  have hΓ : Real.Gamma (s/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hπ : Real.pi^(s/2) * Real.pi^(-(s/2)) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]
    simp
  calc r^(-s) = (Real.pi^(s/2) * Real.pi^(-(s/2))) * (Real.Gamma (s/2) / Real.Gamma (s/2)) *
        r^(-s) := by rw [hπ, div_self hΓ]; ring
    _ = Real.pi^(s/2) / Real.Gamma (s/2) *
        (Real.Gamma (s/2) * Real.pi^(-(s/2)) * r^(-s)) := by ring

/-- Consistency with the fixed exponent `s = 4`. -/
theorem rpow_neg_four_gaussian_mellin {r : ℝ} (hr : 0 < r) :
    r^(-(4:ℝ)) = Real.pi^2 *
      ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(Real.pi*r^2*t)) := by
  have h := rpow_neg_eq_gaussian_mellin (s := 4) (by norm_num) hr
  have e1 : (4:ℝ)/2 = 2 := by norm_num
  rw [e1] at h
  have hΓ : Real.Gamma 2 = 1 := by norm_num
  rw [hΓ, div_one, Real.rpow_two] at h
  rw [h]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only
  rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]

#print axioms rpow_neg_gaussian_mellin_integral
#print axioms rpow_neg_eq_gaussian_mellin
#print axioms rpow_neg_four_gaussian_mellin

end SphericalRiesz
