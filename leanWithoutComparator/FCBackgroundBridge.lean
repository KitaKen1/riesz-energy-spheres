import FCPoleBetaLaw
import FCBetaIntegral
import Riesz.SphereRieszLower2
import Riesz.SphereRieszLower24

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
noncomputable section
open Set MeasureTheory
namespace RieszSphereFC

private theorem beta_background_formula (k : ℕ) {c s : ℝ}
    (hconst : c * Real.Gamma ((k : ℝ) + 1) * Real.sqrt Real.pi =
      Real.Gamma ((k : ℝ) + 1 + 1 / 2)) (hs : s < 2 * (k : ℝ) + 2) :
    c * (∫ v in Ioo (0 : ℝ) 2, (2 * v) ^ (-s / 2) * v ^ k * (2 - v) ^ k) =
      rieszBackground (2 * k + 2) s := by
  rw [pole_beta_riesz_integral k hs]
  unfold rieszBackground
  push_cast
  rw [show (2 * (k : ℝ) + 2 + 1) / 2 = (k : ℝ) + 1 + 1 / 2 by ring,
    show (2 * (k : ℝ) + 2 - s) / 2 = (k : ℝ) + 1 - s / 2 by ring,
    show 2 * (k : ℝ) + 2 - s - 1 = 2 * (k : ℝ) + 1 - s by ring]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hc : c * Real.Gamma ((k : ℝ) + 1) =
      Real.Gamma ((k : ℝ) + 1 + 1 / 2) / Real.sqrt Real.pi :=
    (eq_div_iff hp).mpr hconst
  calc
    _ = 2 ^ (2 * (k : ℝ) + 1 - s) * Real.Gamma ((k : ℝ) + 1 - s / 2) *
        (c * Real.Gamma ((k : ℝ) + 1)) / Real.Gamma (2 * (k : ℝ) + 2 - s / 2) := by ring
    _ = _ := by
      rw [hc]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem gamma_constant_two :
    (1 / 2 : ℝ) * Real.Gamma (((0 : ℕ) : ℝ) + 1) * Real.sqrt Real.pi =
      Real.Gamma (((0 : ℕ) : ℝ) + 1 + 1 / 2) := by
  rw [Real.Gamma_nat_add_one_add_half 0]
  norm_num
  ring

private theorem gamma_constant_eight :
    (35 / 32 : ℝ) * Real.Gamma (((3 : ℕ) : ℝ) + 1) * Real.sqrt Real.pi =
      Real.Gamma (((3 : ℕ) : ℝ) + 1 + 1 / 2) := by
  rw [Real.Gamma_nat_add_one_add_half 3, Real.Gamma_nat_eq_factorial 3]
  norm_num [Nat.doubleFactorial]
  ring

private theorem gamma_constant_twenty_four :
    (2028117 / 1048576 : ℝ) * Real.Gamma (((11 : ℕ) : ℝ) + 1) * Real.sqrt Real.pi =
      Real.Gamma (((11 : ℕ) : ℝ) + 1 + 1 / 2) := by
  rw [Real.Gamma_nat_add_one_add_half 11, Real.Gamma_nat_eq_factorial 11]
  norm_num [Nat.doubleFactorial]
  ring

theorem rieszBackground_two_eq {s : ℝ} (hs : s < 2) :
    rieszBackground 2 s = ∫ p : Sphere 2 × Sphere 2, dist p.1 p.2 ^ (-s)
      ∂((uniform 2).prod (uniform 2)) := by
  have h := sphere_riesz_integral_eq_beta (d := 2) (k := 0)
    (c := 1 / 2) (by norm_num) (fun t ht => by
      change SphericalRiesz.sphereGaussianBackground2 t = _
      simpa only [SphericalRiesz.polePolynomialGaussian2, pow_zero, mul_one] using
        SphericalRiesz.sphereGaussianBackground2_polynomial_set ht.le) s
  rw [h]
  exact (beta_background_formula 0 gamma_constant_two (by norm_num only [Nat.cast_ofNat] <;> linarith)).symm

theorem rieszBackground_eight_eq {s : ℝ} (hs : s < 8) :
    rieszBackground 8 s = ∫ p : Sphere 8 × Sphere 8, dist p.1 p.2 ^ (-s)
      ∂((uniform 8).prod (uniform 8)) := by
  have h := sphere_riesz_integral_eq_beta (d := 8) (k := 3)
    (c := 35 / 32) (by norm_num) (fun t ht => by
      change SphericalRiesz.sphereGaussianBackground8 t = _
      simpa only [SphericalRiesz.polePolynomialGaussian8] using
        SphericalRiesz.sphereGaussianBackground8_polynomial_set ht.le) s
  rw [h]
  exact (beta_background_formula 3 gamma_constant_eight (by norm_num only [Nat.cast_ofNat] <;> linarith)).symm

theorem rieszBackground_twenty_four_eq {s : ℝ} (hs : s < 24) :
    rieszBackground 24 s = ∫ p : Sphere 24 × Sphere 24, dist p.1 p.2 ^ (-s)
      ∂((uniform 24).prod (uniform 24)) := by
  have h := sphere_riesz_integral_eq_beta (d := 24) (k := 11)
    (c := 2028117 / 1048576) (by norm_num) (fun t ht => by
      change SphericalRiesz.sphereGaussianBackground24 t = _
      simpa only [SphericalRiesz.polePolynomialGaussian24] using
        SphericalRiesz.sphereGaussianBackground24_polynomial_set ht.le) s
  rw [h]
  exact (beta_background_formula 11 gamma_constant_twenty_four (by norm_num only [Nat.cast_ofNat] <;> linarith)).symm

end RieszSphereFC
