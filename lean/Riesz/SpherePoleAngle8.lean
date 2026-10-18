import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
The angular integral needed for the S8 inverse-fourth pole. A known
polynomial primitive replaces a general beta-integral development.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def poleAngular4 (t : ℝ) : ℝ := Real.sin t ^ 3 * (1 + Real.cos t)^2 / 4

def poleAngularPrimitive4 (t : ℝ) : ℝ :=
  -(Real.cos t / 4 + Real.cos t ^ 2 / 4 - Real.cos t ^ 4 / 8 - Real.cos t ^ 5 / 20)

theorem poleAngular4_continuous : Continuous poleAngular4 := by
  unfold poleAngular4
  fun_prop

theorem poleAngularPrimitive4_hasDerivAt (t : ℝ) :
    HasDerivAt poleAngularPrimitive4 (poleAngular4 t) t := by
  have hc := Real.hasDerivAt_cos t
  have h := (((hc.div_const 4).add ((hc.pow 2).div_const 4)).sub
    ((hc.pow 4).div_const 8)).sub ((hc.pow 5).div_const 20) |>.neg
  convert h using 1
  · rfl
  · have hs : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    change Real.sin t ^ 3 * (1 + Real.cos t)^2 / 4 = _
    calc
      _ = Real.sin t * Real.sin t ^ 2 * (1 + Real.cos t)^2 / 4 := by ring
      _ = _ := by rw [hs]; ring

theorem poleAngular4_intervalIntegral :
    (∫ t in (0 : ℝ)..Real.pi, poleAngular4 t) = 2 / 5 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => poleAngularPrimitive4_hasDerivAt t)
    (poleAngular4_continuous.intervalIntegrable 0 Real.pi)]
  norm_num [poleAngularPrimitive4]

theorem poleAngular4_setIntegral :
    (∫ t in Ioo (0 : ℝ) Real.pi, poleAngular4 t) = 2 / 5 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact poleAngular4_intervalIntegral

theorem poleRadialPower8_setIntegral :
    (∫ r in Ioo (0 : ℝ) 1, r ^ 8) = 1 / 9 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num

theorem poleAngular4_kernel_cancel (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    Real.sin t ^ 7 * (2 - 2 * Real.cos t)⁻¹ ^ 2 = poleAngular4 t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hc : 2 - 2 * Real.cos t ≠ 0 := by
    intro hz
    have he : Real.cos t = 1 := by linarith
    have hh := Real.sin_sq_add_cos_sq t
    rw [he] at hh
    nlinarith [sq_pos_of_pos hs]
  have hs2 : Real.sin t ^ 2 = (1 - Real.cos t) * (1 + Real.cos t) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hp : Real.sin t ^ 7 =
      Real.sin t ^ 3 * ((1 - Real.cos t) * (1 + Real.cos t))^2 := by
    rw [← hs2]
    ring
  rw [hp]
  unfold poleAngular4
  have hc1 : 1 - Real.cos t ≠ 0 := by
    intro hz
    apply hc
    linarith
  field_simp [hc, hc1]
  ring

theorem poleRectangle4_integral :
    (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi,
      p.1 ^ 8 * poleAngular4 p.2) = 2 / 45 := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul (fun r : ℝ => r ^ 8) poleAngular4,
    poleRadialPower8_setIntegral, poleAngular4_setIntegral]
  norm_num

#print axioms poleAngularPrimitive4_hasDerivAt
#print axioms poleAngular4_intervalIntegral
#print axioms poleAngular4_setIntegral
#print axioms poleRadialPower8_setIntegral
#print axioms poleAngular4_kernel_cancel
#print axioms poleRectangle4_integral

end SphericalRiesz
