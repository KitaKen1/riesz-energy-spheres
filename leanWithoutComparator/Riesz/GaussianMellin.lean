import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! The fixed exponent s = 4 requires only the second Gamma moment. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz

/-- No general Mellin-transform or meromorphic Epstein theory is needed here. -/
theorem inverse_fourth_gaussian_integral {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(r^2*t)) = r⁻¹^4 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := r^2) (by norm_num) (sq_pos_of_pos hr)
  have hΓ : Real.Gamma 2 = 1 := by
    norm_num
  norm_num [Real.rpow_two, hΓ] at h
  simpa only [one_div, inv_pow, ← pow_mul] using h

#print axioms inverse_fourth_gaussian_integral

end SphericalRiesz
