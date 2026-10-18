import Riesz.SmoothQuadrature
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! An affine change of variables turns the unit-interval certificate into a cell estimate. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem iteratedDeriv_six_affine {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f) (a w t : ℝ) :
    iteratedDeriv 6 (fun x => f (a+w*x)) t = w^6*iteratedDeriv 6 f (a+w*t) := by
  have hs : ContDiff ℝ 6 (fun x => f (a+x)) := by fun_prop
  have h := iteratedDeriv_comp_const_mul hs w
  rw [iteratedDeriv_comp_const_add] at h
  exact congrFun h t

/-- Unnormalized integral error on a cell of width w, with its exact seventh-power scaling. -/
theorem quadrature_cell_sixth_order_bound {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 6 f) (a w : ℝ) (hw : 0 < w) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc a (a+w), |iteratedDeriv 6 f x| ≤ M) :
    |w*quadrature m (fun t => f (a+w*t)) - ∫ x in a..a+w, f x| ≤
      (64/(m : ℝ)^6)*w^7*M := by
  have hg : ContDiff ℝ 6 (fun t => f (a+w*t)) := by fun_prop
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv 6 (fun x => f (a+w*x)) t| ≤ w^6*M := by
    intro t ht
    have hx : a+w*t ∈ Set.Icc a (a+w) := by
      constructor <;> nlinarith [ht.1, ht.2]
    rw [iteratedDeriv_six_affine hf a w t, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ w^6)]
    exact mul_le_mul_of_nonneg_left (hM _ hx) (by positivity)
  have h := quadrature_sixth_order_bound hm hg (w^6*M) hb
  have hi : (∫ x in a..a+w, f x) = w*(∫ t in (0 : ℝ)..1, f (a+w*t)) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f w a
  rw [hi, ← mul_sub, abs_mul, abs_of_pos hw]
  calc
    _ ≤ w*((64/(m : ℝ)^6)*(w^6*M)) := mul_le_mul_of_nonneg_left h hw.le
    _ = (64/(m : ℝ)^6)*w^7*M := by ring

#print axioms iteratedDeriv_six_affine
#print axioms quadrature_cell_sixth_order_bound

end SphericalRiesz.Boundary
