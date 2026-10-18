import Riesz.QuadraticKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Order-nine bounds for the fifth coordinate derivative

The explicit rational derivative certificate already checks the answer.
Here the square root of the positive quadratic denominator bounds each
numerator monomial. A fixed coarse constant is sufficient for a face
integral, so no sharp coefficient optimization is required.
-/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

theorem quadraticKernelDerivative_five_bound_sqrt (b c x : ℝ) (hb : 0 ≤ b)
    (hq : 0 < (x-c)^2+b) :
    |quadraticKernelDerivative 5 b c x| ≤ 23040/(Real.sqrt ((x-c)^2+b))^9 := by
  let z : ℝ := x-c
  let q : ℝ := z^2+b
  let p : ℝ := Real.sqrt q
  have hqp : 0 < q := hq
  have hp : 0 < p := Real.sqrt_pos.mpr hqp
  have hpsq : p^2 = q := Real.sq_sqrt hqp.le
  have hzq : z^2 ≤ q := by dsimp only [q]; linarith
  have hbq : b ≤ p^2 := by rw [hpsq]; dsimp only [q]; nlinarith [sq_nonneg z]
  have hz : |z| ≤ p := (sq_le_sq₀ (abs_nonneg z) hp.le).mp (by
    rw [sq_abs, hpsq]
    exact hzq)
  have hz5 : |z|^5 ≤ p^5 := pow_le_pow_left₀ (abs_nonneg z) hz 5
  have hbz3 : b*|z|^3 ≤ p^5 := by
    calc
      _ ≤ p^2*p^3 := mul_le_mul hbq (pow_le_pow_left₀ (abs_nonneg z) hz 3)
        (by positivity) (by positivity)
      _ = _ := by ring
  have hb2z : b^2*|z| ≤ p^5 := by
    calc
      _ ≤ (p^2)^2*p := mul_le_mul (pow_le_pow_left₀ hb hbq 2) hz
        (abs_nonneg z) (by positivity)
      _ = _ := by ring
  have hnum : |-6720*z^5+13440*b*z^3-2880*b^2*z| ≤ 23040*p^5 := by
    calc
      _ ≤ |-6720*z^5+13440*b*z^3|+|2880*b^2*z| := abs_sub _ _
      _ ≤ |-6720*z^5|+|13440*b*z^3|+|2880*b^2*z| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = 6720*|z|^5+13440*b*|z|^3+2880*b^2*|z| := by
        simp only [abs_mul, abs_pow, abs_of_nonneg hb]
        norm_num
      _ ≤ 23040*p^5 := by
        have h1 := mul_le_mul_of_nonneg_left hz5 (by norm_num : (0:ℝ) ≤ 6720)
        have h2 := mul_le_mul_of_nonneg_left hbz3 (by norm_num : (0:ℝ) ≤ 13440)
        have h3 := mul_le_mul_of_nonneg_left hb2z (by norm_num : (0:ℝ) ≤ 2880)
        nlinarith only [h1, h2, h3]
  change |(-6720*z^5+13440*b*z^3-2880*b^2*z)/q^7| ≤ 23040/p^9
  rw [abs_div, abs_of_pos (pow_pos hqp 7)]
  calc
    _ ≤ (23040*p^5)/q^7 := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 23040/p^9 := by rw [← hpsq]; field_simp

theorem quadraticKernelDerivative_five_bound_radius (b c x r : ℝ) (hb : 0 ≤ b)
    (hr : 0 < r) (hsep : r^2 ≤ (x-c)^2+b) :
    |quadraticKernelDerivative 5 b c x| ≤ 23040/r^9 := by
  have hq : 0 < (x-c)^2+b := (sq_pos_of_pos hr).trans_le hsep
  have hp : 0 < Real.sqrt ((x-c)^2+b) := Real.sqrt_pos.mpr hq
  have hrp : r ≤ Real.sqrt ((x-c)^2+b) := (sq_le_sq₀ hr.le hp.le).mp (by
    rw [Real.sq_sqrt hq.le]
    exact hsep)
  calc
    _ ≤ 23040/(Real.sqrt ((x-c)^2+b))^9 :=
      quadraticKernelDerivative_five_bound_sqrt b c x hb hq
    _ ≤ 23040/r^9 := div_le_div_of_nonneg_left (by norm_num) (pow_pos hr 9)
      (pow_le_pow_left₀ hr.le hrp 9)

theorem quadraticKernelDerivative_five_bound_rpow (b c x : ℝ) (hb : 0 ≤ b)
    (hq : 0 < (x-c)^2+b) :
    |quadraticKernelDerivative 5 b c x| ≤ 23040*((x-c)^2+b)^(-(9:ℝ)/2) := by
  have hp : (Real.sqrt ((x-c)^2+b))^9 = ((x-c)^2+b)^((9:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hq.le]
    norm_num
  calc
    _ ≤ 23040/(Real.sqrt ((x-c)^2+b))^9 :=
      quadraticKernelDerivative_five_bound_sqrt b c x hb hq
    _ = _ := by
      rw [hp, show -(9:ℝ)/2 = -((9:ℝ)/2) by ring, Real.rpow_neg hq.le]
      rfl

#print axioms quadraticKernelDerivative_five_bound_sqrt
#print axioms quadraticKernelDerivative_five_bound_radius
#print axioms quadraticKernelDerivative_five_bound_rpow

end SphericalRiesz
