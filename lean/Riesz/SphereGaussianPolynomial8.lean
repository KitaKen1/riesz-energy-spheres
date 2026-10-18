import Riesz.SphereGaussianPolar8
import Riesz.GaussianMellin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The actual Gaussian background as a finite exponential-polynomial integral.
The cubic Gamma moment gives the uniform decay without a closed-form asymptotic. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def polePolynomialGaussian8 (t v : ℝ) : ℝ :=
  Real.exp (-(2*t*v))*v^3*(2-v)^3

theorem polePolynomialGaussian8_continuous (t : ℝ) : Continuous (polePolynomialGaussian8 t) := by
  unfold polePolynomialGaussian8
  fun_prop

theorem poleHeight8_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun u : ℝ => 1-Real.cos u) (Real.sin θ) θ := by
  convert (Real.hasDerivAt_cos θ).neg.const_add 1 using 1 <;> simp

theorem poleAngularGaussian8_polynomial (t θ : ℝ) :
    poleAngularGaussian8 t θ = polePolynomialGaussian8 t (1-Real.cos θ)*Real.sin θ := by
  have hs : Real.sin θ^2 = (1-Real.cos θ)*(1+Real.cos θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs7 : Real.sin θ^7 = Real.sin θ*(Real.sin θ^2)^3 := by ring
  unfold poleAngularGaussian8 polePolynomialGaussian8
  rw [hs7, hs]
  have he : -(t*(2-2*Real.cos θ)) = -(2*t*(1-Real.cos θ)) := by ring
  rw [he]
  ring

theorem poleAngularGaussian8_interval_polynomial (t : ℝ) :
    (∫ θ in (0:ℝ)..Real.pi, poleAngularGaussian8 t θ) =
      ∫ v in (0:ℝ)..2, polePolynomialGaussian8 t v := by
  simp_rw [poleAngularGaussian8_polynomial]
  have h := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := Real.pi)
    (f := fun θ : ℝ => 1-Real.cos θ) (f' := Real.sin) (g := polePolynomialGaussian8 t)
    (fun θ _ => poleHeight8_hasDerivAt θ) Real.continuous_sin.continuousOn
    (polePolynomialGaussian8_continuous t)
  simpa only [Function.comp_def, Real.cos_zero, Real.cos_pi, sub_self,
    sub_neg_eq_add, one_add_one_eq_two] using h

theorem poleAngularGaussian8_set_polynomial (t : ℝ) :
    (∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian8 t θ) =
      ∫ v in (0:ℝ)..2, polePolynomialGaussian8 t v := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact poleAngularGaussian8_interval_polynomial t

theorem sphereGaussianBackground8_polynomial {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground8 t =
      (35/32:ℝ)*∫ v in (0:ℝ)..2, polePolynomialGaussian8 t v := by
  rw [sphereGaussianBackground8_angular ht, poleAngularGaussian8_set_polynomial]

theorem sphereGaussianBackground8_polynomial_set {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground8 t =
      (35/32:ℝ)*∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian8 t v := by
  rw [sphereGaussianBackground8_polynomial ht,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2), integral_Ioc_eq_integral_Ioo]

theorem polePolynomialGaussian8_nonneg (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    0 ≤ polePolynomialGaussian8 t v := by
  unfold polePolynomialGaussian8
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv.1 _))
    (pow_nonneg (sub_nonneg.mpr hv.2) _)

theorem polePolynomialGaussian8_le_cubic (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    polePolynomialGaussian8 t v ≤ 8*(v^3*Real.exp (-(2*t*v))) := by
  have hp : (2-v)^3 ≤ (8:ℝ) := by
    have h := pow_le_pow_left₀ (sub_nonneg.mpr hv.2) (show 2-v ≤ (2:ℝ) by linarith [hv.1]) 3
    norm_num at h
    exact h
  unfold polePolynomialGaussian8
  calc
    _ ≤ Real.exp (-(2*t*v))*v^3*8 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv.1 3))
    _ = _ := by ring

theorem cubicGaussian8_integral {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ in Ioi 0, v^3*Real.exp (-(2*t*v))) = 3/(8*t^4) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 4) (r := 2*t) (by norm_num) (by positivity)
  have h' : (∫ v : ℝ in Ioi 0, v^3*Real.exp (-(2*t*v))) = (1/(2*t))^4*6 := by
    simpa only [show (4:ℝ)-1 = 3 by norm_num, Real.rpow_ofNat,
      show Real.Gamma 4 = 6 by norm_num] using h
  rw [h']
  field_simp
  ring

theorem cubicGaussian8_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => v^3*Real.exp (-(2*t*v))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [cubicGaussian8_integral ht]
  exact (by positivity : (0:ℝ) < 3/(8*t^4)).ne'

theorem sphereGaussianBackground8_decay {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground8 t ≤ (105/32:ℝ)/t^4 := by
  have hf := cubicGaussian8_integrable ht
  have hg : IntegrableOn (polePolynomialGaussian8 t) (Ioo (0:ℝ) 2) :=
    (polePolynomialGaussian8_continuous t).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcap : (∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian8 t v) ≤
      ∫ v in Ioo (0:ℝ) 2, 8*(v^3*Real.exp (-(2*t*v))) :=
    setIntegral_mono_on hg ((hf.mono_set Ioo_subset_Ioi_self).const_mul 8)
      measurableSet_Ioo (fun v hv => polePolynomialGaussian8_le_cubic t ⟨hv.1.le,hv.2.le⟩)
  have htail : (∫ v in Ioo (0:ℝ) 2, v^3*Real.exp (-(2*t*v))) ≤
      ∫ v in Ioi (0:ℝ), v^3*Real.exp (-(2*t*v)) := by
    apply setIntegral_mono_set hf
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le
    · exact .of_forall fun v hv => hv.1
  rw [sphereGaussianBackground8_polynomial_set ht.le]
  calc
    _ ≤ (35/32:ℝ)*∫ v in Ioo (0:ℝ) 2, 8*(v^3*Real.exp (-(2*t*v))) :=
      mul_le_mul_of_nonneg_left hcap (by norm_num)
    _ = (35/32:ℝ)*8*(∫ v in Ioo (0:ℝ) 2, v^3*Real.exp (-(2*t*v))) := by
      rw [integral_const_mul]; ring
    _ ≤ (35/32:ℝ)*8*(∫ v in Ioi (0:ℝ), v^3*Real.exp (-(2*t*v))) :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = _ := by rw [cubicGaussian8_integral ht]; field_simp; ring

theorem sphereGaussianBackground8_min_bound {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground8 t ≤ min 1 ((105/32:ℝ)/t^4) :=
  le_min (sphereGaussianBackground8_le_one ht.le) (sphereGaussianBackground8_decay ht)

theorem sphereGaussianBackground8_area_decay {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground8 t ≤ (Real.pi^4/sphereArea8.real univ)/t^4 := by
  have hC : Real.pi^4/sphereArea8.real univ = (105/32:ℝ) := by
    rw [sphereArea8_mass_real]
    have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
  rw [hC]
  exact sphereGaussianBackground8_decay ht

end SphericalRiesz
