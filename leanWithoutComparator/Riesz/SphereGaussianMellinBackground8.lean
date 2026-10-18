import Riesz.SphereGaussianPolynomial8
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual continuum Gaussian/Riesz Mellin exchange in dimension eight.
The checked sphere background formula reduces Fubini to two real variables.
No sphere height marginal or sharp Gaussian certificate is assumed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem linearGaussianMoment_integral {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t*Real.exp (-(r*t))) = r⁻¹^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := r) (by norm_num) hr
  simpa only [show (2:ℝ)-1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    show Real.Gamma 2 = 1 by norm_num, mul_one, one_div] using h

theorem linearGaussianMoment_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t*Real.exp (-(r*t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [linearGaussianMoment_integral hr]
  exact (by positivity : (0:ℝ) < r⁻¹^2).ne'

def sphereGaussianMellinJoint8 (p : ℝ × ℝ) : ℝ :=
  p.2*polePolynomialGaussian8 p.2 p.1

theorem sphereGaussianMellinJoint8_continuous : Continuous sphereGaussianMellinJoint8 := by
  unfold sphereGaussianMellinJoint8 polePolynomialGaussian8
  fun_prop

theorem sphereGaussianMellinJoint8_nonneg {v t : ℝ}
    (hv : v ∈ Icc (0:ℝ) 2) (ht : 0 ≤ t) :
    0 ≤ sphereGaussianMellinJoint8 (v,t) :=
  mul_nonneg ht (polePolynomialGaussian8_nonneg t hv)

theorem sphereGaussianMellinJoint8_row_integrable {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun t : ℝ => sphereGaussianMellinJoint8 (v,t)) (Ioi 0) := by
  have hi := (linearGaussianMoment_integrable (by positivity : 0 < 2*v)).const_mul
    (v^3*(2-v)^3)
  change Integrable (fun t : ℝ => sphereGaussianMellinJoint8 (v,t)) (volume.restrict (Ioi 0))
  convert hi using 1
  ext t
  unfold sphereGaussianMellinJoint8 polePolynomialGaussian8
  have he : -(2*t*v) = -(2*v*t) := by ring
  rw [he]
  ring

theorem sphereGaussianMellinJoint8_row_integral {v : ℝ} (hv : 0 < v) :
    (∫ t : ℝ in Ioi 0, sphereGaussianMellinJoint8 (v,t)) = v*(2-v)^3/4 := by
  have he : (fun t : ℝ => sphereGaussianMellinJoint8 (v,t)) =
      (fun t : ℝ => (v^3*(2-v)^3)*(t*Real.exp (-(2*v*t)))) := by
    ext t
    unfold sphereGaussianMellinJoint8 polePolynomialGaussian8
    have he : -(2*t*v) = -(2*v*t) := by ring
    rw [he]
    ring
  rw [he, integral_const_mul, linearGaussianMoment_integral (by positivity : 0 < 2*v)]
  field_simp [hv.ne']
  ring

theorem sphereGaussianMellinJoint8_row_norm_integral {v : ℝ}
    (hv : v ∈ Ioo (0:ℝ) 2) :
    (∫ t : ℝ in Ioi 0, ‖sphereGaussianMellinJoint8 (v,t)‖) = v*(2-v)^3/4 := by
  rw [← sphereGaussianMellinJoint8_row_integral hv.1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact Real.norm_of_nonneg (sphereGaussianMellinJoint8_nonneg ⟨hv.1.le,hv.2.le⟩ ht.le)

theorem sphereGaussianMellinJoint8_integrable :
    Integrable sphereGaussianMellinJoint8
      ((volume.restrict (Ioo (0:ℝ) 2)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff sphereGaussianMellinJoint8_continuous.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact sphereGaussianMellinJoint8_row_integrable hv.1
  · have hi : IntegrableOn (fun v : ℝ => v*(2-v)^3/4) (Ioo (0:ℝ) 2) :=
      (show Continuous (fun v : ℝ => v*(2-v)^3/4) by fun_prop).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact (sphereGaussianMellinJoint8_row_norm_integral hv).symm

def sphereGaussianMellinPrimitive8 (v : ℝ) : ℝ :=
  v^2-v^3+(3/8:ℝ)*v^4-v^5/20

theorem sphereGaussianMellinPrimitive8_hasDerivAt (v : ℝ) :
    HasDerivAt sphereGaussianMellinPrimitive8 (v*(2-v)^3/4) v := by
  have h := ((((hasDerivAt_id v).pow 2).sub ((hasDerivAt_id v).pow 3)).add
    (((hasDerivAt_id v).pow 4).const_mul (3/8:ℝ))).sub
      (((hasDerivAt_id v).pow 5).div_const 20)
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

theorem sphereGaussianMellin_row_polynomial_integral :
    (∫ v : ℝ in Ioo 0 2, v*(2-v)^3/4) = 2/5 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => sphereGaussianMellinPrimitive8_hasDerivAt v)
      ((show Continuous (fun v : ℝ => v*(2-v)^3/4) by fun_prop).intervalIntegrable 0 2)]
  norm_num [sphereGaussianMellinPrimitive8]

theorem sphereGaussianBackground8_weighted_polynomial_ae :
    (fun t : ℝ => t*sphereGaussianBackground8 t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (35/32:ℝ)*(∫ v in Ioo (0:ℝ) 2, sphereGaussianMellinJoint8 (v,t))) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [sphereGaussianBackground8_polynomial_set ht.le]
  simp only [sphereGaussianMellinJoint8]
  rw [integral_const_mul]
  ring

theorem sphereGaussianBackground8_weighted_integrable :
    IntegrableOn (fun t : ℝ => t*sphereGaussianBackground8 t) (Ioi 0) := by
  exact (sphereGaussianMellinJoint8_integrable.integral_prod_right.const_mul (35/32:ℝ)).congr
    sphereGaussianBackground8_weighted_polynomial_ae.symm

theorem sphereGaussianBackground8_mellin_four :
    (∫ t : ℝ in Ioi 0, t*sphereGaussianBackground8 t) = 7/16 := by
  rw [integral_congr_ae sphereGaussianBackground8_weighted_polynomial_ae,
    integral_const_mul, ← integral_prod_symm _ sphereGaussianMellinJoint8_integrable,
    integral_prod _ sphereGaussianMellinJoint8_integrable]
  have he : (∫ v : ℝ in Ioo 0 2, ∫ t : ℝ in Ioi 0, sphereGaussianMellinJoint8 (v,t)) =
      ∫ v : ℝ in Ioo 0 2, v*(2-v)^3/4 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    exact sphereGaussianMellinJoint8_row_integral hv.1
  rw [he, sphereGaussianMellin_row_polynomial_integral]
  norm_num

theorem sphereGaussianBackground8_mellin_eq_riesz :
    (∫ t : ℝ in Ioi 0, t*sphereGaussianBackground8 t) =
      ∫ p : Sphere8 × Sphere8, sphereKernel4 p.1 p.2
        ∂sphereProbability8.prod sphereProbability8 := by
  rw [sphereGaussianBackground8_mellin_four, sphereKernel4_pair_integral_value]

end SphericalRiesz
