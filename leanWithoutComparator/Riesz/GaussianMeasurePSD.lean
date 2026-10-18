import Riesz.GaussianPSD
import Mathlib.MeasureTheory.Integral.Prod

/-!
Gaussian positivity for actual finite measures.  All product integrals are
integrable by boundedness.  The signed difference is represented by a
difference of characteristic functions, without a signed-measure API.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem gaussianKernel_le_one {t : ℝ} (ht : 0 ≤ t) (x y : E) :
    gaussianKernel t x y ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (sq_nonneg _)))

theorem gaussianKernel_product_integrable {t : ℝ} (ht : 0 ≤ t)
    (ρ : Measure (E × E)) [IsFiniteMeasure ρ] :
    Integrable (fun p : E × E => gaussianKernel t p.1 p.2) ρ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold gaussianKernel; fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianKernel_nonneg _ _ _)]
  exact gaussianKernel_le_one ht _ _

def gaussianMeasurePair (t : ℝ) (μ ν : Measure E) : ℝ :=
  ∫ p : E × E, gaussianKernel t p.1 p.2 ∂μ.prod ν

theorem gaussianMeasurePair_iterated {t : ℝ} (ht : 0 ≤ t)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasurePair t μ ν = ∫ x, ∫ y, gaussianKernel t x y ∂ν ∂μ := by
  exact integral_prod _ (gaussianKernel_product_integrable ht (μ.prod ν))

theorem gaussianMeasurePair_symm {t : ℝ} (ht : 0 ≤ t)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasurePair t μ ν = gaussianMeasurePair t ν μ := by
  rw [gaussianMeasurePair_iterated ht, gaussianMeasurePair_iterated ht]
  rw [integral_integral_swap (gaussianKernel_product_integrable ht (μ.prod ν))]
  simp_rw [gaussianKernel_symm t]

theorem charFun_hermitian_product_integrable (r : ℝ)
    (μ ν ρ : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    Integrable (fun z => charFun μ (r • z) * conj (charFun ν (r • z))) ρ := by
  have hμ : StronglyMeasurable (fun z : E => charFun μ (r • z)) :=
    (stronglyMeasurable_charFun (μ := μ)).comp_measurable (by fun_prop)
  have hν : StronglyMeasurable (fun z : E => charFun ν (r • z)) :=
    (stronglyMeasurable_charFun (μ := ν)).comp_measurable (by fun_prop)
  apply (integrable_const (μ.real Set.univ * ν.real Set.univ)).mono'
    ((hμ.mul (Complex.continuous_conj.comp_stronglyMeasurable hν)).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖charFun μ (r • z) * conj (charFun ν (r • z))‖ ≤ μ.real Set.univ * ν.real Set.univ
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (norm_charFun_le _) (norm_charFun_le _) (norm_nonneg _) (by positivity)

theorem inner_phase_mul_conj (r : ℝ) (z x y : E) :
    Complex.exp (⟪x, r • z⟫ * Complex.I) *
      conj (Complex.exp (⟪y, r • z⟫ * Complex.I)) =
      Complex.exp (⟪z, r • (x-y)⟫ * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, inner_smul_right,
    inner_sub_right]
  rw [real_inner_comm z x, real_inner_comm z y]
  push_cast
  ring

/-- One Fubini swap over a finite product measure identifies the whole Hermitian form. -/
theorem charFun_hermitian_product_integral (r : ℝ)
    (μ ν ρ : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    (∫ z, charFun μ (r • z) * conj (charFun ν (r • z)) ∂ρ) =
      ∫ p : E × E, charFun ρ (r • (p.1-p.2)) ∂μ.prod ν := by
  have hphase : Integrable (fun q : E × (E × E) =>
      Complex.exp (⟪q.1, r • (q.2.1-q.2.2)⟫ * Complex.I))
      (ρ.prod (μ.prod ν)) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with q
    simp only [Complex.norm_exp_ofReal_mul_I]
    exact le_rfl
  calc
    _ = ∫ z, ∫ p : E × E,
        Complex.exp (⟪z, r • (p.1-p.2)⟫ * Complex.I) ∂μ.prod ν ∂ρ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [show (fun p : E × E => Complex.exp (⟪z, r • (p.1-p.2)⟫ * Complex.I)) =
          (fun p => Complex.exp (⟪p.1, r • z⟫ * Complex.I) *
            conj (Complex.exp (⟪p.2, r • z⟫ * Complex.I))) from
          funext fun p => (inner_phase_mul_conj r z p.1 p.2).symm,
        integral_prod_mul (fun x : E => Complex.exp (⟪x, r • z⟫ * Complex.I))
          (fun y : E => conj (Complex.exp (⟪y, r • z⟫ * Complex.I))), integral_conj]
      rfl
    _ = ∫ p : E × E, ∫ z,
        Complex.exp (⟪z, r • (p.1-p.2)⟫ * Complex.I) ∂ρ ∂μ.prod ν :=
      integral_integral_swap hphase
    _ = _ := rfl

theorem gaussianMeasurePair_charFun {t : ℝ} (ht : 0 ≤ t)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ z, charFun μ (Real.sqrt (2*t) • z) *
      conj (charFun ν (Real.sqrt (2*t) • z)) ∂stdGaussian E) =
      (gaussianMeasurePair t μ ν : ℂ) := by
  rw [charFun_hermitian_product_integral]
  simp_rw [gaussian_charFun_rescale ht, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  exact integral_complex_ofReal

def gaussianMeasureDefect (t M : ℝ) (μ ν : Measure E) : ℝ :=
  gaussianMeasurePair t μ μ - 2*M*gaussianMeasurePair t μ ν +
    M^2*gaussianMeasurePair t ν ν

/-- The actual diffuse defect is exactly an integral of a squared modulus. -/
theorem gaussianMeasureDefect_eq_normSq {t : ℝ} (ht : 0 ≤ t) (M : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    gaussianMeasureDefect t M μ ν =
      ∫ z, Complex.normSq (charFun μ (Real.sqrt (2*t) • z) -
        (M : ℂ)*charFun ν (Real.sqrt (2*t) • z)) ∂stdGaussian E := by
  let a : E → ℂ := fun z => charFun μ (Real.sqrt (2*t) • z)
  let b : E → ℂ := fun z => charFun ν (Real.sqrt (2*t) • z)
  have haa := charFun_hermitian_product_integrable (Real.sqrt (2*t)) μ μ (stdGaussian E)
  have hab := charFun_hermitian_product_integrable (Real.sqrt (2*t)) μ ν (stdGaussian E)
  have hba := charFun_hermitian_product_integrable (Real.sqrt (2*t)) ν μ (stdGaussian E)
  have hbb := charFun_hermitian_product_integrable (Real.sqrt (2*t)) ν ν (stdGaussian E)
  change Integrable (fun z => a z * conj (a z)) _ at haa
  change Integrable (fun z => a z * conj (b z)) _ at hab
  change Integrable (fun z => b z * conj (a z)) _ at hba
  change Integrable (fun z => b z * conj (b z)) _ at hbb
  have habM : Integrable (fun z => (M:ℂ)*(a z*conj (b z))) (stdGaussian E) :=
    hab.const_mul (M:ℂ)
  have hbaM : Integrable (fun z => (M:ℂ)*(b z*conj (a z))) (stdGaussian E) :=
    hba.const_mul (M:ℂ)
  have hbbM : Integrable (fun z => (M:ℂ)^2*(b z*conj (b z))) (stdGaussian E) :=
    hbb.const_mul ((M:ℂ)^2)
  have hsub : Integrable (fun z => a z*conj (a z) - (M:ℂ)*(a z*conj (b z)))
      (stdGaussian E) := haa.sub habM
  have hsub2 : Integrable (fun z => a z*conj (a z) - (M:ℂ)*(a z*conj (b z)) -
      (M:ℂ)*(b z*conj (a z))) (stdGaussian E) := hsub.sub hbaM
  have heq (z : E) : (Complex.normSq (a z - (M:ℂ)*b z) : ℂ) =
      a z*conj (a z) - (M:ℂ)*(a z*conj (b z)) -
        (M:ℂ)*(b z*conj (a z)) + (M:ℂ)^2*(b z*conj (b z)) := by
    rw [← Complex.mul_conj]
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    ring
  apply Complex.ofReal_injective
  change (gaussianMeasureDefect t M μ ν : ℂ) =
    ((∫ z, Complex.normSq (a z - (M:ℂ)*b z) ∂stdGaussian E : ℝ) : ℂ)
  rw [← integral_complex_ofReal]
  simp_rw [heq]
  rw [integral_add hsub2 hbbM, integral_sub hsub hbaM, integral_sub haa habM]
  simp only [integral_const_mul]
  change _ = (∫ z, charFun μ (Real.sqrt (2*t) • z) *
        conj (charFun μ (Real.sqrt (2*t) • z)) ∂stdGaussian E) -
      (M:ℂ)*(∫ z, charFun μ (Real.sqrt (2*t) • z) *
        conj (charFun ν (Real.sqrt (2*t) • z)) ∂stdGaussian E) -
      (M:ℂ)*(∫ z, charFun ν (Real.sqrt (2*t) • z) *
        conj (charFun μ (Real.sqrt (2*t) • z)) ∂stdGaussian E) +
      (M:ℂ)^2*(∫ z, charFun ν (Real.sqrt (2*t) • z) *
        conj (charFun ν (Real.sqrt (2*t) • z)) ∂stdGaussian E)
  rw [gaussianMeasurePair_charFun ht, gaussianMeasurePair_charFun ht,
    gaussianMeasurePair_charFun ht, gaussianMeasurePair_charFun ht,
    gaussianMeasurePair_symm ht ν μ]
  unfold gaussianMeasureDefect
  push_cast
  ring

theorem gaussianMeasureDefect_nonneg {t : ℝ} (ht : 0 ≤ t) (M : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ gaussianMeasureDefect t M μ ν := by
  rw [gaussianMeasureDefect_eq_normSq ht]
  exact integral_nonneg fun z => Complex.normSq_nonneg _

end SphericalRiesz
