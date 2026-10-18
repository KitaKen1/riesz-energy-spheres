import Riesz.SpectralMeasurePSD
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Fourier-nonnegative Schwartz kernels on actual finite positive measures.
The nonnegative Fourier density defines the spectral measure explicitly.
Fourier inversion identifies its characteristic function with the original
kernel, with the checked 2*pi convention.  This is a positivity foundation;
it does not construct an E8/Leech sharp Gaussian minorant.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped SchwartzMap RealInnerProductSpace FourierTransform ComplexConjugate
namespace SphericalRiesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

def schwartzSpectralMeasure (f : 𝓢(E, ℂ)) : Measure E :=
  volume.withDensity (fun z => ENNReal.ofReal ((𝓕 f) z).re)

theorem schwartzSpectralMeasure_finite (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) : IsFiniteMeasure (schwartzSpectralMeasure f) := by
  have hFi := ((𝓕 f : 𝓢(E, ℂ)).integrable (μ := (volume : Measure E))).re
  change Integrable (fun z => ((𝓕 f) z).re) (volume : Measure E) at hFi
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hFi
    (Filter.Eventually.of_forall hFnonneg)]
  exact ENNReal.ofReal_ne_top

theorem schwartzSpectralMeasure_charFun (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re)
    (hFreal : ∀ z, ((𝓕 f) z).im = 0) (x : E) :
    charFun (schwartzSpectralMeasure f) ((2*Real.pi) • x) = f x := by
  rw [charFun_apply, schwartzSpectralMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hFnonneg _), inner_smul_right]
  have hreal (z : E) : (((𝓕 f) z).re : ℂ) = (𝓕 f) z := by
    apply Complex.ext
    · rfl
    · simpa using (hFreal z).symm
  calc
    _ = 𝓕⁻ (fun z => (𝓕 f : 𝓢(E, ℂ)) z) x := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with z
      rw [Complex.real_smul, smul_eq_mul, hreal]
      ring
    _ = f x := by
      have h := congrArg (fun g : 𝓢(E, ℂ) => g x) (FourierTransform.fourierInv_fourier_eq (F := 𝓢(E, ℂ)) f)
      simpa only [SchwartzMap.fourierInv_coe] using h

def schwartzMeasurePair (f : 𝓢(E, ℂ)) (a : ℝ) (μ ν : Measure E) : ℝ :=
  ∫ p : E × E, (f (a • (p.1-p.2))).re ∂μ.prod ν

theorem schwartzKernel_product_integrable (f : 𝓢(E, ℂ)) (a : ℝ)
    (τ : Measure (E × E)) [IsFiniteMeasure τ] :
    Integrable (fun p : E × E => f (a • (p.1-p.2))) τ := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    ((f.continuous.comp (by fun_prop)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun p => SchwartzMap.norm_le_seminorm ℝ f _

theorem spectralMeasurePair_eq_schwartz (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re)
    (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    spectralMeasurePair (2*Real.pi*a) (schwartzSpectralMeasure f) μ ν =
      schwartzMeasurePair f a μ ν := by
  unfold spectralMeasurePair schwartzMeasurePair
  have hs (p : E × E) : (2*Real.pi*a) • (p.1-p.2) =
      (2*Real.pi) • (a • (p.1-p.2)) := mul_smul _ _ _
  simp_rw [hs, schwartzSpectralMeasure_charFun f hFnonneg hFreal]
  have h := integral_re (schwartzKernel_product_integrable f a (μ.prod ν))
  change (∫ p : E × E, (f (a • (p.1-p.2))).re ∂μ.prod ν) =
    (∫ p : E × E, f (a • (p.1-p.2)) ∂μ.prod ν).re at h
  exact h.symm

theorem schwartzMeasurePair_iterated (f : 𝓢(E, ℂ)) (a : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    schwartzMeasurePair f a μ ν = ∫ x, ∫ y, (f (a • (x-y))).re ∂ν ∂μ := by
  exact integral_prod _ (schwartzKernel_product_integrable f a (μ.prod ν)).re

theorem schwartzMeasurePair_symm (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re)
    (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    schwartzMeasurePair f a μ ν = schwartzMeasurePair f a ν μ := by
  letI := schwartzSpectralMeasure_finite f hFnonneg
  rw [← spectralMeasurePair_eq_schwartz f hFnonneg hFreal,
    ← spectralMeasurePair_eq_schwartz f hFnonneg hFreal]
  exact spectralMeasurePair_symm _ _ _ _

def schwartzMeasureDefect (f : 𝓢(E, ℂ)) (a M : ℝ) (μ ν : Measure E) : ℝ :=
  schwartzMeasurePair f a μ μ - 2*M*schwartzMeasurePair f a μ ν +
    M^2*schwartzMeasurePair f a ν ν

theorem schwartzMeasureDefect_eq_normSq (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re)
    (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a M : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    schwartzMeasureDefect f a M μ ν = ∫ z, Complex.normSq
      (charFun μ ((2*Real.pi*a) • z) - (M : ℂ)*charFun ν ((2*Real.pi*a) • z))
      ∂schwartzSpectralMeasure f := by
  letI := schwartzSpectralMeasure_finite f hFnonneg
  unfold schwartzMeasureDefect
  simp_rw [← spectralMeasurePair_eq_schwartz f hFnonneg hFreal]
  exact spectralMeasureDefect_eq_normSq _ _ _ _ _

theorem schwartzMeasureDefect_nonneg (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re)
    (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a M : ℝ)
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ schwartzMeasureDefect f a M μ ν := by
  rw [schwartzMeasureDefect_eq_normSq f hFnonneg hFreal]
  exact integral_nonneg fun z => Complex.normSq_nonneg _

end SphericalRiesz
