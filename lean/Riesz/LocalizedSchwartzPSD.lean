import Riesz.SchwartzMeasurePSD

/-!
Actual chart-cutoff localization.  The positive weighted pushforward measures
are constructed from a measurable chart and a nonnegative integrable cutoff.
The theorem refers to the original weighted double integrals, not a supplied
positive-definiteness witness.  Haar averaging and the sharp minorant remain
separate proof obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped SchwartzMap RealInnerProductSpace FourierTransform ComplexConjugate
namespace SphericalRiesz

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

def weightedChartMeasure (μ : Measure S) (χ : S → ℝ) (u : S → E) : Measure E :=
  (μ.withDensity (fun x => ENNReal.ofReal (χ x))).map u

theorem weightedChartMeasure_finite (μ : Measure S) (χ : S → ℝ) (u : S → E)
    (hχ : Integrable χ μ) (hχnonneg : ∀ x, 0 ≤ χ x) :
    IsFiniteMeasure (weightedChartMeasure μ χ u) := by
  have hfin : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (χ x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hχ (Filter.Eventually.of_forall hχnonneg)]
    exact ENNReal.ofReal_ne_top
  letI := hfin
  unfold weightedChartMeasure
  infer_instance

theorem weightedChartMeasure_integral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure S) (χ : S → ℝ) (u : S → E)
    (hχmeas : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hu : Measurable u)
    (g : E → F) (hg : StronglyMeasurable g) :
    (∫ y, g y ∂weightedChartMeasure μ χ u) = ∫ x, χ x • g (u x) ∂μ := by
  rw [weightedChartMeasure, integral_map hu.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hχmeas.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hχnonneg _)]

theorem weightedChartMeasure_charFun (μ : Measure S) (χ : S → ℝ) (u : S → E)
    (hχmeas : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hu : Measurable u) (z : E) :
    charFun (weightedChartMeasure μ χ u) z =
      ∫ x, (χ x : ℂ)*Complex.exp (⟪u x, z⟫ * Complex.I) ∂μ := by
  rw [charFun_apply, weightedChartMeasure_integral μ χ u hχmeas hχnonneg hu
    _ (by fun_prop)]
  simp only [Complex.real_smul, smul_eq_mul]

def localizedSchwartzPair (f : 𝓢(E, ℂ)) (a : ℝ) (χ : S → ℝ) (u : S → E)
    (μ ν : Measure S) : ℝ :=
  ∫ x, ∫ y, χ x*χ y*(f (a • (u x-u y))).re ∂ν ∂μ

theorem localizedSchwartzPair_eq_measurePair (f : 𝓢(E, ℂ)) (a : ℝ)
    (χ : S → ℝ) (u : S → E) (μ ν : Measure S)
    (hχmeas : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hu : Measurable u)
    (hχμ : Integrable χ μ) (hχν : Integrable χ ν) :
    localizedSchwartzPair f a χ u μ ν =
      schwartzMeasurePair f a (weightedChartMeasure μ χ u) (weightedChartMeasure ν χ u) := by
  letI := weightedChartMeasure_finite μ χ u hχμ hχnonneg
  letI := weightedChartMeasure_finite ν χ u hχν hχnonneg
  rw [schwartzMeasurePair_iterated,
    weightedChartMeasure_integral μ χ u hχmeas hχnonneg hu _
      ((show StronglyMeasurable (fun p : E × E => (f (a • (p.1-p.2))).re) from
        (by fun_prop)).integral_prod_right')]
  have hinner (x : E) :
      (∫ y, (f (a • (x-y))).re ∂weightedChartMeasure ν χ u) =
      ∫ y, χ y*(f (a • (x-u y))).re ∂ν := by
    have h := weightedChartMeasure_integral ν χ u hχmeas hχnonneg hu
      (fun y => (f (a • (x-y))).re) (by fun_prop)
    simpa only [smul_eq_mul] using h
  simp_rw [hinner, smul_eq_mul, ← integral_const_mul]
  unfold localizedSchwartzPair
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  ring

def localizedSchwartzDefect (f : 𝓢(E, ℂ)) (a M : ℝ) (χ : S → ℝ) (u : S → E)
    (μ ν : Measure S) : ℝ :=
  localizedSchwartzPair f a χ u μ μ - 2*M*localizedSchwartzPair f a χ u μ ν +
    M^2*localizedSchwartzPair f a χ u ν ν

theorem localizedSchwartzDefect_eq_measureDefect (f : 𝓢(E, ℂ)) (a M : ℝ)
    (χ : S → ℝ) (u : S → E) (μ ν : Measure S)
    (hχmeas : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hu : Measurable u)
    (hχμ : Integrable χ μ) (hχν : Integrable χ ν) :
    localizedSchwartzDefect f a M χ u μ ν =
      schwartzMeasureDefect f a M (weightedChartMeasure μ χ u) (weightedChartMeasure ν χ u) := by
  unfold localizedSchwartzDefect schwartzMeasureDefect
  rw [localizedSchwartzPair_eq_measurePair f a χ u μ μ hχmeas hχnonneg hu hχμ hχμ,
    localizedSchwartzPair_eq_measurePair f a χ u μ ν hχmeas hχnonneg hu hχμ hχν,
    localizedSchwartzPair_eq_measurePair f a χ u ν ν hχmeas hχnonneg hu hχν hχν]

theorem localizedSchwartzDefect_eq_normSq (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a M : ℝ) (χ : S → ℝ) (u : S → E) (μ ν : Measure S)
    (hχmeas : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hu : Measurable u)
    (hχμ : Integrable χ μ) (hχν : Integrable χ ν) :
    localizedSchwartzDefect f a M χ u μ ν = ∫ z, Complex.normSq
      ((∫ x, (χ x : ℂ)*Complex.exp (⟪u x, (2*Real.pi*a) • z⟫ * Complex.I) ∂μ) -
        (M : ℂ)*(∫ x, (χ x : ℂ)*Complex.exp (⟪u x, (2*Real.pi*a) • z⟫ * Complex.I) ∂ν))
      ∂schwartzSpectralMeasure f := by
  letI := weightedChartMeasure_finite μ χ u hχμ hχnonneg
  letI := weightedChartMeasure_finite ν χ u hχν hχnonneg
  rw [localizedSchwartzDefect_eq_measureDefect f a M χ u μ ν hχmeas hχnonneg hu hχμ hχν,
    schwartzMeasureDefect_eq_normSq f hFnonneg hFreal]
  simp_rw [weightedChartMeasure_charFun μ χ u hχmeas hχnonneg hu,
    weightedChartMeasure_charFun ν χ u hχmeas hχnonneg hu]

theorem localizedSchwartzDefect_nonneg (f : 𝓢(E, ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a M : ℝ) (χ : S → ℝ) (u : S → E) (μ ν : Measure S)
    (hχmeas : Measurable χ) (hχnonneg : ∀ x, 0 ≤ χ x) (hu : Measurable u)
    (hχμ : Integrable χ μ) (hχν : Integrable χ ν) :
    0 ≤ localizedSchwartzDefect f a M χ u μ ν := by
  rw [localizedSchwartzDefect_eq_normSq f hFnonneg hFreal a M χ u μ ν
    hχmeas hχnonneg hu hχμ hχν]
  exact integral_nonneg fun z => Complex.normSq_nonneg _

end SphericalRiesz
