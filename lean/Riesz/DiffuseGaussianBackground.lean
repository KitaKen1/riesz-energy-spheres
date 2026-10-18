import Riesz.GaussianMeasurePSD

/-! A finite foreground and an actual finite diffuse background measure. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
variable {ι : Type*} [Fintype ι]

def finitePointMeasure (x : ι → E) : Measure E := ∑ i, Measure.dirac (x i)

instance finitePointMeasure_finite (x : ι → E) : IsFiniteMeasure (finitePointMeasure x) := by
  unfold finitePointMeasure
  infer_instance

theorem finitePointMeasure_integral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (x : ι → E) (f : E → F) :
    (∫ y, f y ∂finitePointMeasure x) = ∑ i, f (x i) := by
  unfold finitePointMeasure
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem finitePointMeasure_charFun (x : ι → E) (z : E) :
    charFun (finitePointMeasure x) z = ∑ i, Complex.exp (⟪x i, z⟫ * Complex.I) := by
  exact finitePointMeasure_integral x _

theorem gaussianMeasurePair_finite_left {t : ℝ} (ht : 0 ≤ t)
    (x : ι → E) (ν : Measure E) [IsFiniteMeasure ν] :
    gaussianMeasurePair t (finitePointMeasure x) ν =
      ∑ i, ∫ y, gaussianKernel t (x i) y ∂ν := by
  rw [gaussianMeasurePair_iterated ht, finitePointMeasure_integral]

theorem gaussianMeasurePair_finite_both {t : ℝ} (ht : 0 ≤ t) (x : ι → E) :
    gaussianMeasurePair t (finitePointMeasure x) (finitePointMeasure x) =
      ∑ i, ∑ j, gaussianKernel t (x i) (x j) := by
  rw [gaussianMeasurePair_finite_left ht]
  simp_rw [finitePointMeasure_integral]

def diffuseGaussianDefect (t M : ℝ) (x : ι → E) (ν : Measure E) : ℝ :=
  (∑ i, ∑ j, gaussianKernel t (x i) (x j)) -
    2*M*(∑ i, ∫ y, gaussianKernel t (x i) y ∂ν) +
    M^2*gaussianMeasurePair t ν ν

theorem diffuseGaussianDefect_eq_measureDefect {t : ℝ} (ht : 0 ≤ t) (M : ℝ)
    (x : ι → E) (ν : Measure E) [IsFiniteMeasure ν] :
    diffuseGaussianDefect t M x ν = gaussianMeasureDefect t M (finitePointMeasure x) ν := by
  unfold diffuseGaussianDefect gaussianMeasureDefect
  rw [gaussianMeasurePair_finite_both ht, gaussianMeasurePair_finite_left ht]

theorem diffuseGaussianDefect_eq_normSq {t : ℝ} (ht : 0 ≤ t) (M : ℝ)
    (x : ι → E) (ν : Measure E) [IsFiniteMeasure ν] :
    diffuseGaussianDefect t M x ν =
      ∫ z, Complex.normSq ((∑ i, Complex.exp (⟪x i, Real.sqrt (2*t) • z⟫ * Complex.I)) -
        (M : ℂ)*charFun ν (Real.sqrt (2*t) • z)) ∂stdGaussian E := by
  rw [diffuseGaussianDefect_eq_measureDefect ht, gaussianMeasureDefect_eq_normSq ht]
  simp only [finitePointMeasure_charFun]

theorem diffuseGaussianDefect_nonneg {t : ℝ} (ht : 0 ≤ t) (M : ℝ)
    (x : ι → E) (ν : Measure E) [IsFiniteMeasure ν] :
    0 ≤ diffuseGaussianDefect t M x ν := by
  rw [diffuseGaussianDefect_eq_measureDefect ht]
  exact gaussianMeasureDefect_nonneg ht M _ ν

end SphericalRiesz
