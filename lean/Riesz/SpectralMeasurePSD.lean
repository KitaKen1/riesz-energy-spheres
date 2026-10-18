import Riesz.GaussianMeasurePSD

/-!
The finite-measure Fourier positivity step, independent of the Gaussian.
A positive finite spectral measure gives a real symmetric kernel.  Its
foreground-minus-background defect is an actual integral of a squared modulus.
No signed-measure representation or sharp Gaussian certificate is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

def spectralMeasurePair (r : ℝ) (ρ μ ν : Measure E) : ℝ :=
  (∫ p : E × E, charFun ρ (r • (p.1-p.2)) ∂μ.prod ν).re

theorem spectralMeasurePair_eq_hermitian (r : ℝ)
    (ρ μ ν : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    spectralMeasurePair r ρ μ ν =
      (∫ z, charFun μ (r • z) * conj (charFun ν (r • z)) ∂ρ).re := by
  rw [charFun_hermitian_product_integral]
  rfl

theorem charFun_hermitian_real_integral (r : ℝ)
    (ρ μ ν : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ z, (charFun μ (r • z) * conj (charFun ν (r • z))).re ∂ρ) =
      (∫ z, charFun μ (r • z) * conj (charFun ν (r • z)) ∂ρ).re := by
  have h := integral_re (charFun_hermitian_product_integrable r μ ν ρ)
  change (∫ z, (charFun μ (r • z) * conj (charFun ν (r • z))).re ∂ρ) =
    (∫ z, charFun μ (r • z) * conj (charFun ν (r • z)) ∂ρ).re at h
  exact h

theorem spectralMeasurePair_symm (r : ℝ)
    (ρ μ ν : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    spectralMeasurePair r ρ μ ν = spectralMeasurePair r ρ ν μ := by
  rw [spectralMeasurePair_eq_hermitian, spectralMeasurePair_eq_hermitian,
    ← charFun_hermitian_real_integral r ρ μ ν,
    ← charFun_hermitian_real_integral r ρ ν μ]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

def spectralMeasureDefect (r M : ℝ) (ρ μ ν : Measure E) : ℝ :=
  spectralMeasurePair r ρ μ μ - 2*M*spectralMeasurePair r ρ μ ν +
    M^2*spectralMeasurePair r ρ ν ν

theorem spectralMeasureDefect_normSq_integrable (r M : ℝ)
    (ρ μ ν : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun z => Complex.normSq
      (charFun μ (r • z) - (M : ℂ)*charFun ν (r • z))) ρ := by
  have haa := (charFun_hermitian_product_integrable r μ μ ρ).re
  have hab := (charFun_hermitian_product_integrable r μ ν ρ).re
  have hba := (charFun_hermitian_product_integrable r ν μ ρ).re
  have hbb := (charFun_hermitian_product_integrable r ν ν ρ).re
  change Integrable (fun z => (charFun μ (r • z) * conj (charFun μ (r • z))).re) ρ at haa
  change Integrable (fun z => (charFun μ (r • z) * conj (charFun ν (r • z))).re) ρ at hab
  change Integrable (fun z => (charFun ν (r • z) * conj (charFun μ (r • z))).re) ρ at hba
  change Integrable (fun z => (charFun ν (r • z) * conj (charFun ν (r • z))).re) ρ at hbb
  apply ((haa.sub (hab.const_mul M)).sub (hba.const_mul M)).add
    (hbb.const_mul (M^2)) |>.congr
  filter_upwards [] with z
  dsimp only [Pi.add_apply, Pi.sub_apply]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem spectralMeasureDefect_eq_normSq (r M : ℝ)
    (ρ μ ν : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    spectralMeasureDefect r M ρ μ ν = ∫ z, Complex.normSq
      (charFun μ (r • z) - (M : ℂ)*charFun ν (r • z)) ∂ρ := by
  have haa := (charFun_hermitian_product_integrable r μ μ ρ).re
  have hab := (charFun_hermitian_product_integrable r μ ν ρ).re
  have hba := (charFun_hermitian_product_integrable r ν μ ρ).re
  have hbb := (charFun_hermitian_product_integrable r ν ν ρ).re
  change Integrable (fun z => (charFun μ (r • z) * conj (charFun μ (r • z))).re) ρ at haa
  change Integrable (fun z => (charFun μ (r • z) * conj (charFun ν (r • z))).re) ρ at hab
  change Integrable (fun z => (charFun ν (r • z) * conj (charFun μ (r • z))).re) ρ at hba
  change Integrable (fun z => (charFun ν (r • z) * conj (charFun ν (r • z))).re) ρ at hbb
  have heq (z : E) : Complex.normSq
      (charFun μ (r • z) - (M : ℂ)*charFun ν (r • z)) =
      (charFun μ (r • z) * conj (charFun μ (r • z))).re -
      M*(charFun μ (r • z) * conj (charFun ν (r • z))).re -
      M*(charFun ν (r • z) * conj (charFun μ (r • z))).re +
      M^2*(charFun ν (r • z) * conj (charFun ν (r • z))).re := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [heq]
  have hsub : Integrable (fun z =>
      (charFun μ (r • z) * conj (charFun μ (r • z))).re -
      M*(charFun μ (r • z) * conj (charFun ν (r • z))).re) ρ :=
    haa.sub (hab.const_mul M)
  have hsub2 : Integrable (fun z =>
      (charFun μ (r • z) * conj (charFun μ (r • z))).re -
      M*(charFun μ (r • z) * conj (charFun ν (r • z))).re -
      M*(charFun ν (r • z) * conj (charFun μ (r • z))).re) ρ :=
    hsub.sub (hba.const_mul M)
  rw [integral_add hsub2 (hbb.const_mul (M^2)),
    integral_sub hsub (hba.const_mul M), integral_sub haa (hab.const_mul M)]
  simp only [integral_const_mul]
  rw [charFun_hermitian_real_integral r ρ μ μ,
    charFun_hermitian_real_integral r ρ μ ν,
    charFun_hermitian_real_integral r ρ ν μ,
    charFun_hermitian_real_integral r ρ ν ν]
  rw [← spectralMeasurePair_eq_hermitian, ← spectralMeasurePair_eq_hermitian,
    ← spectralMeasurePair_eq_hermitian, ← spectralMeasurePair_eq_hermitian,
    spectralMeasurePair_symm r ρ ν μ]
  unfold spectralMeasureDefect
  ring

theorem spectralMeasureDefect_nonneg (r M : ℝ)
    (ρ μ ν : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ spectralMeasureDefect r M ρ μ ν := by
  rw [spectralMeasureDefect_eq_normSq]
  exact integral_nonneg fun z => Complex.normSq_nonneg _

end SphericalRiesz
