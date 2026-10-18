import E8Leech.GaussianPairIntegrals
import E8Leech.StationaryOffDiagonalLP
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

/-!
# Actual Gaussian Fourier density in the project's Euclidean convention

The known Gaussian integral supplies the precise dimension and pi factors.
Fourier inversion identifies the actual inverse spectral kernel, without a
postulated spectral witness or a new Schwartz proof. This alone is not the
sharp lattice Gaussian certificate required by universal optimality.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical FourierTransform

theorem integrable_gaussianKernel {d : ℕ} {α : ℝ} (hα : 0 < α) :
    Integrable (@gaussianKernel d α) volume :=
  integrable_of_hasRapidDecay _ (continuous_gaussianKernel α).measurable
    (hasRapidDecay_gaussianKernel hα)

theorem integral_gaussianKernel {d : ℕ} {α : ℝ} (hα : 0 < α) :
    (∫ x : Ambient d, gaussianKernel α x) = (Real.pi / α) ^ ((d : ℝ) / 2) := by
  simpa only [gaussianKernel, Ambient, finrank_euclideanSpace, Fintype.card_fin] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Ambient d) hα

def gaussianSpectralDensity {d : ℕ} (α : ℝ) (ξ : Ambient d) : ℝ :=
  (Real.pi / α) ^ ((d : ℝ) / 2) * gaussianKernel (Real.pi ^ 2 / α) ξ

theorem gaussianSpectralDensity_pos {d : ℕ} {α : ℝ} (hα : 0 < α) (ξ : Ambient d) :
    0 < gaussianSpectralDensity α ξ :=
  mul_pos (Real.rpow_pos_of_pos (div_pos Real.pi_pos hα) _) (gaussianKernel_pos _ _)

theorem continuous_gaussianSpectralDensity {d : ℕ} (α : ℝ) :
    Continuous (@gaussianSpectralDensity d α) :=
  continuous_const.mul (continuous_gaussianKernel _)

theorem integrable_gaussianSpectralDensity {d : ℕ} {α : ℝ} (hα : 0 < α) :
    Integrable (@gaussianSpectralDensity d α) volume :=
  (integrable_gaussianKernel (div_pos (pow_pos Real.pi_pos 2) hα)).const_mul _

theorem fourier_gaussianKernel {d : ℕ} {α : ℝ} (hα : 0 < α) (ξ : Ambient d) :
    𝓕 (fun x : Ambient d => (gaussianKernel α x : ℂ)) ξ =
      (gaussianSpectralDensity α ξ : ℂ) := by
  have hfun : (fun x : Ambient d => (gaussianKernel α x : ℂ)) =
      (fun x : Ambient d => Complex.exp (-(α : ℂ) * (‖x‖ : ℂ) ^ 2)) := by
    funext x
    simp only [gaussianKernel, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_pow]
  rw [hfun, fourier_gaussian_innerProductSpace (show 0 < (α : ℂ).re from hα)]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin]
  have hp : (Real.pi / α : ℂ) ^ ((d : ℂ) / 2) =
      ((Real.pi / α) ^ ((d : ℝ) / 2) : ℝ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (div_pos Real.pi_pos hα).le ((d : ℝ) / 2)).symm
  rw [hp]
  unfold gaussianSpectralDensity gaussianKernel
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem fourier_gaussianKernel_eq_density {d : ℕ} {α : ℝ} (hα : 0 < α) :
    𝓕 (fun x : Ambient d => (gaussianKernel α x : ℂ)) =
      fun ξ => (gaussianSpectralDensity α ξ : ℂ) :=
  funext (fourier_gaussianKernel hα)

theorem inverseSpectralKernel_gaussianDensity {d : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Ambient d) :
    inverseSpectralKernel volume (gaussianSpectralDensity α) x =
      (gaussianKernel α x : ℂ) := by
  rw [inverseSpectralKernel_eq_fourierInv, ← fourier_gaussianKernel_eq_density hα]
  apply (integrable_gaussianKernel hα).ofReal.fourierInv_fourier_eq
  · rw [fourier_gaussianKernel_eq_density hα]
    exact (integrable_gaussianSpectralDensity hα).ofReal
  · exact (Complex.continuous_ofReal.comp (continuous_gaussianKernel α)).continuousAt

theorem realSpectralKernel_gaussianDensity {d : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Ambient d) :
    realSpectralKernel volume (gaussianSpectralDensity α) x = gaussianKernel α x := by
  unfold realSpectralKernel
  rw [inverseSpectralKernel_gaussianDensity hα, Complex.ofReal_re]

theorem integral_gaussianSpectralDensity {d : ℕ} {α : ℝ} (hα : 0 < α) :
    (∫ ξ : Ambient d, gaussianSpectralDensity α ξ) = 1 := by
  have h := inverseSpectralKernel_gaussianDensity (d := d) hα 0
  rw [inverseSpectralKernel_zero] at h
  exact Complex.ofReal_injective (by simpa [gaussianKernel] using h)

theorem fourier_gaussianKernel_zero {d : ℕ} {α : ℝ} (hα : 0 < α) :
    (𝓕 (fun x : Ambient d => (gaussianKernel α x : ℂ)) 0).re =
      (Real.pi / α) ^ ((d : ℝ) / 2) := by
  rw [fourier_gaussianKernel hα]
  simp [gaussianSpectralDensity, gaussianKernel]

theorem stationary_gaussian_offDiagonal_lower {d : ℕ} {s α : ℝ}
    (hs : 0 ≤ s) (hα : 0 < α) (μ : Measure (Configuration (Ambient d)))
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (henergy : rieszEnergy s μ ≠ ∞) :
    ρ.toReal ^ 2 * (Real.pi / α) ^ ((d : ℝ) / 2) - ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else gaussianKernel α (x - y)) c (unitWindow d) univ ∂μ := by
  have heq : realSpectralKernel volume (gaussianSpectralDensity (d := d) α) =
      gaussianKernel α := funext (realSpectralKernel_gaussianDensity hα)
  have hp := stationary_spectral_offDiagonal_anchor_lower_of_rapidDecay hs μ hμ ρ hρ
    hρtop henergy volume (gaussianSpectralDensity α) (integrable_gaussianSpectralDensity hα)
    (Filter.Eventually.of_forall fun ξ => (gaussianSpectralDensity_pos hα ξ).le)
    (heq.symm ▸ hasRapidDecay_gaussianKernel hα)
  rw [heq, integral_gaussianKernel hα] at hp
  simpa only [gaussianKernel, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Real.exp_zero, one_mul] using hp

end E8Leech
