import E8Leech.SchwartzValueDecay
import E8Leech.SpectralSlackGap
import E8Leech.EvenFourierReality
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The actual Schwartz Fourier transform supplies the stationary LP witness

The spectral density is the real part of the actual Fourier transform of the
Schwartz function. When that transform is real valued, Mathlib inversion proves
the spectral representation. Decay and integrability are derived, not postulated.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical SchwartzMap FourierTransform RealInnerProductSpace

theorem integrable_fourier_schwartzMap_re {d : ℕ} (f : 𝓢(Ambient d, ℂ)) :
    Integrable (fun ξ => (𝓕 f ξ).re) volume :=
  (𝓕 f).integrable.re

theorem fourier_schwartzMap_real_density_eq {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) :
    (fun ξ => ((𝓕 f ξ).re : ℂ)) = ((𝓕 f : 𝓢(Ambient d, ℂ)) : Ambient d → ℂ) := by
  funext ξ
  apply Complex.ext
  · simp
  · simpa using (him ξ).symm

theorem inverseSpectralKernel_fourier_schwartzMap_re {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) (x : Ambient d) :
    inverseSpectralKernel volume (fun ξ => (𝓕 f ξ).re) x = f x := by
  rw [inverseSpectralKernel_eq_fourierInv, fourier_schwartzMap_real_density_eq f him,
    ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]

theorem realSpectralKernel_fourier_schwartzMap_re {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) :
    realSpectralKernel volume (fun ξ => (𝓕 f ξ).re) = fun x => (f x).re := by
  funext x
  exact congrArg Complex.re (inverseSpectralKernel_fourier_schwartzMap_re f him x)

theorem fourier_schwartzMap_zero_re {d : ℕ} (f : 𝓢(Ambient d, ℂ)) :
    (𝓕 f (0 : Ambient d)).re = ∫ x, (f x).re := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul]
  exact (integral_re f.integrable).symm

theorem stationary_schwartzMap_offDiagonal_lower
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re) :
    ρ.toReal ^ 2 * (𝓕 f (0 : Ambient d)).re - (f 0).re * ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0 else (f (x - y)).re) c
        (unitWindow d) univ ∂μ := by
  have hk := realSpectralKernel_fourier_schwartzMap_re f him
  have hd : HasRapidDecay (realSpectralKernel volume (fun ξ => (𝓕 f ξ).re)) := by
    rw [hk]
    exact hasRapidDecay_schwartzMap_re f
  have hp := stationary_spectral_offDiagonal_anchor_lower_of_rapidDecay hs μ hμ ρ hρ hρtop
    henergy volume (fun ξ => (𝓕 f ξ).re) (integrable_fourier_schwartzMap_re f) hnonneg hd
  simpa only [hk, ← fourier_schwartzMap_zero_re f] using hp

theorem stationarySlackGapInput_of_schwartzMap_minorant
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (Λ : Set (Ambient d)) (hbase : latticeRieszEnergy Λ s ≠ ∞)
    (f : 𝓢(Ambient d, ℂ)) (him : ∀ ξ, (𝓕 f ξ).im = 0)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (hminor : ∀ x y, x ≠ y →
      rieszPotential s x y + ENNReal.ofReal (-(f (x - y)).re) =
        V x y + ENNReal.ofReal (f (x - y)).re)
    (hcalib : (latticeRieszEnergy Λ s).toReal = (𝓕 f (0 : Ambient d)).re - (f 0).re) :
    StationarySlackGapInput Λ s V := by
  have hk := realSpectralKernel_fourier_schwartzMap_re f him
  have hd : HasRapidDecay (realSpectralKernel volume (fun ξ => (𝓕 f ξ).re)) := by
    rw [hk]
    exact hasRapidDecay_schwartzMap_re f
  apply stationarySlackGapInput_of_spectral_minorant hs Λ hbase volume
    (fun ξ => (𝓕 f ξ).re) (integrable_fourier_schwartzMap_re f) hnonneg hd V hV
  · simpa only [hk] using hminor
  · simpa only [hk, ← fourier_schwartzMap_zero_re f] using hcalib

theorem fourier_complexSchwartzMap_im_zero_of_even {d : ℕ} (f : 𝓢(Ambient d, ℝ))
    (heven : ∀ x, f (-x) = f x) (ξ : Ambient d) :
    (𝓕 (complexSchwartzMap f) ξ).im = 0 := by
  rw [SchwartzMap.fourier_coe]
  apply fourier_im_zero_of_real_even
  · intro x
    simp
  · intro x
    simp only [complexSchwartzMap_apply, heven]

@[simp] theorem fourier_complexSchwartzMap_apply {d : ℕ} (f : 𝓢(Ambient d, ℝ))
    (ξ : Ambient d) :
    (𝓕 (complexSchwartzMap f) ξ) = 𝓕 (fun x => (f x : ℂ)) ξ := by
  rw [SchwartzMap.fourier_coe]
  rfl

theorem stationary_real_schwartzMap_even_offDiagonal_lower
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (f : 𝓢(Ambient d, ℝ))
    (heven : ∀ x, f (-x) = f x)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re) :
    ρ.toReal ^ 2 * (𝓕 (fun x => (f x : ℂ)) (0 : Ambient d)).re - f 0 * ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0 else f (x - y)) c
        (unitWindow d) univ ∂μ := by
  have hn : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (complexSchwartzMap f) ξ).re := hnonneg
  have hp := stationary_schwartzMap_offDiagonal_lower hs μ hμ ρ hρ hρtop henergy
    (complexSchwartzMap f) (fourier_complexSchwartzMap_im_zero_of_even f heven) hn
  simpa only [fourier_complexSchwartzMap_apply, complexSchwartzMap_apply,
    Complex.ofReal_re] using hp

theorem stationarySlackGapInput_of_real_even_schwartzMap_minorant
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (Λ : Set (Ambient d)) (hbase : latticeRieszEnergy Λ s ≠ ∞)
    (f : 𝓢(Ambient d, ℝ)) (heven : ∀ x, f (-x) = f x)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (fun x => (f x : ℂ)) ξ).re)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (hminor : ∀ x y, x ≠ y → rieszPotential s x y + ENNReal.ofReal (-f (x - y)) =
      V x y + ENNReal.ofReal (f (x - y)))
    (hcalib : (latticeRieszEnergy Λ s).toReal =
      (𝓕 (fun x => (f x : ℂ)) (0 : Ambient d)).re - f 0) :
    StationarySlackGapInput Λ s V := by
  apply stationarySlackGapInput_of_schwartzMap_minorant hs Λ hbase (complexSchwartzMap f)
    (fourier_complexSchwartzMap_im_zero_of_even f heven) hnonneg V hV
  · simpa only [complexSchwartzMap_apply, Complex.ofReal_re] using hminor
  · simpa only [fourier_complexSchwartzMap_apply, complexSchwartzMap_apply,
      Complex.ofReal_re] using hcalib

end E8Leech
