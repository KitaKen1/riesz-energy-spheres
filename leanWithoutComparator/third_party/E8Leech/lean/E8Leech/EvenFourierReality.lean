import E8Leech.SpectralFiniteForms

/-!
# Real even functions have real Fourier transforms in the actual convention

Conjugate the Bochner integral and use the volume-preserving negation isometry.
No new Fourier-reality premise is needed for a real radial auxiliary function.
-/

noncomputable section

namespace E8Leech

open MeasureTheory ComplexConjugate
open scoped FourierTransform RealInnerProductSpace

theorem fourier_conj_of_real_values {d : ℕ} (f : Ambient d → ℂ)
    (hreal : ∀ x, (f x).im = 0) (ξ : Ambient d) :
    conj (𝓕 f ξ) = 𝓕 f (-ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  congr 1
  funext x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, inner_neg_right,
    Complex.conj_eq_iff_im.mpr (hreal x)]
  congr 2
  push_cast
  ring

theorem fourier_neg_of_even {d : ℕ} (f : Ambient d → ℂ)
    (heven : ∀ x, f (-x) = f x) (ξ : Ambient d) :
    𝓕 f ξ = 𝓕 f (-ξ) := by
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f ξ
  simpa only [Function.comp_def, LinearIsometryEquiv.coe_neg, heven] using h

theorem fourier_im_zero_of_real_even {d : ℕ} (f : Ambient d → ℂ)
    (hreal : ∀ x, (f x).im = 0) (heven : ∀ x, f (-x) = f x) (ξ : Ambient d) :
    (𝓕 f ξ).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [fourier_conj_of_real_values f hreal ξ, ← fourier_neg_of_even f heven ξ]

end E8Leech
