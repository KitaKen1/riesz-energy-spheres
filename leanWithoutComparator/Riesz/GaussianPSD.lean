/-
The Gaussian characteristic-function rescaling proof is adapted from TauCeti,
Copyright (c) 2026 The Tau Ceti contributors, Apache License 2.0.
Source: TauCeti/Analysis/Bochner/Gaussian/Basic.lean,
commit 98962476aaba1de05b4a883df5af0562247cb501.
See third_party/TauCeti/LICENSE and NOTICE.txt.
-/
import Riesz.CharFun
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Gaussian nonnegativity with arbitrary real signed weights. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexOrder

namespace SphericalRiesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_charFun_rescale {t : ℝ} (ht : 0 ≤ t) (x : E) :
    charFun (stdGaussian E) (Real.sqrt (2*t) • x) =
      Complex.exp (-(t * ‖x‖^2 : ℝ)) := by
  have hs : Real.sqrt (2*t)^2 = 2*t := Real.sq_sqrt (by positivity)
  have hn : ‖Real.sqrt (2*t) • x‖^2 = 2*t*‖x‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
  rw [charFun_stdGaussian, ← Complex.ofReal_pow, hn]
  congr 1
  push_cast
  ring

/-- Real coefficients can have either sign. No separation or zero-mass hypothesis is needed. -/
theorem gaussian_weighted_sum_nonneg {ι : Type*} [Fintype ι]
    {t : ℝ} (ht : 0 ≤ t) (c : ι → ℝ) (x : ι → E) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.exp (-(t * ‖x i-x j‖^2)) := by
  have h := Fourier.charFun_fintype_sum_mul_conj_nonneg
    (μ := stdGaussian E) (fun i => (c i : ℂ)) (fun i => Real.sqrt (2*t) • x i)
  simp only [← smul_sub, gaussian_charFun_rescale ht, Complex.conj_ofReal,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_sum] at h
  exact Complex.zero_le_real.mp h

def gaussianKernel (t : ℝ) (x y : E) : ℝ := Real.exp (-(t * ‖x-y‖^2))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianKernel_symm (t : ℝ) (x y : E) : gaussianKernel t x y = gaussianKernel t y x := by
  simp only [gaussianKernel, norm_sub_rev]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem gaussianKernel_self (t : ℝ) (x : E) : gaussianKernel t x x = 1 := by
  simp [gaussianKernel]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussianKernel_nonneg (t : ℝ) (x y : E) : 0 ≤ gaussianKernel t x y :=
  (Real.exp_pos _).le

#print axioms gaussian_weighted_sum_nonneg

end SphericalRiesz
