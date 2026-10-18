import E8Leech.RamanujanIdentities
import E8Leech.CKMRVPoleLimits

/-!
# Actual j derivative and the published coefficient diagonal limits

The actual E4/E6 derivative identities discharge the previous bridge's two
premises. The published coefficient constants are now unconditional at points
with E4 and E6 nonzero. This does not identify the phi/psi analytic kernels,
classify modular orbits/elliptic poles, or construct the full CKMRV witnesses.
-/

noncomputable section
namespace E8Leech
open Filter
open scoped Topology Matrix

theorem hasDerivAt_modularDiscriminant_actual (z : UpperHalfPlane) :
    HasDerivAt (fun w : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex w))
      (2 * (Real.pi : ℂ) * Complex.I * EisensteinSeries.E2 z * ModularForm.discriminant z)
      (z : ℂ) :=
  hasDerivAt_modularDiscriminant_of_eisenstein_derivatives z (EisensteinSeries.E2 z)
    (hasDerivAt_eisensteinFour z) (hasDerivAt_eisensteinSix z)

theorem hasDerivAt_kleinModularJ_actual_formula (z : UpperHalfPlane) :
    HasDerivAt (fun w : ℂ => kleinModularJ (UpperHalfPlane.ofComplex w))
      (ckmrvKleinDerivativeCandidate z) (z : ℂ) :=
  hasDerivAt_kleinModularJ_of_eisenstein_derivatives z (EisensteinSeries.E2 z)
    (hasDerivAt_eisensteinFour z) (hasDerivAt_eisensteinSix z)

theorem kleinModularJDerivative_eq_candidate (z : UpperHalfPlane) :
    kleinModularJDerivative z = ckmrvKleinDerivativeCandidate z :=
  kleinModularJDerivative_eq_candidate_of_eisenstein_derivatives z (EisensteinSeries.E2 z)
    (hasDerivAt_eisensteinFour z) (hasDerivAt_eisensteinSix z)

theorem kleinModularJDerivative_eq_zero_iff (z : UpperHalfPlane) :
    kleinModularJDerivative z = 0 ↔ ModularForm.E₄ z = 0 ∨ ModularForm.E₆ z = 0 := by
  rw [kleinModularJDerivative_eq_candidate]
  simp [ckmrvKleinDerivativeCandidate, ModularForm.discriminant_ne_zero z,
    Real.pi_ne_zero, Complex.I_ne_zero]

theorem kleinModularJDerivative_ne_zero_iff (z : UpperHalfPlane) :
    kleinModularJDerivative z ≠ 0 ↔ ModularForm.E₄ z ≠ 0 ∧ ModularForm.E₆ z ≠ 0 := by
  rw [ne_eq, kleinModularJDerivative_eq_zero_iff, not_or]

theorem kleinModularJDerivative_imaginary_ne_zero {y : ℝ} (hy : 1 < y) :
    kleinModularJDerivative (UpperHalfPlane.ofComplex (Complex.I * y)) ≠ 0 := by
  rw [kleinModularJDerivative_eq_candidate]
  exact ckmrvKleinDerivativeCandidate_imaginary_ne_zero hy

theorem tendsto_ckmrvEightPlusCoefficientMatrix_published_residue
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 ((((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) i j)) :=
  tendsto_ckmrvEightPlusCoefficientMatrix_published_residue_of_derivative_identification
    z hA hB (kleinModularJDerivative_eq_candidate z) i j

theorem tendsto_ckmrvEightMinusCoefficientMatrix_published_residue
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 (((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) • ckmrvMinusResidueMatrix z) i j)) :=
  tendsto_ckmrvEightMinusCoefficientMatrix_published_residue_of_derivative_identification
    z hA hB (kleinModularJDerivative_eq_candidate z) i j

theorem tendsto_ckmrvLeechPlusCoefficientMatrix_published_residue
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 ((((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) i j)) :=
  tendsto_ckmrvLeechPlusCoefficientMatrix_published_residue_of_derivative_identification
    z hA hB (kleinModularJDerivative_eq_candidate z) i j

theorem tendsto_ckmrvLeechMinusCoefficientMatrix_published_residue
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 (((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) • ckmrvMinusResidueMatrix z) i j)) :=
  tendsto_ckmrvLeechMinusCoefficientMatrix_published_residue_of_derivative_identification
    z hA hB (kleinModularJDerivative_eq_candidate z) i j

theorem not_continuousAt_ckmrvEightPlus_imaginary {y : ℝ} (hy : 1 < y) :
    ¬ ContinuousAt (fun w : ℂ => ckmrvEightPlusCoefficientMatrix
      (UpperHalfPlane.ofComplex w) (UpperHalfPlane.ofComplex (Complex.I * y)) 0 2)
      ((UpperHalfPlane.ofComplex (Complex.I * y) : UpperHalfPlane) : ℂ) := by
  apply not_continuousAt_ckmrvEightPlus_diagonal _ (kleinModularJDerivative_imaginary_ne_zero hy)
  · intro h
    have ha := eisensteinFour_imaginary_re_lower (by linarith only [hy] : 0 < y)
    rw [h, Complex.zero_re] at ha
    norm_num at ha
  · intro h
    have hb := eisensteinSix_imaginary_re_pos hy
    rw [h, Complex.zero_re] at hb
    exact lt_irrefl 0 hb

end E8Leech
