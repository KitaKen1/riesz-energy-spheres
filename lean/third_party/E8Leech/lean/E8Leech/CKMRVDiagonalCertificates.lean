import E8Leech.CKMRVMeromorphic
import E8Leech.CKMRVResiduePositivity

/-!
# Diagonal numerator certificates and exact candidate residue normalization

Evaluate the four polynomial answers at tau=z and use E4^3-E6^2=1728 Delta.
The published expression for j' is only a candidate definition here. The
normalizations below are unconditional algebraic identities given E4,E6
nonzero, not proofs that this candidate is the actual derivative or that
any matrix is an analytic kernel residue.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open scoped Matrix

def ckmrvPlusResidueMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1; 0, -2, 0; 1, 0, 0]

def ckmrvKleinDerivativeCandidate (z : UpperHalfPlane) : ℂ :=
  -2 * (Real.pi : ℂ) * Complex.I * ModularForm.E₄ z ^ 2 * ModularForm.E₆ z /
    ModularForm.discriminant z

theorem ckmrvKleinCrossDifference_diagonal (z : UpperHalfPlane) :
    ckmrvKleinCrossDifference z z = 0 := by
  unfold ckmrvKleinCrossDifference
  ring

theorem ckmrvEightPlusPolynomialNumerator_diagonal (z : UpperHalfPlane) :
    ckmrvEightPlusPolynomialNumerator z z = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) • (ckmrvPlusResidueMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change ((ModularForm.E₆ z) * (ckmrvKleinCrossDifference z z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change ((ModularForm.discriminant z) * (ModularForm.E₆ z) * (ModularForm.E₄ z) ^ 2 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (1)
    ring
  · change (-2 * (ModularForm.E₄ z) * (ckmrvKleinCrossDifference z z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (-2 * (ModularForm.discriminant z) * (ModularForm.E₄ z) * (ModularForm.E₄ z) * (ModularForm.E₆ z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-2)
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) * (ModularForm.discriminant z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (1)
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring


theorem ckmrvEightMinusPolynomialNumerator_diagonal (z : UpperHalfPlane) :
    ckmrvEightMinusPolynomialNumerator z z = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) • (ckmrvMinusResidueMatrix z) := by
  have h := eisenstein_cubic_square_discriminant z
  ext i j
  fin_cases i <;> fin_cases j
  · change (-2 * 1728 * (ModularForm.discriminant z) * (ModularForm.E₄ z) * (ModularForm.E₄ z) * (ModularForm.E₆ z) : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-3456 * (ModularForm.discriminant z))
    ring
  · change (0 : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change (0 : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change (0 : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) * (ModularForm.E₄ z) ^ 2 : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * ((ModularForm.E₄ z) ^ 2)
    ring
  · change (-(ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) * (ModularForm.E₆ z) : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-(ModularForm.E₆ z))
    ring
  · change (0 : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change ((1728 * (ModularForm.discriminant z) - (ModularForm.E₄ z) ^ 3) * (ModularForm.E₄ z) ^ 2 : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-(ModularForm.E₆ z))
    linear_combination -((ModularForm.E₄ z) ^ 2) * h
  · change ((ModularForm.E₄ z) ^ 3 * (ModularForm.E₆ z) : ℂ) = ((ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * ((ModularForm.E₄ z))
    ring


theorem ckmrvLeechPlusPolynomialNumerator_diagonal (z : UpperHalfPlane) :
    ckmrvLeechPlusPolynomialNumerator z z = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) • (ckmrvPlusResidueMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (6 * (ckmrvKleinCrossDifference z z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) * (ModularForm.E₄ z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (0 : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change ((1728 * (ModularForm.discriminant z) * (ModularForm.discriminant z) - 6 * (ckmrvKleinCrossDifference z z)) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (1)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change ((-12 * (ModularForm.E₄ z) ^ 3 + 5 * 1728 * (ModularForm.discriminant z)) * (ckmrvKleinCrossDifference z z) * (ModularForm.E₄ z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (-2 * 1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-2)
    ring
  · change ((12 * (ModularForm.E₄ z) ^ 3 - 7 * 1728 * (ModularForm.discriminant z)) * (ckmrvKleinCrossDifference z z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change ((1728 * (ModularForm.discriminant z) * (ModularForm.discriminant z) + 6 * (ckmrvKleinCrossDifference z z)) * (ModularForm.E₄ z) * (ModularForm.E₆ z) * (ModularForm.E₄ z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (1)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (0 : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change (-6 * (ckmrvKleinCrossDifference z z) * (ModularForm.E₄ z) * (ModularForm.E₆ z) : ℂ) = (1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring


theorem ckmrvLeechMinusPolynomialNumerator_diagonal (z : UpperHalfPlane) :
    ckmrvLeechMinusPolynomialNumerator z z = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) • (ckmrvMinusResidueMatrix z) := by
  have h := eisenstein_cubic_square_discriminant z
  ext i j
  fin_cases i <;> fin_cases j
  · change (-2 * 1728 * (ModularForm.discriminant z) ^ 2 * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-3456 * (ModularForm.discriminant z))
    ring
  · change (-2 * 1728 * (ModularForm.discriminant z) * (ckmrvKleinCrossDifference z z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change (((ModularForm.E₄ z) ^ 3 * (ModularForm.discriminant z) + 2 * (ckmrvKleinCrossDifference z z)) * (ModularForm.E₄ z) * (ModularForm.E₆ z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * ((ModularForm.E₄ z) ^ 2)
    rw [ckmrvKleinCrossDifference_diagonal]
    ring
  · change (-(ModularForm.discriminant z) * (ModularForm.E₄ z) * (ModularForm.E₆ z) * (ModularForm.E₄ z) * (ModularForm.E₆ z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-(ModularForm.E₆ z))
    ring
  · change (0 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (0)
    ring
  · change ((1728 * (ModularForm.discriminant z) * (ModularForm.discriminant z) - 2 * (ckmrvKleinCrossDifference z z) - (ModularForm.E₄ z) ^ 3 * (ModularForm.discriminant z)) * (ModularForm.E₄ z) ^ 2 : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * (-(ModularForm.E₆ z))
    rw [ckmrvKleinCrossDifference_diagonal]
    linear_combination -((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2) * h
  · change ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₄ z) * (ModularForm.E₆ z) : ℂ) = ((ModularForm.discriminant z) * (ModularForm.E₄ z) ^ 2 * (ModularForm.E₆ z)) * ((ModularForm.E₄ z))
    ring


theorem ckmrvKleinDerivativeCandidate_ne_zero (z : UpperHalfPlane)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    ckmrvKleinDerivativeCandidate z ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp)
      Complex.I_ne_zero) (pow_ne_zero 2 hA)) hB)
    (ModularForm.discriminant_ne_zero z)

theorem ckmrvKleinDerivativeCandidate_imaginary_ne_zero {y : ℝ} (hy : 1 < y) :
    ckmrvKleinDerivativeCandidate (UpperHalfPlane.ofComplex (Complex.I * y)) ≠ 0 := by
  apply ckmrvKleinDerivativeCandidate_ne_zero
  · intro h
    have ha := eisensteinFour_imaginary_re_lower (by linarith only [hy] : 0 < y)
    rw [h, Complex.zero_re] at ha
    norm_num at ha
  · intro h
    have hb := eisensteinSix_imaginary_re_pos hy
    rw [h, Complex.zero_re] at hb
    exact lt_irrefl 0 hb

theorem ckmrvEightPlus_diagonal_normalization (z : UpperHalfPlane)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    (ckmrvPlusScale * ModularForm.discriminant z ^ 2 *
      ckmrvKleinDerivativeCandidate z)⁻¹ • ckmrvEightPlusPolynomialNumerator z z =
      ((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix := by
  rw [ckmrvEightPlusPolynomialNumerator_diagonal, smul_smul]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [ckmrvPlusScale, ckmrvKleinDerivativeCandidate,
    zpow_neg, zpow_ofNat, div_eq_mul_inv]
  field_simp [hp, hA, hB, Complex.I_ne_zero, ModularForm.discriminant_ne_zero z]
  simp only [Complex.I_sq]
  ring

theorem ckmrvEightMinus_diagonal_normalization (z : UpperHalfPlane)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    (ckmrvMinusScale * ModularForm.discriminant z ^ 2 *
      ckmrvKleinDerivativeCandidate z)⁻¹ • ckmrvEightMinusPolynomialNumerator z z =
      (Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) • ckmrvMinusResidueMatrix z := by
  rw [ckmrvEightMinusPolynomialNumerator_diagonal, smul_smul]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [ckmrvMinusScale, ckmrvKleinDerivativeCandidate, div_eq_mul_inv]
  field_simp [hp, hA, hB, Complex.I_ne_zero, ModularForm.discriminant_ne_zero z]
  simp only [Complex.I_sq]
  ring

theorem ckmrvLeechPlus_diagonal_normalization (z : UpperHalfPlane)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    ((1728 * ckmrvPlusScale) * ModularForm.discriminant z ^ 3 *
      ckmrvKleinDerivativeCandidate z)⁻¹ • ckmrvLeechPlusPolynomialNumerator z z =
      ((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix := by
  rw [ckmrvLeechPlusPolynomialNumerator_diagonal, smul_smul]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [ckmrvPlusScale, ckmrvKleinDerivativeCandidate,
    zpow_neg, zpow_ofNat, div_eq_mul_inv]
  field_simp [hp, hA, hB, Complex.I_ne_zero, ModularForm.discriminant_ne_zero z]
  simp only [Complex.I_sq]
  ring

theorem ckmrvLeechMinus_diagonal_normalization (z : UpperHalfPlane)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    (ckmrvMinusScale * ModularForm.discriminant z ^ 3 *
      ckmrvKleinDerivativeCandidate z)⁻¹ • ckmrvLeechMinusPolynomialNumerator z z =
      (Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) • ckmrvMinusResidueMatrix z := by
  rw [ckmrvLeechMinusPolynomialNumerator_diagonal, smul_smul]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [ckmrvMinusScale, ckmrvKleinDerivativeCandidate, div_eq_mul_inv]
  field_simp [hp, hA, hB, Complex.I_ne_zero, ModularForm.discriminant_ne_zero z]
  simp only [Complex.I_sq]
  ring

end E8Leech
