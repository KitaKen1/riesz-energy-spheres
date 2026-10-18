import E8Leech.CKMRVCoefficientMatrices

/-!
# Four denominator-free polynomial numerators for the published coefficient formulas

Choose H = E4(tau)^3 Delta(z) - Delta(tau) E4(z)^3 as the known answer.
After the appropriate common denominator and constant prefactor are cleared,
each coefficient matrix is an explicit finite polynomial in actual E4, E6
and Delta values. All Delta and j-gap reciprocals disappear from the numerator.
The finite identities are checked entry by entry by the kernel.

Continuity of these polynomials includes equal-j pairs. This does not extend
the original coefficient quotient across a pole, nor identify phi/psi kernel
contractions, their analytic residues, or their signs.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3

noncomputable section
namespace E8Leech
open scoped Matrix

def ckmrvKleinCrossDifference (τ z : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ τ ^ 3 * ModularForm.discriminant z -
    ModularForm.discriminant τ * ModularForm.E₄ z ^ 3

def ckmrvEightPlusPolynomialNumerator (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  let A := ModularForm.E₄ τ
  let B := ModularForm.E₆ τ
  let D := ModularForm.discriminant τ
  let a := ModularForm.E₄ z
  let b := ModularForm.E₆ z
  let d := ModularForm.discriminant z
  let H := ckmrvKleinCrossDifference τ z
  !![B * H, 0, D * B * a ^ 2;
     -2 * A * H, -2 * D * A * a * b, 0;
     A ^ 2 * B * d, 0, 0]

def ckmrvEightMinusPolynomialNumerator (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  let A := ModularForm.E₄ τ
  let B := ModularForm.E₆ τ
  let D := ModularForm.discriminant τ
  let a := ModularForm.E₄ z
  let b := ModularForm.E₆ z
  !![-2 * 1728 * D * A * a * b, 0, 0;
     0, A ^ 2 * B * a ^ 2, -A ^ 2 * B * b;
     0, (1728 * D - A ^ 3) * a ^ 2, A ^ 3 * b]

def ckmrvLeechPlusPolynomialNumerator (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  let A := ModularForm.E₄ τ
  let B := ModularForm.E₆ τ
  let D := ModularForm.discriminant τ
  let a := ModularForm.E₄ z
  let b := ModularForm.E₆ z
  let d := ModularForm.discriminant z
  let H := ckmrvKleinCrossDifference τ z
  !![6 * H * A ^ 2 * B * a, 0, (1728 * D * d - 6 * H) * A ^ 2 * B;
     (-12 * A ^ 3 + 5 * 1728 * D) * H * a, -2 * 1728 * D ^ 2 * a ^ 2 * b,
       (12 * A ^ 3 - 7 * 1728 * D) * H;
     (1728 * D * d + 6 * H) * A * B * a, 0, -6 * H * A * B]

def ckmrvLeechMinusPolynomialNumerator (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  let A := ModularForm.E₄ τ
  let B := ModularForm.E₆ τ
  let D := ModularForm.discriminant τ
  let a := ModularForm.E₄ z
  let b := ModularForm.E₆ z
  let d := ModularForm.discriminant z
  let H := ckmrvKleinCrossDifference τ z
  !![-2 * 1728 * D ^ 2 * a ^ 2 * b, -2 * 1728 * D * H, 0;
     0, (A ^ 3 * d + 2 * H) * A * B, -D * A * B * a * b;
     0, (1728 * D * d - 2 * H - A ^ 3 * d) * A ^ 2, D * A ^ 2 * a * b]

theorem ckmrvKleinCrossDifference_eq (τ z : UpperHalfPlane) :
    ckmrvKleinCrossDifference τ z = ModularForm.discriminant τ * ModularForm.discriminant z *
      (kleinModularJ τ - kleinModularJ z) := by
  unfold ckmrvKleinCrossDifference kleinModularJ
  field_simp [ModularForm.discriminant_ne_zero τ, ModularForm.discriminant_ne_zero z]

theorem ckmrvEightPlusCoefficientMatrix_polynomial (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvEightPlusCoefficientMatrix τ z =
      ckmrvPlusScale⁻¹ • ckmrvEightPlusPolynomialNumerator τ z := by
  rw [ckmrvEightPlusCoefficientMatrix_clear τ z hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, ckmrvModularCoreMatrix_apply,
      ckmrvModularFactor_eq_products, ckmrvEightPlusCore,
      ckmrvEightPlusPolynomialNumerator, ckmrvKleinCrossDifference, kleinModularJ] <;>
    field_simp [ckmrvPlusScale_ne_zero, ModularForm.discriminant_ne_zero τ,
      ModularForm.discriminant_ne_zero z]

theorem ckmrvEightMinusCoefficientMatrix_polynomial (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvEightMinusCoefficientMatrix τ z =
      ckmrvMinusScale⁻¹ • ckmrvEightMinusPolynomialNumerator τ z := by
  rw [ckmrvEightMinusCoefficientMatrix_clear τ z hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, ckmrvModularCoreMatrix_apply,
      ckmrvModularFactor_eq_products, ckmrvEightMinusCore,
      ckmrvEightMinusPolynomialNumerator, kleinModularJ] <;>
    field_simp [ckmrvMinusScale_ne_zero, ModularForm.discriminant_ne_zero τ,
      ModularForm.discriminant_ne_zero z]

theorem ckmrvLeechPlusCoefficientMatrix_polynomial (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvLeechPlusCoefficientMatrix τ z =
      (1728 * ckmrvPlusScale)⁻¹ • ckmrvLeechPlusPolynomialNumerator τ z := by
  rw [ckmrvLeechPlusCoefficientMatrix_clear τ z hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, ckmrvModularCoreMatrix_apply,
      ckmrvModularFactor_eq_products, ckmrvLeechPlusClearedCore,
      ckmrvLeechPlusPolynomialNumerator, ckmrvKleinCrossDifference, kleinModularJ] <;>
    field_simp [ckmrvPlusScale_ne_zero, ModularForm.discriminant_ne_zero τ,
      ModularForm.discriminant_ne_zero z]

theorem ckmrvLeechMinusCoefficientMatrix_polynomial (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvLeechMinusCoefficientMatrix τ z =
      ckmrvMinusScale⁻¹ • ckmrvLeechMinusPolynomialNumerator τ z := by
  rw [ckmrvLeechMinusCoefficientMatrix_clear τ z hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, ckmrvModularCoreMatrix_apply,
      ckmrvModularFactor_eq_products, ckmrvLeechMinusCore,
      ckmrvLeechMinusPolynomialNumerator, ckmrvKleinCrossDifference, kleinModularJ] <;>
    field_simp [ckmrvMinusScale_ne_zero, ModularForm.discriminant_ne_zero τ,
      ModularForm.discriminant_ne_zero z]

theorem continuous_ckmrvEightPlusPolynomialNumerator_entry (i j : Fin 3) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightPlusPolynomialNumerator p.1 p.2 i j) := by
  have hA : Continuous (ModularForm.E₄ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₄
  have hB : Continuous (ModularForm.E₆ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₆
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.1) * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.1) * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) ^ 2)
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -2 * (ModularForm.E₄ p.1) * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -2 * (ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.discriminant p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop

theorem continuous_ckmrvEightMinusPolynomialNumerator_entry (i j : Fin 3) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightMinusPolynomialNumerator p.1 p.2 i j) := by
  have hA : Continuous (ModularForm.E₄ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₄
  have hB : Continuous (ModularForm.E₆ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₆
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -2 * 1728 * (ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) ^ 2)
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -(ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.E₆ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (1728 * (ModularForm.discriminant p.1) - (ModularForm.E₄ p.1) ^ 3) * (ModularForm.E₄ p.2) ^ 2)
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1) ^ 3 * (ModularForm.E₆ p.2))
    fun_prop

theorem continuous_ckmrvLeechPlusPolynomialNumerator_entry (i j : Fin 3) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechPlusPolynomialNumerator p.1 p.2 i j) := by
  have hA : Continuous (ModularForm.E₄ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₄
  have hB : Continuous (ModularForm.E₆ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₆
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => 6 * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3) * (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (1728 * (ModularForm.discriminant p.1) * (ModularForm.discriminant p.2) - 6 * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3)) * (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (-12 * (ModularForm.E₄ p.1) ^ 3 + 5 * 1728 * (ModularForm.discriminant p.1)) * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3) * (ModularForm.E₄ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -2 * 1728 * (ModularForm.discriminant p.1) ^ 2 * (ModularForm.E₄ p.2) ^ 2 * (ModularForm.E₆ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (12 * (ModularForm.E₄ p.1) ^ 3 - 7 * 1728 * (ModularForm.discriminant p.1)) * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (1728 * (ModularForm.discriminant p.1) * (ModularForm.discriminant p.2) + 6 * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3)) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -6 * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1))
    fun_prop

theorem continuous_ckmrvLeechMinusPolynomialNumerator_entry (i j : Fin 3) :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechMinusPolynomialNumerator p.1 p.2 i j) := by
  have hA : Continuous (ModularForm.E₄ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₄
  have hB : Continuous (ModularForm.E₆ : UpperHalfPlane → ℂ) :=
    ModularFormClass.continuous ModularForm.E₆
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  fin_cases i <;> fin_cases j
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -2 * 1728 * (ModularForm.discriminant p.1) ^ 2 * (ModularForm.E₄ p.2) ^ 2 * (ModularForm.E₆ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -2 * 1728 * (ModularForm.discriminant p.1) * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.E₄ p.1) ^ 3 * (ModularForm.discriminant p.2) + 2 * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3)) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => -(ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (0 : ℂ))
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (1728 * (ModularForm.discriminant p.1) * (ModularForm.discriminant p.2) - 2 * ((ModularForm.E₄ p.1) ^ 3 * ModularForm.discriminant p.2 - ModularForm.discriminant p.1 * (ModularForm.E₄ p.2) ^ 3) - (ModularForm.E₄ p.1) ^ 3 * (ModularForm.discriminant p.2)) * (ModularForm.E₄ p.1) ^ 2)
    fun_prop
  · change Continuous (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2))
    fun_prop

end E8Leech
