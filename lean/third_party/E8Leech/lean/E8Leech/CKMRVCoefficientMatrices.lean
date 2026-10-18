import E8Leech.EisensteinProductIdentities
import E8Leech.CKMRVCoreMatrices

/-!
# Actual diagonal factors and the four published CKMRV coefficient formulas

Section 4.4 of arXiv:1902.05438v3 is used as an explicit candidate formula.
The nine factors are ordered by weights -2, 0, 2, 4, 6, 8, 10, 12, 14.
All Eisenstein entries use Mathlib's actual normalized modular forms.
The three product identities are proved separately, not assumed.

This constructs the four coefficient-matrix formulas with their exact
pi/I/Delta/j prefactors and verifies common-denominator clearing. It does
not prove that their phi/psi contractions are the analytic CKMRV kernels,
or prove modular functional equations, residues, Fourier identities or signs.
-/

set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 3

noncomputable section
namespace E8Leech
open Set
open scoped Matrix BigOperators

/-- Finite weight order: -2, 0, 2, 4, 6, 8, 10, 12, 14. -/
def ckmrvModularFactor (z : UpperHalfPlane) : Fin 9 → ℂ :=
  ![ModularForm.E (by norm_num : 3 ≤ 10) z / ModularForm.discriminant z,
    1, ModularForm.E (by norm_num : 3 ≤ 14) z / ModularForm.discriminant z,
    ModularForm.E₄ z, ModularForm.E₆ z,
    ModularForm.E (by norm_num : 3 ≤ 8) z,
    ModularForm.E (by norm_num : 3 ≤ 10) z,
    ModularForm.discriminant z, ModularForm.E (by norm_num : 3 ≤ 14) z]

section FiniteAlgebra
variable {𝕜 : Type*} [Field 𝕜]

def ckmrvDiagonalCore (l r : Fin 3 → 𝕜) (M : Matrix (Fin 3) (Fin 3) 𝕜) :
    Matrix (Fin 3) (Fin 3) 𝕜 := Matrix.diagonal l * M * Matrix.diagonal r

theorem ckmrvDiagonalCore_apply (l r : Fin 3 → 𝕜) (M : Matrix (Fin 3) (Fin 3) 𝕜)
    (i j : Fin 3) : ckmrvDiagonalCore l r M i j = l i * M i j * r j := by
  simp [ckmrvDiagonalCore, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem ckmrvDiagonalCore_contract (a b l r : Fin 3 → 𝕜)
    (M : Matrix (Fin 3) (Fin 3) 𝕜) :
    ckmrvCoreContraction a b (ckmrvDiagonalCore l r M) =
      ckmrvCoreContraction (fun i => a i * l i) (fun j => r j * b j) M := by
  simp [ckmrvCoreContraction, ckmrvDiagonalCore_apply, mul_assoc]

theorem ckmrvDiagonalCore_smul (c : 𝕜) (l r : Fin 3 → 𝕜)
    (M : Matrix (Fin 3) (Fin 3) 𝕜) :
    c • ckmrvDiagonalCore l r M = ckmrvDiagonalCore l r (c • M) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, ckmrvDiagonalCore_apply]
  ring

theorem ckmrvCoreContraction_smul (c : 𝕜) (a b : Fin 3 → 𝕜)
    (M : Matrix (Fin 3) (Fin 3) 𝕜) :
    ckmrvCoreContraction a b (c • M) = c * ckmrvCoreContraction a b M := by
  simp only [ckmrvCoreContraction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ckmrv_matrix_clear_common (A D g s : 𝕜)
    (hD : D ≠ 0) (hg : g ≠ 0) (hs : s ≠ 0) (M : Matrix (Fin 3) (Fin 3) 𝕜) :
    (A * D * g) • ((s * D * g)⁻¹ • M) = (A / s) • M := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

theorem ckmrv_matrix_clear_leech_plus (A D g s : 𝕜)
    (hD : D ≠ 0) (hs : s ≠ 0) (M : Matrix (Fin 3) (Fin 3) 𝕜) :
    (A * D ^ 2 * g) • ((s * D)⁻¹ • M) = (A * D / s) • (g • M) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  field_simp

end FiniteAlgebra

/-- The two actual diagonal modular factors surrounding a finite core. -/
def ckmrvModularCoreMatrix (l r : Fin 3 → Fin 9) (τ z : UpperHalfPlane)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ckmrvDiagonalCore (fun i => ckmrvModularFactor τ (l i))
    (fun j => ckmrvModularFactor z (r j)) M

def ckmrvPlusScale : ℂ := 36 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I

def ckmrvMinusScale : ℂ := 2 * 1728 * (Real.pi : ℂ)

def ckmrvEightPlusCoefficientMatrix (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  (ckmrvPlusScale * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z))⁻¹ •
    ckmrvModularCoreMatrix ![4, 3, 2] ![7, 6, 5] τ z
      (ckmrvEightPlusCore (kleinModularJ τ - kleinModularJ z))

def ckmrvLeechPlusCoefficientMatrix (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1728 * ckmrvPlusScale * ModularForm.discriminant z)⁻¹ •
    ckmrvModularCoreMatrix ![8, 7, 6] ![3, 2, 1] τ z
      (ckmrvLeechPlusCore (kleinModularJ τ) (kleinModularJ τ - kleinModularJ z))

def ckmrvEightMinusCoefficientMatrix (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  (ckmrvMinusScale * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z))⁻¹ •
    ckmrvModularCoreMatrix ![3, 2, 1] ![6, 5, 4] τ z
      (ckmrvEightMinusCore (kleinModularJ τ))

def ckmrvLeechMinusCoefficientMatrix (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  (ckmrvMinusScale * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z))⁻¹ •
    ckmrvModularCoreMatrix ![7, 6, 5] ![2, 1, 0] τ z
      (ckmrvLeechMinusCore (kleinModularJ τ) (kleinModularJ τ - kleinModularJ z))

theorem ckmrvModularFactor_eq_products (z : UpperHalfPlane) :
    ckmrvModularFactor z =
      ![ModularForm.E₄ z * ModularForm.E₆ z / ModularForm.discriminant z,
        1, ModularForm.E₄ z ^ 2 * ModularForm.E₆ z / ModularForm.discriminant z,
        ModularForm.E₄ z, ModularForm.E₆ z, ModularForm.E₄ z ^ 2,
        ModularForm.E₄ z * ModularForm.E₆ z, ModularForm.discriminant z,
        ModularForm.E₄ z ^ 2 * ModularForm.E₆ z] := by
  ext k
  fin_cases k <;> dsimp [ckmrvModularFactor]
  · exact congrArg (fun v => v / ModularForm.discriminant z) (eisensteinTen_eq_four_mul_six z)
  · exact congrArg (fun v => v / ModularForm.discriminant z) (eisensteinFourteen_eq_four_sq_mul_six z)
  · exact eisensteinEight_eq_four_sq z
  · exact eisensteinTen_eq_four_mul_six z
  · exact eisensteinFourteen_eq_four_sq_mul_six z

theorem ckmrvModularFactor_imaginary_eq_q {y : ℝ} (hy : 0 < y) (k : Fin 9) :
    ckmrvModularFactor (UpperHalfPlane.ofComplex (Complex.I * y)) k =
      (let A := eisensteinFourQ (imaginaryNome y)
       let B := eisensteinSixQ (imaginaryNome y)
       let D := discriminantQ (imaginaryNome y)
       ![A * B / D, 1, A ^ 2 * B / D, A, B, A ^ 2, A * B, D, A ^ 2 * B] k : ℝ) := by
  rw [ckmrvModularFactor_eq_products]
  fin_cases k <;>
    simp [eisensteinFour_imaginary_eq_q hy, eisensteinSix_imaginary_eq_q hy,
      discriminant_imaginary_eq_q hy]

theorem ckmrvModularFactor_imaginary_re_pos {y : ℝ} (hy : 1 < y) (k : Fin 9) :
    0 < (ckmrvModularFactor (UpperHalfPlane.ofComplex (Complex.I * y)) k).re := by
  rw [ckmrvModularFactor_imaginary_eq_q (by linarith only [hy]), Complex.ofReal_re]
  have hA : 0 < eisensteinFourQ (imaginaryNome y) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (eisensteinFourQ_lower (imaginaryNome_pos y).le)
  have hB := eisensteinSix_imaginary_re_pos hy
  rw [eisensteinSix_imaginary_eq_q (by linarith only [hy]), Complex.ofReal_re] at hB
  have hD := discriminantQ_nome_pos (by linarith only [hy] : 0 < y)
  fin_cases k <;> dsimp <;> positivity

theorem ckmrvPlusScale_ne_zero : ckmrvPlusScale ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) (zpow_ne_zero _ hp)) Complex.I_ne_zero

theorem ckmrvMinusScale_ne_zero : ckmrvMinusScale ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (by norm_num) hp

theorem ckmrvModularCoreMatrix_apply (l r : Fin 3 → Fin 9) (τ z : UpperHalfPlane)
    (M : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    ckmrvModularCoreMatrix l r τ z M i j =
      ckmrvModularFactor τ (l i) * M i j * ckmrvModularFactor z (r j) :=
  ckmrvDiagonalCore_apply _ _ _ _ _

theorem ckmrvModularCoreMatrix_contract (l r : Fin 3 → Fin 9) (τ z : UpperHalfPlane)
    (M : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3 → ℂ) :
    ckmrvCoreContraction a b (ckmrvModularCoreMatrix l r τ z M) =
      ckmrvCoreContraction (fun i => a i * ckmrvModularFactor τ (l i))
        (fun j => ckmrvModularFactor z (r j) * b j) M :=
  ckmrvDiagonalCore_contract _ _ _ _ _

theorem ckmrvModularCoreMatrix_smul (c : ℂ) (l r : Fin 3 → Fin 9) (τ z : UpperHalfPlane)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    c • ckmrvModularCoreMatrix l r τ z M = ckmrvModularCoreMatrix l r τ z (c • M) :=
  ckmrvDiagonalCore_smul _ _ _ _

theorem ckmrvEightPlusCoefficientMatrix_clear (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvEightPlusCoefficientMatrix τ z =
    (ModularForm.discriminant τ / ckmrvPlusScale) •
      ckmrvModularCoreMatrix ![4, 3, 2] ![7, 6, 5] τ z
        (ckmrvEightPlusCore (kleinModularJ τ - kleinModularJ z)) :=
  ckmrv_matrix_clear_common _ _ _ _ (ModularForm.discriminant_ne_zero _) hg
    ckmrvPlusScale_ne_zero _

theorem ckmrvEightMinusCoefficientMatrix_clear (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvEightMinusCoefficientMatrix τ z =
    (ModularForm.discriminant τ / ckmrvMinusScale) •
      ckmrvModularCoreMatrix ![3, 2, 1] ![6, 5, 4] τ z
        (ckmrvEightMinusCore (kleinModularJ τ)) :=
  ckmrv_matrix_clear_common _ _ _ _ (ModularForm.discriminant_ne_zero _) hg
    ckmrvMinusScale_ne_zero _

theorem ckmrvLeechMinusCoefficientMatrix_clear (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvLeechMinusCoefficientMatrix τ z =
    (ModularForm.discriminant τ * ModularForm.discriminant z / ckmrvMinusScale) •
      ckmrvModularCoreMatrix ![7, 6, 5] ![2, 1, 0] τ z
        (ckmrvLeechMinusCore (kleinModularJ τ) (kleinModularJ τ - kleinModularJ z)) := by
  rw [show ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z) =
    (ModularForm.discriminant τ * ModularForm.discriminant z) * ModularForm.discriminant z *
      (kleinModularJ τ - kleinModularJ z) by ring]
  exact ckmrv_matrix_clear_common _ _ _ _ (ModularForm.discriminant_ne_zero _) hg
    ckmrvMinusScale_ne_zero _

theorem ckmrvLeechPlusCoefficientMatrix_clear (τ z : UpperHalfPlane)
    (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
      (kleinModularJ τ - kleinModularJ z)) • ckmrvLeechPlusCoefficientMatrix τ z =
    (ModularForm.discriminant τ * ModularForm.discriminant z / (1728 * ckmrvPlusScale)) •
      ckmrvModularCoreMatrix ![8, 7, 6] ![3, 2, 1] τ z
        (ckmrvLeechPlusClearedCore (kleinModularJ τ) (kleinModularJ τ - kleinModularJ z)) := by
  unfold ckmrvLeechPlusCoefficientMatrix
  rw [ckmrv_matrix_clear_leech_plus _ _ _ _ (ModularForm.discriminant_ne_zero _)
      (mul_ne_zero (by norm_num) ckmrvPlusScale_ne_zero),
    ckmrvModularCoreMatrix_smul, ckmrvLeechPlusCore_clear _ _ hg]

end E8Leech
