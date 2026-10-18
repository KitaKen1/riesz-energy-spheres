import E8Leech.CKMRVPlusKernels

/-!
# Actual plus kernels: affine translation and the T annihilator

The explicit phi formulas make every integer translate affine. The actual
coefficient matrices are periodic, so contraction preserves that affine law.
This verifies the T part of CKMRV Theorem 4.3(2) directly, without constructing
or classifying the group-ring annihilator quotient. Statements concern the
totalized explicit formulas; analytic extensions and orbit poles are separate.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open UpperHalfPlane
open scoped MatrixGroups ModularForm Matrix BigOperators

theorem ckmrvTranslate_zero (z : UpperHalfPlane) : ckmrvTranslate 0 z = z := by
  apply UpperHalfPlane.ext
  simp [ckmrvTranslate_coe]

theorem ckmrvTranslate_add (n m : ℤ) (z : UpperHalfPlane) :
    ckmrvTranslate n (ckmrvTranslate m z) = ckmrvTranslate (m + n) z := by
  apply UpperHalfPlane.ext
  simp only [ckmrvTranslate_coe, Int.cast_add]
  ring

theorem ckmrvTranslate_eq_T_zpow (n : ℤ) (z : UpperHalfPlane) :
    ckmrvTranslate n z = ModularGroup.T ^ n • z := by
  rw [UpperHalfPlane.modular_T_zpow_smul]
  apply UpperHalfPlane.ext
  simp [ckmrvTranslate_coe, UpperHalfPlane.coe_vadd, add_comm]

def ckmrvPhiTranslationSlope (z : UpperHalfPlane) : Fin 3 → ℂ :=
  ![1, EisensteinSeries.E2 z, EisensteinSeries.E2 z ^ 2]

theorem ckmrvPhiTranslationSlope_translate (n : ℤ) (z : UpperHalfPlane) :
    ckmrvPhiTranslationSlope (ckmrvTranslate n z) = ckmrvPhiTranslationSlope z := by
  simp only [ckmrvPhiTranslationSlope, eisensteinTwo_translate]

theorem ckmrvPhiBasis_translate_affine (n : ℤ) (z : UpperHalfPlane) (i : Fin 3) :
    ckmrvPhiBasis (ckmrvTranslate n z) i =
      ckmrvPhiBasis z i + (n : ℂ) * ckmrvPhiTranslationSlope z i := by
  rw [ckmrvPhiBasis_translate]
  fin_cases i <;> simp [ckmrvPhiBasis, ckmrvPhiTranslationSlope] <;> ring

theorem ckmrvCoreContraction_affine_left {𝕜 : Type*} [Field 𝕜]
    (a v b : Fin 3 → 𝕜) (M : Matrix (Fin 3) (Fin 3) 𝕜) (c : 𝕜) :
    ckmrvCoreContraction (fun i => a i + c * v i) b M =
      ckmrvCoreContraction a b M + c * ckmrvCoreContraction v b M := by
  simp only [ckmrvCoreContraction, Fin.sum_univ_three]
  ring

def ckmrvEightPlusTranslationSlope (τ z : UpperHalfPlane) : ℂ :=
  ckmrvCoreContraction (ckmrvPhiTranslationSlope τ) (ckmrvTildePhiBasis z)
    (ckmrvEightPlusCoefficientMatrix τ z)

def ckmrvLeechPlusTranslationSlope (τ z : UpperHalfPlane) : ℂ :=
  ckmrvCoreContraction (ckmrvPhiTranslationSlope τ) (ckmrvTildePhiBasis z)
    (ckmrvLeechPlusCoefficientMatrix τ z)

theorem ckmrvEightPlusKernel_translate_affine (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvEightPlusKernel (ckmrvTranslate n τ) z =
      ckmrvEightPlusKernel τ z + (n : ℂ) * ckmrvEightPlusTranslationSlope τ z := by
  unfold ckmrvEightPlusKernel ckmrvEightPlusTranslationSlope
  have hphi : ckmrvPhiBasis (ckmrvTranslate n τ) =
      (fun i => ckmrvPhiBasis τ i + (n : ℂ) * ckmrvPhiTranslationSlope τ i) :=
    funext (ckmrvPhiBasis_translate_affine n τ)
  rw [ckmrvEightPlusCoefficientMatrix_translate_left, hphi]
  exact ckmrvCoreContraction_affine_left _ _ _ _ _

theorem ckmrvLeechPlusKernel_translate_affine (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvLeechPlusKernel (ckmrvTranslate n τ) z =
      ckmrvLeechPlusKernel τ z + (n : ℂ) * ckmrvLeechPlusTranslationSlope τ z := by
  unfold ckmrvLeechPlusKernel ckmrvLeechPlusTranslationSlope
  have hphi : ckmrvPhiBasis (ckmrvTranslate n τ) =
      (fun i => ckmrvPhiBasis τ i + (n : ℂ) * ckmrvPhiTranslationSlope τ i) :=
    funext (ckmrvPhiBasis_translate_affine n τ)
  rw [ckmrvLeechPlusCoefficientMatrix_translate_left, hphi]
  exact ckmrvCoreContraction_affine_left _ _ _ _ _

theorem ckmrvEightPlusTranslationSlope_translate (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvEightPlusTranslationSlope (ckmrvTranslate n τ) z =
      ckmrvEightPlusTranslationSlope τ z := by
  simp only [ckmrvEightPlusTranslationSlope, ckmrvPhiTranslationSlope_translate,
    ckmrvEightPlusCoefficientMatrix_translate_left]

theorem ckmrvLeechPlusTranslationSlope_translate (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvLeechPlusTranslationSlope (ckmrvTranslate n τ) z =
      ckmrvLeechPlusTranslationSlope τ z := by
  simp only [ckmrvLeechPlusTranslationSlope, ckmrvPhiTranslationSlope_translate,
    ckmrvLeechPlusCoefficientMatrix_translate_left]

theorem ckmrvEightPlusKernel_translate_second_difference (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvEightPlusKernel (ckmrvTranslate (2 * n) τ) z -
      2 * ckmrvEightPlusKernel (ckmrvTranslate n τ) z + ckmrvEightPlusKernel τ z = 0 := by
  simp only [ckmrvEightPlusKernel_translate_affine, Int.cast_mul, Int.cast_ofNat]
  ring

theorem ckmrvLeechPlusKernel_translate_second_difference (n : ℤ) (τ z : UpperHalfPlane) :
    ckmrvLeechPlusKernel (ckmrvTranslate (2 * n) τ) z -
      2 * ckmrvLeechPlusKernel (ckmrvTranslate n τ) z + ckmrvLeechPlusKernel τ z = 0 := by
  simp only [ckmrvLeechPlusKernel_translate_affine, Int.cast_mul, Int.cast_ofNat]
  ring

theorem ckmrv_slash_T_apply (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    (f ∣[k] ModularGroup.T) τ = f (ckmrvTranslate 1 τ) := by
  have hT : ModularGroup.T • τ = ckmrvTranslate 1 τ := by
    simpa only [zpow_one] using (ckmrvTranslate_eq_T_zpow 1 τ).symm
  rw [ModularForm.SL_slash_apply, hT]
  have hd : denom ModularGroup.T (τ : ℂ) = 1 := by
    simp [denom, ModularGroup.T, Matrix.SpecialLinearGroup.map]
  rw [hd, one_zpow, mul_one]

theorem ckmrvEightPlusKernel_slash_T_second_difference (z : UpperHalfPlane) :
    (((fun τ => ckmrvEightPlusKernel τ z) ∣[(4 : ℤ)] ModularGroup.T) ∣[(4 : ℤ)]
      ModularGroup.T) - (2 : ℂ) • ((fun τ => ckmrvEightPlusKernel τ z) ∣[(4 : ℤ)]
        ModularGroup.T) + (fun τ => ckmrvEightPlusKernel τ z) = 0 := by
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrv_slash_T_apply, ckmrvTranslate_add]
  simpa only [mul_one, show (1 : ℤ) + 1 = 2 from rfl] using
    ckmrvEightPlusKernel_translate_second_difference 1 τ z

theorem ckmrvLeechPlusKernel_slash_T_second_difference (z : UpperHalfPlane) :
    (((fun τ => ckmrvLeechPlusKernel τ z) ∣[(12 : ℤ)] ModularGroup.T) ∣[(12 : ℤ)]
      ModularGroup.T) - (2 : ℂ) • ((fun τ => ckmrvLeechPlusKernel τ z) ∣[(12 : ℤ)]
        ModularGroup.T) + (fun τ => ckmrvLeechPlusKernel τ z) = 0 := by
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrv_slash_T_apply, ckmrvTranslate_add]
  simpa only [mul_one, show (1 : ℤ) + 1 = 2 from rfl] using
    ckmrvLeechPlusKernel_translate_second_difference 1 τ z

end E8Leech
