import E8Leech.CKMRVPlusTranslation

/-!
# Actual plus kernels: S covariance

We use the actual E2 transformation and level-one modular forms to verify
the published formulas directly. The left weights of phi times its row
factor are 4 and 12. Consequently the actual explicit plus kernels have
S eigenvalue -1, as in CKMRV Theorem 4.3(2). No minus logarithmic branch,
growth condition, orbit classification or Fourier certificate is supplied.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open UpperHalfPlane
open scoped MatrixGroups ModularForm Matrix BigOperators

theorem levelOne_S {k : ℤ} (f : ModularForm 𝒮ℒ k) (z : UpperHalfPlane) :
    f (ModularGroup.S • z) = (z : ℂ) ^ k * f z := by
  rw [ModularGroup.sl_moeb]
  simpa only [ModularGroup.denom_S] using
    SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) (k := k) f
      (γ := (ModularGroup.S : GL (Fin 2) ℝ)) ⟨ModularGroup.S, rfl⟩ z

theorem discriminant_S (z : UpperHalfPlane) :
    ModularForm.discriminant (ModularGroup.S • z) =
      (z : ℂ) ^ 12 * ModularForm.discriminant z := by
  rw [ModularGroup.sl_moeb]
  simpa only [CuspForm.coe_discriminant, ModularGroup.denom_S, zpow_ofNat] using
    SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) (k := 12) CuspForm.discriminant
      (γ := (ModularGroup.S : GL (Fin 2) ℝ)) ⟨ModularGroup.S, rfl⟩ z

theorem eisensteinTwo_S_explicit (z : UpperHalfPlane) :
    EisensteinSeries.E2 (ModularGroup.S • z) =
      (z : ℂ) ^ 2 * EisensteinSeries.E2 z - 6 * Complex.I / (Real.pi : ℂ) * (z : ℂ) := by
  have h := eisensteinTwo_slash_S_explicit z
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S] at h
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [zpow_neg, zpow_ofNat] at h
  field_simp [hp, z.ne_zero] at h ⊢
  linear_combination h

theorem kleinModularJ_S (z : UpperHalfPlane) :
    kleinModularJ (ModularGroup.S • z) = kleinModularJ z := by
  unfold kleinModularJ
  rw [levelOne_S ModularForm.E₄, discriminant_S]
  simp only [zpow_ofNat]
  field_simp [z.ne_zero]

def ckmrvPhiWeight : Fin 3 → ℤ := ![-2, 0, 2]

theorem ckmrvPhiBasis_S_weighted (z : UpperHalfPlane) (i : Fin 3) :
    ckmrvPhiBasis (ModularGroup.S • z) i * (z : ℂ) ^ (-ckmrvPhiWeight i) =
      -ckmrvPhiBasis z i := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp_rw [ckmrvPhiBasis, eisensteinTwo_S_explicit]
  simp only [UpperHalfPlane.modular_S_smul]
  fin_cases i <;> norm_num [ckmrvPhiWeight] <;>
    field_simp [hp, z.ne_zero] <;> ring_nf

theorem ckmrvTildePhiBasis_S_weighted (z : UpperHalfPlane) (i : Fin 3) :
    ckmrvTildePhiBasis (ModularGroup.S • z) i * (z : ℂ) ^ (-ckmrvPhiWeight i) =
      ckmrvPhiTranslationSlope z i := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp_rw [ckmrvTildePhiBasis, ckmrvPhiTranslationSlope, eisensteinTwo_S_explicit]
  simp only [UpperHalfPlane.modular_S_smul]
  fin_cases i <;> norm_num [ckmrvPhiWeight] <;>
    field_simp [hp, z.ne_zero] <;> ring_nf
  rw [Complex.I_sq]
  ring

theorem ckmrvEightPlusRow_S (z : UpperHalfPlane) (i : Fin 3) :
    ckmrvPhiBasis (ModularGroup.S • z) i *
      ckmrvModularFactor (ModularGroup.S • z) (![4, 3, 2] i) =
        -(z : ℂ) ^ 4 * (ckmrvPhiBasis z i * ckmrvModularFactor z (![4, 3, 2] i)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp_rw [ckmrvPhiBasis, ckmrvModularFactor_eq_products, eisensteinTwo_S_explicit,
    levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆, discriminant_S]
  simp only [UpperHalfPlane.modular_S_smul, zpow_ofNat]
  fin_cases i <;> dsimp <;>
    field_simp [hp, z.ne_zero] <;> ring_nf

theorem ckmrvLeechPlusRow_S (z : UpperHalfPlane) (i : Fin 3) :
    ckmrvPhiBasis (ModularGroup.S • z) i *
      ckmrvModularFactor (ModularGroup.S • z) (![8, 7, 6] i) =
        -(z : ℂ) ^ 12 * (ckmrvPhiBasis z i * ckmrvModularFactor z (![8, 7, 6] i)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp_rw [ckmrvPhiBasis, ckmrvModularFactor_eq_products, eisensteinTwo_S_explicit,
    levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆, discriminant_S]
  simp only [UpperHalfPlane.modular_S_smul, zpow_ofNat]
  fin_cases i <;> dsimp <;>
    field_simp [hp, z.ne_zero] <;> ring_nf

theorem ckmrvDiagonalCore_contract_left_covariance {𝕜 : Type*} [Field 𝕜]
    (a a' b l l' r : Fin 3 → 𝕜) (M : Matrix (Fin 3) (Fin 3) 𝕜) (c : 𝕜)
    (h : ∀ i, a' i * l' i = c * (a i * l i)) :
    ckmrvCoreContraction a' b (ckmrvDiagonalCore l' r M) =
      c * ckmrvCoreContraction a b (ckmrvDiagonalCore l r M) := by
  rw [ckmrvDiagonalCore_contract, ckmrvDiagonalCore_contract]
  simp_rw [ckmrvCoreContraction, h]
  simp only [Fin.sum_univ_three]
  ring

theorem ckmrvEightPlusKernel_S (τ z : UpperHalfPlane) :
    ckmrvEightPlusKernel (ModularGroup.S • τ) z =
      -(τ : ℂ) ^ 4 * ckmrvEightPlusKernel τ z := by
  unfold ckmrvEightPlusKernel ckmrvEightPlusCoefficientMatrix ckmrvModularCoreMatrix
  rw [kleinModularJ_S]
  rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
  rw [ckmrvDiagonalCore_contract_left_covariance
    (ckmrvPhiBasis τ) (ckmrvPhiBasis (ModularGroup.S • τ)) _
    (fun i => ckmrvModularFactor τ (![4, 3, 2] i)) _ _ _
    (-(τ : ℂ) ^ 4) (ckmrvEightPlusRow_S τ)]
  ring

theorem ckmrvLeechPlusKernel_S (τ z : UpperHalfPlane) :
    ckmrvLeechPlusKernel (ModularGroup.S • τ) z =
      -(τ : ℂ) ^ 12 * ckmrvLeechPlusKernel τ z := by
  unfold ckmrvLeechPlusKernel ckmrvLeechPlusCoefficientMatrix ckmrvModularCoreMatrix
  simp only [kleinModularJ_S]
  rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
  rw [ckmrvDiagonalCore_contract_left_covariance
    (ckmrvPhiBasis τ) (ckmrvPhiBasis (ModularGroup.S • τ)) _
    (fun i => ckmrvModularFactor τ (![8, 7, 6] i)) _ _ _
    (-(τ : ℂ) ^ 12) (ckmrvLeechPlusRow_S τ)]
  ring

theorem ckmrvEightPlusKernel_slash_S (z : UpperHalfPlane) :
    (fun τ => ckmrvEightPlusKernel τ z) ∣[(4 : ℤ)] ModularGroup.S =
      -(fun τ => ckmrvEightPlusKernel τ z) := by
  funext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, Pi.neg_apply,
    ckmrvEightPlusKernel_S, zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

theorem ckmrvLeechPlusKernel_slash_S (z : UpperHalfPlane) :
    (fun τ => ckmrvLeechPlusKernel τ z) ∣[(12 : ℤ)] ModularGroup.S =
      -(fun τ => ckmrvLeechPlusKernel τ z) := by
  funext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, Pi.neg_apply,
    ckmrvLeechPlusKernel_S, zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

end E8Leech
