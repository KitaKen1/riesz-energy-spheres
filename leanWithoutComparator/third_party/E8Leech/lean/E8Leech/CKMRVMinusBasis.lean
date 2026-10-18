import E8Leech.ThetaLogBranches
import E8Leech.CKMRVPlusInversion

/-!
# The CKMRV minus basis and the explicit minus kernels: left functional equations

CKMRV Proposition 4.5 gives `ψ₀ = 1`, `ψ₂ = ξ₂ L + (ξ₂|₂S) L_S`, `ψ₄ = ξ₄ L + (ξ₄|₄S) L_S`
with `ξ₂ = U + W`, `ξ₄ = U² + W² − 2V²`; Proposition 4.8 gives `ψ̃₀ = L`, `ψ̃₂ = W`,
`ψ̃₄ = U² − V²`. The explicit minus kernels (p.60) are `K₋ = ψᵀ Υ₋ ψ̃` with the existing actual
coefficient matrices `Υ₋`. Every claimed law is a known answer checked by finite algebra from
the theta laws (2.11), Jacobi's identity and the logarithm laws (2.17):

* `ψ_k(Sτ) = τ^k ψ_k(τ)` and `ψ(τ + 1) = ψ(τ) + πi ξ(τ)` with `ξ` translation invariant;
* `K₋(Sτ, z) = τ^{d/2} K₋(τ, z)`, i.e. left slash eigenvalue `+1`, and the left second
  difference vanishes: the left half of CKMRV Theorem 4.3(2) for `I₋ = (S − I)R + (T − I)²R`;
* `ψ̃` is annihilated by `T − 2I + T⁻¹ + 2S` (the first relation of Proposition 4.8).

Right-variable kernel relations, residues, cusp asymptotics, signs and the Fourier side are
not addressed here.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm Matrix BigOperators

/-! ## The weight two and four seeds `ξ` -/

/-- `ξ₂ = U + W`. -/
def ckmrvXiTwo (τ : ℍ) : ℂ := thetaU τ + thetaW τ

/-- `ξ₄ = U² + W² − 2V²`. -/
def ckmrvXiFour (τ : ℍ) : ℂ := thetaU τ ^ 2 + thetaW τ ^ 2 - 2 * thetaV τ ^ 2

/-- `ξ₂|₂S = −(U + V)`. -/
def ckmrvXiTwoS (τ : ℍ) : ℂ := -(thetaU τ + thetaV τ)

/-- `ξ₄|₄S = U² + V² − 2W²`. -/
def ckmrvXiFourS (τ : ℍ) : ℂ := thetaU τ ^ 2 + thetaV τ ^ 2 - 2 * thetaW τ ^ 2

theorem ckmrvXiTwo_S (τ : ℍ) :
    ckmrvXiTwo (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * ckmrvXiTwoS τ := by
  simp only [ckmrvXiTwo, ckmrvXiTwoS, thetaU_S, thetaW_S]
  ring

theorem ckmrvXiTwoS_S (τ : ℍ) :
    ckmrvXiTwoS (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * ckmrvXiTwo τ := by
  simp only [ckmrvXiTwo, ckmrvXiTwoS, thetaU_S, thetaV_S]
  ring

theorem ckmrvXiFour_S (τ : ℍ) :
    ckmrvXiFour (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * ckmrvXiFourS τ := by
  simp only [ckmrvXiFour, ckmrvXiFourS, thetaU_S, thetaV_S, thetaW_S]
  ring

theorem ckmrvXiFourS_S (τ : ℍ) :
    ckmrvXiFourS (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * ckmrvXiFour τ := by
  simp only [ckmrvXiFour, ckmrvXiFourS, thetaU_S, thetaV_S, thetaW_S]
  ring

theorem ckmrvXiTwo_T (τ : ℍ) : ckmrvXiTwo (ModularGroup.T • τ) = ckmrvXiTwo τ := by
  simp only [ckmrvXiTwo, thetaU_T, thetaW_T]
  ring

theorem ckmrvXiFour_T (τ : ℍ) : ckmrvXiFour (ModularGroup.T • τ) = ckmrvXiFour τ := by
  simp only [ckmrvXiFour, thetaU_T, thetaV_T, thetaW_T]
  ring

/-! ## The minus basis `ψ` (CKMRV Proposition 4.5) -/

/-- `ψ`, ordered by weights 0, 2, 4. -/
def ckmrvPsiBasis (τ : ℍ) : Fin 3 → ℂ :=
  ![1, ckmrvXiTwo τ * ckmrvL τ + ckmrvXiTwoS τ * ckmrvLS τ,
    ckmrvXiFour τ * ckmrvL τ + ckmrvXiFourS τ * ckmrvLS τ]

def ckmrvPsiWeight : Fin 3 → ℕ := ![0, 2, 4]

/-- `ψ|S = ψ` at weights 0, 2, 4. -/
theorem ckmrvPsiBasis_S (τ : ℍ) (i : Fin 3) :
    ckmrvPsiBasis (ModularGroup.S • τ) i = (τ : ℂ) ^ ckmrvPsiWeight i * ckmrvPsiBasis τ i := by
  simp only [ckmrvPsiBasis, ckmrvXiTwo_S, ckmrvXiTwoS_S, ckmrvXiFour_S, ckmrvXiFourS_S,
    ckmrvL_S, ckmrvLS_S]
  fin_cases i <;> simp [ckmrvPsiWeight] <;> ring

/-- `πi ξ`, ordered by weights 0, 2, 4. -/
def ckmrvPsiTranslationSlope (τ : ℍ) : Fin 3 → ℂ :=
  ![0, π * I * ckmrvXiTwo τ, π * I * ckmrvXiFour τ]

/-- `ψ(τ + 1) = ψ(τ) + πi ξ(τ)`. -/
theorem ckmrvPsiBasis_T (τ : ℍ) (i : Fin 3) :
    ckmrvPsiBasis (ModularGroup.T • τ) i =
      ckmrvPsiBasis τ i + ckmrvPsiTranslationSlope τ i := by
  simp only [ckmrvPsiBasis, ckmrvPsiTranslationSlope, ckmrvXiTwo, ckmrvXiFour, ckmrvXiTwoS,
    ckmrvXiFourS, thetaU_T, thetaV_T, thetaW_T, ckmrvL_T, ckmrvLS_T]
  fin_cases i <;> simp <;> ring

theorem ckmrvPsiTranslationSlope_T (τ : ℍ) :
    ckmrvPsiTranslationSlope (ModularGroup.T • τ) = ckmrvPsiTranslationSlope τ := by
  simp only [ckmrvPsiTranslationSlope, ckmrvXiTwo_T, ckmrvXiFour_T]

theorem mdifferentiable_ckmrvPsiBasis (i : Fin 3) :
    MDiff (fun τ : ℍ => ckmrvPsiBasis τ i) := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  have hW := mdifferentiable_thetaW
  have hL := mdifferentiable_ckmrvL
  have hLS := mdifferentiable_ckmrvLS
  fin_cases i
  · exact mdifferentiable_const
  · exact ((hU.add hW).mul hL).add ((hU.add hV).neg.mul hLS)
  · have h : (fun τ : ℍ => ckmrvPsiBasis τ 2) =
        (thetaU * thetaU + thetaW * thetaW - (fun _ => (2 : ℂ)) * (thetaV * thetaV)) * ckmrvL +
          (thetaU * thetaU + thetaV * thetaV - (fun _ => (2 : ℂ)) * (thetaW * thetaW)) * ckmrvLS := by
      funext τ
      simp only [ckmrvPsiBasis, ckmrvXiFour, ckmrvXiFourS, Pi.add_apply, Pi.sub_apply,
        Pi.mul_apply]
      simp
      ring
    change MDiff (fun τ : ℍ => ckmrvPsiBasis τ 2)
    rw [h]
    exact ((((hU.mul hU).add (hW.mul hW)).sub (mdifferentiable_const.mul (hV.mul hV))).mul
      hL).add ((((hU.mul hU).add (hV.mul hV)).sub
        (mdifferentiable_const.mul (hW.mul hW))).mul hLS)

/-! ## The tilde minus basis `ψ̃` (CKMRV Proposition 4.8) -/

/-- `ψ̃ = (L, W, U² − V²)`, ordered by weights 0, 2, 4. -/
def ckmrvTildePsiBasis (z : ℍ) : Fin 3 → ℂ :=
  ![ckmrvL z, thetaW z, thetaU z ^ 2 - thetaV z ^ 2]

theorem thetaU_T_inv (z : ℍ) : thetaU (ModularGroup.T⁻¹ • z) = thetaW z := by
  have h := thetaW_T (ModularGroup.T⁻¹ • z)
  rw [smul_inv_smul] at h
  exact h.symm

theorem thetaW_T_inv (z : ℍ) : thetaW (ModularGroup.T⁻¹ • z) = thetaU z := by
  have h := thetaU_T (ModularGroup.T⁻¹ • z)
  rw [smul_inv_smul] at h
  exact h.symm

theorem thetaV_T_inv (z : ℍ) : thetaV (ModularGroup.T⁻¹ • z) = -thetaV z := by
  have h := thetaV_T (ModularGroup.T⁻¹ • z)
  rw [smul_inv_smul] at h
  rw [h, neg_neg]

theorem ckmrvLS_T_inv (z : ℍ) : ckmrvLS (ModularGroup.T⁻¹ • z) = -ckmrvLS z := by
  have h := ckmrvLS_T (ModularGroup.T⁻¹ • z)
  rw [smul_inv_smul] at h
  rw [h, neg_neg]

theorem ckmrvL_T_inv (z : ℍ) :
    ckmrvL (ModularGroup.T⁻¹ • z) = ckmrvL z - ckmrvLS z - π * I := by
  have h := ckmrvL_T (ModularGroup.T⁻¹ • z)
  rw [smul_inv_smul, ckmrvLS_T_inv] at h
  linear_combination -h

/-- CKMRV Proposition 4.8, first relation: `ψ̃|(T − 2I + T⁻¹ + 2S) = 0` at weights 0, 2, 4. -/
theorem ckmrvTildePsiBasis_relation (z : ℍ) (i : Fin 3) :
    ckmrvTildePsiBasis (ModularGroup.T • z) i - 2 * ckmrvTildePsiBasis z i +
      ckmrvTildePsiBasis (ModularGroup.T⁻¹ • z) i +
        2 * ((z : ℂ) ^ ckmrvPsiWeight i)⁻¹ * ckmrvTildePsiBasis (ModularGroup.S • z) i = 0 := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  fin_cases i
  · simp only [ckmrvTildePsiBasis, ckmrvPsiWeight, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, pow_zero, inv_one, mul_one, ckmrvL_T, ckmrvL_T_inv, ckmrvL_S]
    ring
  · simp only [ckmrvTildePsiBasis, ckmrvPsiWeight, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero, thetaW_T, thetaW_T_inv, thetaW_S]
    rw [thetaU_eq_add]
    field_simp
    ring
  · simp only [ckmrvTildePsiBasis, ckmrvPsiWeight, Fin.reduceFinMk,
      Matrix.cons_val, thetaU_T, thetaV_T, thetaU_T_inv, thetaV_T_inv, thetaU_S, thetaV_S]
    field_simp
    ring

/-! ## The explicit minus kernels -/

def ckmrvEightMinusKernel (τ z : ℍ) : ℂ :=
  ckmrvCoreContraction (ckmrvPsiBasis τ) (ckmrvTildePsiBasis z)
    (ckmrvEightMinusCoefficientMatrix τ z)

def ckmrvLeechMinusKernel (τ z : ℍ) : ℂ :=
  ckmrvCoreContraction (ckmrvPsiBasis τ) (ckmrvTildePsiBasis z)
    (ckmrvLeechMinusCoefficientMatrix τ z)

/-- Row weights: `ψ` (0, 2, 4) times `E₄, E₁₄/Δ, 1` (4, 2, 0). -/
theorem ckmrvEightMinusRow_S (τ : ℍ) (i : Fin 3) :
    ckmrvPsiBasis (ModularGroup.S • τ) i *
      ckmrvModularFactor (ModularGroup.S • τ) (![3, 2, 1] i) =
        (τ : ℂ) ^ 4 * (ckmrvPsiBasis τ i * ckmrvModularFactor τ (![3, 2, 1] i)) := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [ckmrvPsiBasis_S]
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  simp only [zpow_ofNat]
  fin_cases i <;> dsimp [ckmrvPsiWeight] <;> field_simp [τ.ne_zero, hΔ]

/-- Row weights: `ψ` (0, 2, 4) times `Δ, E₁₀, E₈` (12, 10, 8). -/
theorem ckmrvLeechMinusRow_S (τ : ℍ) (i : Fin 3) :
    ckmrvPsiBasis (ModularGroup.S • τ) i *
      ckmrvModularFactor (ModularGroup.S • τ) (![7, 6, 5] i) =
        (τ : ℂ) ^ 12 * (ckmrvPsiBasis τ i * ckmrvModularFactor τ (![7, 6, 5] i)) := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [ckmrvPsiBasis_S]
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  simp only [zpow_ofNat]
  fin_cases i <;> dsimp [ckmrvPsiWeight] <;> field_simp [τ.ne_zero, hΔ]

/-- Left `S` eigenvalue `+1` at weight 4. -/
theorem ckmrvEightMinusKernel_S (τ z : ℍ) :
    ckmrvEightMinusKernel (ModularGroup.S • τ) z = (τ : ℂ) ^ 4 * ckmrvEightMinusKernel τ z := by
  unfold ckmrvEightMinusKernel ckmrvEightMinusCoefficientMatrix ckmrvModularCoreMatrix
  rw [kleinModularJ_S]
  rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
  rw [ckmrvDiagonalCore_contract_left_covariance
    (ckmrvPsiBasis τ) (ckmrvPsiBasis (ModularGroup.S • τ)) _
    (fun i => ckmrvModularFactor τ (![3, 2, 1] i)) _ _ _
    ((τ : ℂ) ^ 4) (ckmrvEightMinusRow_S τ)]
  ring

/-- Left `S` eigenvalue `+1` at weight 12. -/
theorem ckmrvLeechMinusKernel_S (τ z : ℍ) :
    ckmrvLeechMinusKernel (ModularGroup.S • τ) z =
      (τ : ℂ) ^ 12 * ckmrvLeechMinusKernel τ z := by
  unfold ckmrvLeechMinusKernel ckmrvLeechMinusCoefficientMatrix ckmrvModularCoreMatrix
  simp only [kleinModularJ_S]
  rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
  rw [ckmrvDiagonalCore_contract_left_covariance
    (ckmrvPsiBasis τ) (ckmrvPsiBasis (ModularGroup.S • τ)) _
    (fun i => ckmrvModularFactor τ (![7, 6, 5] i)) _ _ _
    ((τ : ℂ) ^ 12) (ckmrvLeechMinusRow_S τ)]
  ring

theorem ckmrvEightMinusKernel_slash_S (z : ℍ) :
    (fun τ => ckmrvEightMinusKernel τ z) ∣[(4 : ℤ)] ModularGroup.S =
      fun τ => ckmrvEightMinusKernel τ z := by
  funext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, ckmrvEightMinusKernel_S,
    zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

theorem ckmrvLeechMinusKernel_slash_S (z : ℍ) :
    (fun τ => ckmrvLeechMinusKernel τ z) ∣[(12 : ℤ)] ModularGroup.S =
      fun τ => ckmrvLeechMinusKernel τ z := by
  funext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, ckmrvLeechMinusKernel_S,
    zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

/-! ## Translation in the left variable -/

theorem T_smul_eq_ckmrvTranslate_one (τ : ℍ) : ModularGroup.T • τ = ckmrvTranslate 1 τ := by
  simpa only [zpow_one] using (ckmrvTranslate_eq_T_zpow 1 τ).symm

theorem ckmrvEightMinusCoefficientMatrix_T (τ z : ℍ) :
    ckmrvEightMinusCoefficientMatrix (ModularGroup.T • τ) z =
      ckmrvEightMinusCoefficientMatrix τ z := by
  rw [T_smul_eq_ckmrvTranslate_one]
  simp only [ckmrvEightMinusCoefficientMatrix, ckmrvModularCoreMatrix, kleinModularJ_translate,
    ckmrvModularFactor_translate]

theorem ckmrvLeechMinusCoefficientMatrix_T (τ z : ℍ) :
    ckmrvLeechMinusCoefficientMatrix (ModularGroup.T • τ) z =
      ckmrvLeechMinusCoefficientMatrix τ z := by
  rw [T_smul_eq_ckmrvTranslate_one]
  simp only [ckmrvLeechMinusCoefficientMatrix, ckmrvModularCoreMatrix, kleinModularJ_translate,
    ckmrvModularFactor_translate]

def ckmrvEightMinusTranslationSlope (τ z : ℍ) : ℂ :=
  ckmrvCoreContraction (ckmrvPsiTranslationSlope τ) (ckmrvTildePsiBasis z)
    (ckmrvEightMinusCoefficientMatrix τ z)

def ckmrvLeechMinusTranslationSlope (τ z : ℍ) : ℂ :=
  ckmrvCoreContraction (ckmrvPsiTranslationSlope τ) (ckmrvTildePsiBasis z)
    (ckmrvLeechMinusCoefficientMatrix τ z)

private theorem ckmrvPsiBasis_T_fun (τ : ℍ) :
    ckmrvPsiBasis (ModularGroup.T • τ) =
      fun i => ckmrvPsiBasis τ i + 1 * ckmrvPsiTranslationSlope τ i := by
  funext i
  rw [ckmrvPsiBasis_T, one_mul]

theorem ckmrvEightMinusKernel_T (τ z : ℍ) :
    ckmrvEightMinusKernel (ModularGroup.T • τ) z =
      ckmrvEightMinusKernel τ z + ckmrvEightMinusTranslationSlope τ z := by
  unfold ckmrvEightMinusKernel ckmrvEightMinusTranslationSlope
  rw [ckmrvEightMinusCoefficientMatrix_T, ckmrvPsiBasis_T_fun, ckmrvCoreContraction_affine_left,
    one_mul]

theorem ckmrvLeechMinusKernel_T (τ z : ℍ) :
    ckmrvLeechMinusKernel (ModularGroup.T • τ) z =
      ckmrvLeechMinusKernel τ z + ckmrvLeechMinusTranslationSlope τ z := by
  unfold ckmrvLeechMinusKernel ckmrvLeechMinusTranslationSlope
  rw [ckmrvLeechMinusCoefficientMatrix_T, ckmrvPsiBasis_T_fun, ckmrvCoreContraction_affine_left,
    one_mul]

theorem ckmrvEightMinusTranslationSlope_T (τ z : ℍ) :
    ckmrvEightMinusTranslationSlope (ModularGroup.T • τ) z =
      ckmrvEightMinusTranslationSlope τ z := by
  unfold ckmrvEightMinusTranslationSlope
  rw [ckmrvEightMinusCoefficientMatrix_T, ckmrvPsiTranslationSlope_T]

theorem ckmrvLeechMinusTranslationSlope_T (τ z : ℍ) :
    ckmrvLeechMinusTranslationSlope (ModularGroup.T • τ) z =
      ckmrvLeechMinusTranslationSlope τ z := by
  unfold ckmrvLeechMinusTranslationSlope
  rw [ckmrvLeechMinusCoefficientMatrix_T, ckmrvPsiTranslationSlope_T]

theorem ckmrvEightMinusKernel_second_difference (τ z : ℍ) :
    ckmrvEightMinusKernel (ModularGroup.T • ModularGroup.T • τ) z -
      2 * ckmrvEightMinusKernel (ModularGroup.T • τ) z + ckmrvEightMinusKernel τ z = 0 := by
  rw [ckmrvEightMinusKernel_T (ModularGroup.T • τ), ckmrvEightMinusKernel_T τ,
    ckmrvEightMinusTranslationSlope_T]
  ring

theorem ckmrvLeechMinusKernel_second_difference (τ z : ℍ) :
    ckmrvLeechMinusKernel (ModularGroup.T • ModularGroup.T • τ) z -
      2 * ckmrvLeechMinusKernel (ModularGroup.T • τ) z + ckmrvLeechMinusKernel τ z = 0 := by
  rw [ckmrvLeechMinusKernel_T (ModularGroup.T • τ), ckmrvLeechMinusKernel_T τ,
    ckmrvLeechMinusTranslationSlope_T]
  ring

/-- `K₋|τ₄ (T − I)² = 0`. -/
theorem ckmrvEightMinusKernel_slash_T_second_difference (z : ℍ) :
    (((fun τ => ckmrvEightMinusKernel τ z) ∣[(4 : ℤ)] ModularGroup.T) ∣[(4 : ℤ)]
      ModularGroup.T) - (2 : ℂ) • ((fun τ => ckmrvEightMinusKernel τ z) ∣[(4 : ℤ)]
        ModularGroup.T) + (fun τ => ckmrvEightMinusKernel τ z) = 0 := by
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrv_slash_T_apply, ← T_smul_eq_ckmrvTranslate_one]
  exact ckmrvEightMinusKernel_second_difference τ z

/-- `K₋|τ₁₂ (T − I)² = 0`. -/
theorem ckmrvLeechMinusKernel_slash_T_second_difference (z : ℍ) :
    (((fun τ => ckmrvLeechMinusKernel τ z) ∣[(12 : ℤ)] ModularGroup.T) ∣[(12 : ℤ)]
      ModularGroup.T) - (2 : ℂ) • ((fun τ => ckmrvLeechMinusKernel τ z) ∣[(12 : ℤ)]
        ModularGroup.T) + (fun τ => ckmrvLeechMinusKernel τ z) = 0 := by
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrv_slash_T_apply, ← T_smul_eq_ckmrvTranslate_one]
  exact ckmrvLeechMinusKernel_second_difference τ z

end E8Leech
