import E8Leech.CKMRVRightRelations
import E8Leech.CKMRVActualDerivatives
import E8Leech.EisensteinCuspDerivative

/-!
# Residues of the explicit CKMRV kernels (Theorem 4.3(3) on `R/I±`)

CKMRV Theorem 4.3(3) asks `Res_{τ=z} (K±|^τ_{d/2} r) = −φ±(r)/(2π)` with `φ±(I) = 0`,
`φ±(T) = 1`, `φ±(TS) = 0` on the basis `I, T, TS` of `R/I±`. At points with
`E₄(z) E₆(z) ≠ 0` the residue of the coefficient matrices is already the published matrix;
here the contractions are evaluated.

Known answers first:
* CKMRV (2.12) `E₄ = (U² + V² + W²)/2` and `E₆ = (U + V)(U + W)(W − V)/2` by level-one cusp
  forms of weights 4 and 6, like Jacobi's identity;
* with `A = E₄² W − E₆ (U² − V²)` and `B = −E₆ W + E₄ (U² − V²)` the two polynomial identities
  `ξ₂ A + ξ₄ B = 3456 Δ` and `(ξ₂|S) A + (ξ₄|S) B = 0` hold; both were found by expanding in
  `V, W` with `U = V + W` and are checked by `ring` here. They make the coefficients of
  `L` and `L_S` in `ψᵀ R₋ ψ̃` vanish and give the `T` residue `−1/(2π)`;
* on the plus side the `TS` residue is `(π/72)(2φ̃₀φ̃₂ − 2φ̃₁²) = 0`.

Elliptic points (`E₄(z) E₆(z) = 0`), cusp asymptotics and growth are not addressed here.
-/

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm Matrix BigOperators

/-! ## CKMRV (2.12): `E₄` and `E₆` from theta functions -/

private theorem tendsto_E4_atImInfty :
    Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h4 : (qExpansion 1 ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide)
  simpa only [h4] using levelOne_tendsto_qExpansion_constant ModularForm.E₄

private theorem tendsto_E6_atImInfty :
    Tendsto (ModularForm.E₆ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h6 : (qExpansion 1 ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide)
  simpa only [h6] using levelOne_tendsto_qExpansion_constant ModularForm.E₆

private theorem E4_T (τ : ℍ) : ModularForm.E₄ (ModularGroup.T • τ) = ModularForm.E₄ τ := by
  rw [T_smul_eq_ckmrvTranslate_one]
  exact levelOne_translate ModularForm.E₄ 1 τ

private theorem E6_T (τ : ℍ) : ModularForm.E₆ (ModularGroup.T • τ) = ModularForm.E₆ τ := by
  rw [T_smul_eq_ckmrvTranslate_one]
  exact levelOne_translate ModularForm.E₆ 1 τ

/-- The weight four defect `E₄ − (U² + V² + W²)/2`. -/
def eisensteinFourThetaDefect (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ - (1 / 2 : ℂ) * (thetaU τ * thetaU τ + thetaV τ * thetaV τ + thetaW τ * thetaW τ)

/-- The weight six defect `E₆ − (U + V)(U + W)(W − V)/2`. -/
def eisensteinSixThetaDefect (τ : ℍ) : ℂ :=
  ModularForm.E₆ τ - (1 / 2 : ℂ) * ((thetaU τ + thetaV τ) * (thetaU τ + thetaW τ) *
    (thetaW τ - thetaV τ))

theorem eisensteinFourThetaDefect_eq_zero (τ : ℍ) : eisensteinFourThetaDefect τ = 0 := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  have hW := mdifferentiable_thetaW
  have hf : eisensteinFourThetaDefect = ⇑ModularForm.E₄ -
      (fun _ => (1 / 2 : ℂ)) * (thetaU * thetaU + thetaV * thetaV + thetaW * thetaW) := by
    funext σ
    simp [eisensteinFourThetaDefect]
  let F : CuspForm 𝒮ℒ 4 := levelOneCuspFormOf 4 eisensteinFourThetaDefect
    (fun σ => by simp only [eisensteinFourThetaDefect, E4_T, thetaU_T, thetaV_T, thetaW_T]; ring)
    (fun σ => by
      simp only [eisensteinFourThetaDefect, levelOne_S ModularForm.E₄, thetaU_S, thetaV_S,
        thetaW_S, zpow_ofNat]
      ring)
    (by
      rw [hf]
      exact (ModularFormClass.holo ModularForm.E₄).sub (mdifferentiable_const.mul
        (((hU.mul hU).add (hV.mul hV)).add (hW.mul hW))))
    (by
      have h := tendsto_E4_atImInfty.sub (tendsto_const_nhds (x := (1 / 2 : ℂ)) |>.mul
        (((tendsto_thetaU_atImInfty.mul tendsto_thetaU_atImInfty).add
          (tendsto_thetaV_atImInfty.mul tendsto_thetaV_atImInfty)).add
            (tendsto_thetaW_atImInfty.mul tendsto_thetaW_atImInfty)))
      rw [show (1 : ℂ) - 1 / 2 * (1 * 1 + 0 * 0 + 1 * 1) = 0 by norm_num] at h
      exact h)
  have hzero : F = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) _
  have h := congrArg (fun G : CuspForm 𝒮ℒ 4 => G τ) hzero
  simpa [F] using h

theorem eisensteinSixThetaDefect_eq_zero (τ : ℍ) : eisensteinSixThetaDefect τ = 0 := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  have hW := mdifferentiable_thetaW
  have hf : eisensteinSixThetaDefect = ⇑ModularForm.E₆ -
      (fun _ => (1 / 2 : ℂ)) * ((thetaU + thetaV) * (thetaU + thetaW) * (thetaW - thetaV)) := by
    funext σ
    simp [eisensteinSixThetaDefect]
  let F : CuspForm 𝒮ℒ 6 := levelOneCuspFormOf 6 eisensteinSixThetaDefect
    (fun σ => by simp only [eisensteinSixThetaDefect, E6_T, thetaU_T, thetaV_T, thetaW_T]; ring)
    (fun σ => by
      simp only [eisensteinSixThetaDefect, levelOne_S ModularForm.E₆, thetaU_S, thetaV_S,
        thetaW_S, zpow_ofNat]
      ring)
    (by
      rw [hf]
      exact (ModularFormClass.holo ModularForm.E₆).sub (mdifferentiable_const.mul
        (((hU.add hV).mul (hU.add hW)).mul (hW.sub hV))))
    (by
      have h := tendsto_E6_atImInfty.sub (tendsto_const_nhds (x := (1 / 2 : ℂ)) |>.mul
        (((tendsto_thetaU_atImInfty.add tendsto_thetaV_atImInfty).mul
          (tendsto_thetaU_atImInfty.add tendsto_thetaW_atImInfty)).mul
            (tendsto_thetaW_atImInfty.sub tendsto_thetaV_atImInfty)))
      rw [show (1 : ℂ) - 1 / 2 * ((1 + 0) * (1 + 1) * (1 - 0)) = 0 by norm_num] at h
      exact h)
  have hzero : F = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) _
  have h := congrArg (fun G : CuspForm 𝒮ℒ 6 => G τ) hzero
  simpa [F] using h

/-- CKMRV (2.12): `E₄ = (U² + V² + W²)/2`. -/
theorem eisensteinFour_eq_theta (τ : ℍ) :
    ModularForm.E₄ τ = (thetaU τ ^ 2 + thetaV τ ^ 2 + thetaW τ ^ 2) / 2 := by
  have h := eisensteinFourThetaDefect_eq_zero τ
  unfold eisensteinFourThetaDefect at h
  linear_combination h

/-- CKMRV (2.12): `E₆ = (U + V)(U + W)(W − V)/2`. -/
theorem eisensteinSix_eq_theta (τ : ℍ) :
    ModularForm.E₆ τ = (thetaU τ + thetaV τ) * (thetaU τ + thetaW τ) * (thetaW τ - thetaV τ) / 2 := by
  have h := eisensteinSixThetaDefect_eq_zero τ
  unfold eisensteinSixThetaDefect at h
  linear_combination h

/-! ## The two residue identities -/

/-- `ξ₂ A + ξ₄ B = 3456 Δ`. -/
theorem ckmrvMinusResidue_identity_one (z : ℍ) :
    ckmrvXiTwo z * (ModularForm.E₄ z ^ 2 * thetaW z -
        ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2)) +
      ckmrvXiFour z * (-ModularForm.E₆ z * thetaW z +
        ModularForm.E₄ z * (thetaU z ^ 2 - thetaV z ^ 2)) =
        3456 * ModularForm.discriminant z := by
  have hΔ := thetaProductSq_eq_discriminant z
  rw [eisensteinFour_eq_theta, eisensteinSix_eq_theta]
  simp only [ckmrvXiTwo, ckmrvXiFour, thetaProductSq] at hΔ ⊢
  simp only [thetaU_eq_add] at hΔ ⊢
  linear_combination (27 / 2 : ℂ) * hΔ

/-- `(ξ₂|S) A + (ξ₄|S) B = 0`. -/
theorem ckmrvMinusResidue_identity_two (z : ℍ) :
    ckmrvXiTwoS z * (ModularForm.E₄ z ^ 2 * thetaW z -
        ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2)) +
      ckmrvXiFourS z * (-ModularForm.E₆ z * thetaW z +
        ModularForm.E₄ z * (thetaU z ^ 2 - thetaV z ^ 2)) = 0 := by
  rw [eisensteinFour_eq_theta, eisensteinSix_eq_theta]
  simp only [ckmrvXiTwoS, ckmrvXiFourS, thetaU_eq_add]
  ring

/-- `πi ξ|S`, the slope seen after the inversion. -/
def ckmrvPsiSlopeS (τ : ℍ) : Fin 3 → ℂ :=
  ![0, π * I * ckmrvXiTwoS τ, π * I * ckmrvXiFourS τ]

private theorem contract_minus_residue (a : Fin 3 → ℂ) (z : ℍ) :
    ckmrvCoreContraction a (ckmrvTildePsiBasis z) (ckmrvMinusResidueMatrix z) =
      a 0 * (-3456 * ModularForm.discriminant z * ckmrvL z) +
        a 1 * (ModularForm.E₄ z ^ 2 * thetaW z -
          ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2)) +
        a 2 * (-ModularForm.E₆ z * thetaW z +
          ModularForm.E₄ z * (thetaU z ^ 2 - thetaV z ^ 2)) := by
  simp [ckmrvCoreContraction, Fin.sum_univ_three, ckmrvTildePsiBasis, ckmrvMinusResidueMatrix]
  ring

theorem ckmrvMinusResidue_contract_self (z : ℍ) :
    ckmrvCoreContraction (ckmrvPsiBasis z) (ckmrvTildePsiBasis z)
      (ckmrvMinusResidueMatrix z) = 0 := by
  rw [contract_minus_residue]
  simp only [ckmrvPsiBasis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination ckmrvL z * ckmrvMinusResidue_identity_one z +
    ckmrvLS z * ckmrvMinusResidue_identity_two z

theorem ckmrvMinusResidue_contract_slope (z : ℍ) :
    ckmrvCoreContraction (ckmrvPsiTranslationSlope z) (ckmrvTildePsiBasis z)
      (ckmrvMinusResidueMatrix z) = π * I * (3456 * ModularForm.discriminant z) := by
  rw [contract_minus_residue]
  simp only [ckmrvPsiTranslationSlope, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (π * I) * ckmrvMinusResidue_identity_one z

theorem ckmrvMinusResidue_contract_slopeS (z : ℍ) :
    ckmrvCoreContraction (ckmrvPsiSlopeS z) (ckmrvTildePsiBasis z)
      (ckmrvMinusResidueMatrix z) = 0 := by
  rw [contract_minus_residue]
  simp only [ckmrvPsiSlopeS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (π * I) * ckmrvMinusResidue_identity_two z

private theorem minus_residue_scale (z : ℍ) :
    Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z) *
      (π * I * (3456 * ModularForm.discriminant z)) = -1 / (2 * (π : ℂ)) := by
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΔ := ModularForm.discriminant_ne_zero z
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Slopes after the inversion -/

theorem ckmrvPsiTranslationSlope_S (τ : ℍ) (i : Fin 3) :
    ckmrvPsiTranslationSlope (ModularGroup.S • τ) i =
      (τ : ℂ) ^ ckmrvPsiWeight i * ckmrvPsiSlopeS τ i := by
  simp only [ckmrvPsiTranslationSlope, ckmrvPsiSlopeS, ckmrvXiTwo_S, ckmrvXiFour_S]
  fin_cases i <;> simp [ckmrvPsiWeight] <;> ring

theorem ckmrvEightMinusSlopeRow_S (τ : ℍ) (i : Fin 3) :
    ckmrvPsiTranslationSlope (ModularGroup.S • τ) i *
      ckmrvModularFactor (ModularGroup.S • τ) (![3, 2, 1] i) =
        (τ : ℂ) ^ 4 * (ckmrvPsiSlopeS τ i * ckmrvModularFactor τ (![3, 2, 1] i)) := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [ckmrvPsiTranslationSlope_S]
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  simp only [zpow_ofNat]
  fin_cases i <;> dsimp [ckmrvPsiWeight] <;> field_simp [τ.ne_zero, hΔ]

theorem ckmrvLeechMinusSlopeRow_S (τ : ℍ) (i : Fin 3) :
    ckmrvPsiTranslationSlope (ModularGroup.S • τ) i *
      ckmrvModularFactor (ModularGroup.S • τ) (![7, 6, 5] i) =
        (τ : ℂ) ^ 12 * (ckmrvPsiSlopeS τ i * ckmrvModularFactor τ (![7, 6, 5] i)) := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [ckmrvPsiTranslationSlope_S]
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  simp only [zpow_ofNat]
  fin_cases i <;> dsimp [ckmrvPsiWeight] <;> field_simp [τ.ne_zero, hΔ]

theorem ckmrvEightMinusTranslationSlope_S (τ z : ℍ) :
    ckmrvEightMinusTranslationSlope (ModularGroup.S • τ) z = (τ : ℂ) ^ 4 *
      ckmrvCoreContraction (ckmrvPsiSlopeS τ) (ckmrvTildePsiBasis z)
        (ckmrvEightMinusCoefficientMatrix τ z) := by
  unfold ckmrvEightMinusTranslationSlope ckmrvEightMinusCoefficientMatrix ckmrvModularCoreMatrix
  rw [kleinModularJ_S]
  rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
  rw [ckmrvDiagonalCore_contract_left_covariance
    (ckmrvPsiSlopeS τ) (ckmrvPsiTranslationSlope (ModularGroup.S • τ)) _
    (fun i => ckmrvModularFactor τ (![3, 2, 1] i)) _ _ _
    ((τ : ℂ) ^ 4) (ckmrvEightMinusSlopeRow_S τ)]
  ring

theorem ckmrvLeechMinusTranslationSlope_S (τ z : ℍ) :
    ckmrvLeechMinusTranslationSlope (ModularGroup.S • τ) z = (τ : ℂ) ^ 12 *
      ckmrvCoreContraction (ckmrvPsiSlopeS τ) (ckmrvTildePsiBasis z)
        (ckmrvLeechMinusCoefficientMatrix τ z) := by
  unfold ckmrvLeechMinusTranslationSlope ckmrvLeechMinusCoefficientMatrix ckmrvModularCoreMatrix
  simp only [kleinModularJ_S]
  rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
  rw [ckmrvDiagonalCore_contract_left_covariance
    (ckmrvPsiSlopeS τ) (ckmrvPsiTranslationSlope (ModularGroup.S • τ)) _
    (fun i => ckmrvModularFactor τ (![7, 6, 5] i)) _ _ _
    ((τ : ℂ) ^ 12) (ckmrvLeechMinusSlopeRow_S τ)]
  ring

/-- `(K₋|₄ TS)(τ) = K₋(τ) + contraction (πi ξ|S)`. -/
theorem ckmrvEightMinusKernel_slash_TS (z τ : ℍ) :
    ((fun σ => ckmrvEightMinusKernel σ z) ∣[(4 : ℤ)]
      (ModularGroup.T * ModularGroup.S)) τ =
      ckmrvEightMinusKernel τ z + ckmrvCoreContraction (ckmrvPsiSlopeS τ)
        (ckmrvTildePsiBasis z) (ckmrvEightMinusCoefficientMatrix τ z) := by
  rw [SlashAction.slash_mul, ckmrv_slash_S_apply, ckmrv_slash_T_apply_smul,
    ckmrvEightMinusKernel_T, ckmrvEightMinusKernel_S, ckmrvEightMinusTranslationSlope_S]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

theorem ckmrvLeechMinusKernel_slash_TS (z τ : ℍ) :
    ((fun σ => ckmrvLeechMinusKernel σ z) ∣[(12 : ℤ)]
      (ModularGroup.T * ModularGroup.S)) τ =
      ckmrvLeechMinusKernel τ z + ckmrvCoreContraction (ckmrvPsiSlopeS τ)
        (ckmrvTildePsiBasis z) (ckmrvLeechMinusCoefficientMatrix τ z) := by
  rw [SlashAction.slash_mul, ckmrv_slash_S_apply, ckmrv_slash_T_apply_smul,
    ckmrvLeechMinusKernel_T, ckmrvLeechMinusKernel_S, ckmrvLeechMinusTranslationSlope_S]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

/-! ## Minus residues at `I`, `T`, `TS` -/

private theorem tendsto_comp_ofComplex {f : ℍ → ℂ} (hf : MDiff f) (z : ℍ) :
    Tendsto (fun w : ℂ => f (ofComplex w)) (𝓝[≠] (z : ℂ)) (𝓝 (f z)) := by
  simpa only [ofComplex_apply] using
    (analyticAt_of_upperHalfPlane_mdifferentiable hf z).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds

theorem mdifferentiable_ckmrvPsiTranslationSlope (i : Fin 3) :
    MDiff (fun τ : ℍ => ckmrvPsiTranslationSlope τ i) := by
  fin_cases i
  · exact mdifferentiable_const
  · exact mdifferentiable_const.mul (mdifferentiable_thetaU.add mdifferentiable_thetaW)
  · have h : (fun τ : ℍ => ckmrvPsiTranslationSlope τ 2) = (fun _ => (π * I : ℂ)) *
        (thetaU * thetaU + thetaW * thetaW - (fun _ => (2 : ℂ)) * (thetaV * thetaV)) := by
      funext τ
      simp [ckmrvPsiTranslationSlope, ckmrvXiFour]
      ring
    change MDiff (fun τ : ℍ => ckmrvPsiTranslationSlope τ 2)
    rw [h]
    exact mdifferentiable_const.mul (((mdifferentiable_thetaU.mul mdifferentiable_thetaU).add
      (mdifferentiable_thetaW.mul mdifferentiable_thetaW)).sub
        (mdifferentiable_const.mul (mdifferentiable_thetaV.mul mdifferentiable_thetaV)))

theorem mdifferentiable_ckmrvPsiSlopeS (i : Fin 3) :
    MDiff (fun τ : ℍ => ckmrvPsiSlopeS τ i) := by
  fin_cases i
  · exact mdifferentiable_const
  · have h : (fun τ : ℍ => ckmrvPsiSlopeS τ 1) = (fun _ => (π * I : ℂ)) *
        -(thetaU + thetaV) := by
      funext τ
      simp [ckmrvPsiSlopeS, ckmrvXiTwoS]
    change MDiff (fun τ : ℍ => ckmrvPsiSlopeS τ 1)
    rw [h]
    exact mdifferentiable_const.mul (mdifferentiable_thetaU.add mdifferentiable_thetaV).neg
  · have h : (fun τ : ℍ => ckmrvPsiSlopeS τ 2) = (fun _ => (π * I : ℂ)) *
        (thetaU * thetaU + thetaV * thetaV - (fun _ => (2 : ℂ)) * (thetaW * thetaW)) := by
      funext τ
      simp [ckmrvPsiSlopeS, ckmrvXiFourS]
      ring
    change MDiff (fun τ : ℍ => ckmrvPsiSlopeS τ 2)
    rw [h]
    exact mdifferentiable_const.mul (((mdifferentiable_thetaU.mul mdifferentiable_thetaU).add
      (mdifferentiable_thetaV.mul mdifferentiable_thetaV)).sub
        (mdifferentiable_const.mul (mdifferentiable_thetaW.mul mdifferentiable_thetaW)))

/-- `Res_{τ=z} K₋⁽⁸⁾ = 0`. -/
theorem tendsto_ckmrvEightMinusKernel_residue (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) * ckmrvEightMinusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  have h := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPsiBasis (ofComplex w)) (ckmrvTildePsiBasis z) (ckmrvPsiBasis z)
    (fun w => ckmrvEightMinusCoefficientMatrix (ofComplex w) z)
    ((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) •
      ckmrvMinusResidueMatrix z) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvPsiBasis i) z)
    (tendsto_ckmrvEightMinusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvMinusResidue_contract_self, mul_zero] at h
  simpa only [ckmrvEightMinusKernel] using h

theorem tendsto_ckmrvLeechMinusKernel_residue (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) * ckmrvLeechMinusKernel (ofComplex w) z)
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  have h := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPsiBasis (ofComplex w)) (ckmrvTildePsiBasis z) (ckmrvPsiBasis z)
    (fun w => ckmrvLeechMinusCoefficientMatrix (ofComplex w) z)
    ((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) •
      ckmrvMinusResidueMatrix z) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvPsiBasis i) z)
    (tendsto_ckmrvLeechMinusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvMinusResidue_contract_self, mul_zero] at h
  simpa only [ckmrvLeechMinusKernel] using h

/-- `Res_{τ=z} (K₋⁽⁸⁾|T) = −1/(2π)`. -/
theorem tendsto_ckmrvEightMinusKernel_residue_T (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvEightMinusKernel σ z) ∣[(4 : ℤ)] ModularGroup.T) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
  have h2 := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPsiTranslationSlope (ofComplex w)) (ckmrvTildePsiBasis z)
    (ckmrvPsiTranslationSlope z) (fun w => ckmrvEightMinusCoefficientMatrix (ofComplex w) z)
    ((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) •
      ckmrvMinusResidueMatrix z) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvPsiTranslationSlope i) z)
    (tendsto_ckmrvEightMinusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvMinusResidue_contract_slope, minus_residue_scale] at h2
  have h := (tendsto_ckmrvEightMinusKernel_residue z hA hB).add h2
  rw [zero_add] at h
  refine h.congr fun w => ?_
  rw [ckmrv_slash_T_apply_smul, ckmrvEightMinusKernel_T]
  simp only [ckmrvEightMinusTranslationSlope]
  ring

theorem tendsto_ckmrvLeechMinusKernel_residue_T (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvLeechMinusKernel σ z) ∣[(12 : ℤ)] ModularGroup.T) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
  have h2 := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPsiTranslationSlope (ofComplex w)) (ckmrvTildePsiBasis z)
    (ckmrvPsiTranslationSlope z) (fun w => ckmrvLeechMinusCoefficientMatrix (ofComplex w) z)
    ((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) •
      ckmrvMinusResidueMatrix z) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvPsiTranslationSlope i) z)
    (tendsto_ckmrvLeechMinusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvMinusResidue_contract_slope, minus_residue_scale] at h2
  have h := (tendsto_ckmrvLeechMinusKernel_residue z hA hB).add h2
  rw [zero_add] at h
  refine h.congr fun w => ?_
  rw [ckmrv_slash_T_apply_smul, ckmrvLeechMinusKernel_T]
  simp only [ckmrvLeechMinusTranslationSlope]
  ring

/-- `Res_{τ=z} (K₋⁽⁸⁾|TS) = 0`. -/
theorem tendsto_ckmrvEightMinusKernel_residue_TS (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvEightMinusKernel σ z) ∣[(4 : ℤ)]
        (ModularGroup.T * ModularGroup.S)) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  have h2 := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPsiSlopeS (ofComplex w)) (ckmrvTildePsiBasis z)
    (ckmrvPsiSlopeS z) (fun w => ckmrvEightMinusCoefficientMatrix (ofComplex w) z)
    ((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) •
      ckmrvMinusResidueMatrix z) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvPsiSlopeS i) z)
    (tendsto_ckmrvEightMinusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvMinusResidue_contract_slopeS, mul_zero] at h2
  have h := (tendsto_ckmrvEightMinusKernel_residue z hA hB).add h2
  rw [zero_add] at h
  refine h.congr fun w => ?_
  rw [ckmrvEightMinusKernel_slash_TS]
  simp only [ckmrvEightMinusKernel]
  ring

theorem tendsto_ckmrvLeechMinusKernel_residue_TS (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvLeechMinusKernel σ z) ∣[(12 : ℤ)]
        (ModularGroup.T * ModularGroup.S)) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  have h2 := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvPsiSlopeS (ofComplex w)) (ckmrvTildePsiBasis z)
    (ckmrvPsiSlopeS z) (fun w => ckmrvLeechMinusCoefficientMatrix (ofComplex w) z)
    ((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) •
      ckmrvMinusResidueMatrix z) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvPsiSlopeS i) z)
    (tendsto_ckmrvLeechMinusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvMinusResidue_contract_slopeS, mul_zero] at h2
  have h := (tendsto_ckmrvLeechMinusKernel_residue z hA hB).add h2
  rw [zero_add] at h
  refine h.congr fun w => ?_
  rw [ckmrvLeechMinusKernel_slash_TS]
  simp only [ckmrvLeechMinusKernel]
  ring

/-! ## Plus residues at `T` and `TS` -/

theorem ckmrvPhiTranslationSlope_S (τ : ℍ) (i : Fin 3) :
    ckmrvPhiTranslationSlope (ModularGroup.S • τ) i =
      (τ : ℂ) ^ ckmrvPhiWeight i * ckmrvTildePhiBasis τ i := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : (τ : ℂ) ≠ 0 := τ.ne_zero
  simp only [ckmrvPhiTranslationSlope, ckmrvTildePhiBasis, eisensteinTwo_S_explicit]
  fin_cases i
  · simp [ckmrvPhiWeight]
    field_simp
  · simp [ckmrvPhiWeight]
  · simp only [ckmrvPhiWeight, Fin.reduceFinMk, Matrix.cons_val]
    simp only [zpow_ofNat]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

theorem ckmrvEightPlusSlopeRow_S (τ : ℍ) (i : Fin 3) :
    ckmrvPhiTranslationSlope (ModularGroup.S • τ) i *
      ckmrvModularFactor (ModularGroup.S • τ) (![4, 3, 2] i) =
        (τ : ℂ) ^ 4 * (ckmrvTildePhiBasis τ i * ckmrvModularFactor τ (![4, 3, 2] i)) := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [ckmrvPhiTranslationSlope_S]
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  simp only [zpow_ofNat]
  fin_cases i <;> dsimp [ckmrvPhiWeight] <;> field_simp [τ.ne_zero, hΔ]

theorem ckmrvLeechPlusSlopeRow_S (τ : ℍ) (i : Fin 3) :
    ckmrvPhiTranslationSlope (ModularGroup.S • τ) i *
      ckmrvModularFactor (ModularGroup.S • τ) (![8, 7, 6] i) =
        (τ : ℂ) ^ 12 * (ckmrvTildePhiBasis τ i * ckmrvModularFactor τ (![8, 7, 6] i)) := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  rw [ckmrvPhiTranslationSlope_S]
  simp_rw [ckmrvModularFactor_eq_products, levelOne_S ModularForm.E₄, levelOne_S ModularForm.E₆,
    discriminant_S]
  simp only [zpow_ofNat]
  fin_cases i <;> dsimp [ckmrvPhiWeight] <;> field_simp [τ.ne_zero, hΔ]

theorem ckmrvPlusResidue_contract_tilde (z : ℍ) :
    ckmrvCoreContraction (ckmrvTildePhiBasis z) (ckmrvTildePhiBasis z)
      ckmrvPlusResidueMatrix = 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [ckmrvCoreContraction, Fin.sum_univ_three, ckmrvTildePhiBasis, ckmrvPlusResidueMatrix]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem ckmrvEightPlusKernel_slash_TS (z τ : ℍ) :
    ((fun σ => ckmrvEightPlusKernel σ z) ∣[(4 : ℤ)]
      (ModularGroup.T * ModularGroup.S)) τ =
      -ckmrvEightPlusKernel τ z + ckmrvCoreContraction (ckmrvTildePhiBasis τ)
        (ckmrvTildePhiBasis z) (ckmrvEightPlusCoefficientMatrix τ z) := by
  rw [SlashAction.slash_mul, ckmrv_slash_S_apply, ckmrv_slash_T_apply,
    ckmrvEightPlusKernel_translate_affine, ckmrvEightPlusKernel_S]
  have hslope : ckmrvEightPlusTranslationSlope (ModularGroup.S • τ) z = (τ : ℂ) ^ 4 *
      ckmrvCoreContraction (ckmrvTildePhiBasis τ) (ckmrvTildePhiBasis z)
        (ckmrvEightPlusCoefficientMatrix τ z) := by
    unfold ckmrvEightPlusTranslationSlope ckmrvEightPlusCoefficientMatrix ckmrvModularCoreMatrix
    rw [kleinModularJ_S]
    rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
    rw [ckmrvDiagonalCore_contract_left_covariance
      (ckmrvTildePhiBasis τ) (ckmrvPhiTranslationSlope (ModularGroup.S • τ)) _
      (fun i => ckmrvModularFactor τ (![4, 3, 2] i)) _ _ _
      ((τ : ℂ) ^ 4) (ckmrvEightPlusSlopeRow_S τ)]
    ring
  rw [hslope]
  simp only [Int.cast_one, one_mul, zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

theorem ckmrvLeechPlusKernel_slash_TS (z τ : ℍ) :
    ((fun σ => ckmrvLeechPlusKernel σ z) ∣[(12 : ℤ)]
      (ModularGroup.T * ModularGroup.S)) τ =
      -ckmrvLeechPlusKernel τ z + ckmrvCoreContraction (ckmrvTildePhiBasis τ)
        (ckmrvTildePhiBasis z) (ckmrvLeechPlusCoefficientMatrix τ z) := by
  rw [SlashAction.slash_mul, ckmrv_slash_S_apply, ckmrv_slash_T_apply,
    ckmrvLeechPlusKernel_translate_affine, ckmrvLeechPlusKernel_S]
  have hslope : ckmrvLeechPlusTranslationSlope (ModularGroup.S • τ) z = (τ : ℂ) ^ 12 *
      ckmrvCoreContraction (ckmrvTildePhiBasis τ) (ckmrvTildePhiBasis z)
        (ckmrvLeechPlusCoefficientMatrix τ z) := by
    unfold ckmrvLeechPlusTranslationSlope ckmrvLeechPlusCoefficientMatrix ckmrvModularCoreMatrix
    simp only [kleinModularJ_S]
    rw [ckmrvCoreContraction_smul, ckmrvCoreContraction_smul]
    rw [ckmrvDiagonalCore_contract_left_covariance
      (ckmrvTildePhiBasis τ) (ckmrvPhiTranslationSlope (ModularGroup.S • τ)) _
      (fun i => ckmrvModularFactor τ (![8, 7, 6] i)) _ _ _
      ((τ : ℂ) ^ 12) (ckmrvLeechPlusSlopeRow_S τ)]
    ring
  rw [hslope]
  simp only [Int.cast_one, one_mul, zpow_neg, zpow_ofNat]
  field_simp [τ.ne_zero]

/-- `Res_{τ=z} (K₊⁽⁸⁾|T) = −1/(2π)`, the existing `n = 1` translate in slash form. -/
theorem tendsto_ckmrvEightPlusKernel_residue_T (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvEightPlusKernel σ z) ∣[(4 : ℤ)] ModularGroup.T) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
  have h := tendsto_ckmrvEightPlusKernel_integer_translate 1 z hA hB
  simp only [Int.cast_one] at h
  refine h.congr fun w => ?_
  rw [ckmrv_slash_T_apply]

theorem tendsto_ckmrvLeechPlusKernel_residue_T (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvLeechPlusKernel σ z) ∣[(12 : ℤ)] ModularGroup.T) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
  have h := tendsto_ckmrvLeechPlusKernel_integer_translate 1 z hA hB
  simp only [Int.cast_one] at h
  refine h.congr fun w => ?_
  rw [ckmrv_slash_T_apply]

/-- `Res_{τ=z} (K₊⁽⁸⁾|TS) = 0`. -/
theorem tendsto_ckmrvEightPlusKernel_residue_TS (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvEightPlusKernel σ z) ∣[(4 : ℤ)]
        (ModularGroup.T * ModularGroup.S)) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  have h2 := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvTildePhiBasis (ofComplex w)) (ckmrvTildePhiBasis z)
    (ckmrvTildePhiBasis z) (fun w => ckmrvEightPlusCoefficientMatrix (ofComplex w) z)
    (((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvTildePhiBasis i) z)
    (tendsto_ckmrvEightPlusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvPlusResidue_contract_tilde, mul_zero] at h2
  have h := (tendsto_ckmrvEightPlusKernel_diagonal_scaled_zero z hA hB).neg.add h2
  rw [neg_zero, zero_add] at h
  refine h.congr fun w => ?_
  rw [ckmrvEightPlusKernel_slash_TS]
  ring

theorem tendsto_ckmrvLeechPlusKernel_residue_TS (z : ℍ)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ((fun σ => ckmrvLeechPlusKernel σ z) ∣[(12 : ℤ)]
        (ModularGroup.T * ModularGroup.S)) (ofComplex w))
      (𝓝[≠] (z : ℂ)) (𝓝 0) := by
  have h2 := tendsto_ckmrvCoreContraction_scaled
    (fun w => ckmrvTildePhiBasis (ofComplex w)) (ckmrvTildePhiBasis z)
    (ckmrvTildePhiBasis z) (fun w => ckmrvLeechPlusCoefficientMatrix (ofComplex w) z)
    (((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) (z : ℂ)
    (fun i => tendsto_comp_ofComplex (mdifferentiable_ckmrvTildePhiBasis i) z)
    (tendsto_ckmrvLeechPlusCoefficientMatrix_published_residue z hA hB)
  rw [ckmrvCoreContraction_smul, ckmrvPlusResidue_contract_tilde, mul_zero] at h2
  have h := (tendsto_ckmrvLeechPlusKernel_diagonal_scaled_zero z hA hB).neg.add h2
  rw [neg_zero, zero_add] at h
  refine h.congr fun w => ?_
  rw [ckmrvLeechPlusKernel_slash_TS]
  ring

end E8Leech
