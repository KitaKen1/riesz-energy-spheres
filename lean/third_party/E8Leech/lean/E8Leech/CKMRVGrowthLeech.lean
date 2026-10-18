import E8Leech.CuspExpansionTheta
import E8Leech.CKMRVHolomorphic
import E8Leech.CKMRVKernelAsymptotics

/-!
# Decay at `i∞` of the Leech minus kernel (CKMRV (4.21), dimension 24)

For fixed `z`, `K^{(24)}_-(τ, z) = O(|τ| e^{-4π Im τ})` as `Im τ → ∞`.

Structure of the proof. Write `ℓ = πiτ + 4 log 2` and `ψᵢ = ℓ ξᵢ + Aᵢ`; the `Aᵢ` are
`T`-invariant because `ψ(τ+1) = ψ(τ) + πi ξ(τ)` and `ℓ(τ+1) = ℓ(τ) + πi`. With
`K = (j(τ) - j(z))⁻¹ Σ_j w_j(z) c_j(τ, z)` the coefficients are
* `c₀ = -3456 Δ`,
* `c₂ = ψ₂ E₈ - ψ₁ E₁₀ = ℓ B + C` with `B = ξ₄E₈ - ξ₂E₁₀`, `C = A₂E₈ - A₁E₁₀`,
* `c₁ = ℓ R_ℓ + R₀ + j(z) (3456 Δ + 2 c₂)`, `R_ℓ = -3 j B + 1728 ξ₄ E₈`,
  `R₀ = -3456 E₄³ - 3 j C + 1728 A₂ E₈`.
`B, C, R_ℓ, R₀` are `T`-invariant and holomorphic. `B, C → 0` by their second-order
expansions (`1152 s²` and `-1152 s²`), and `R_ℓ Δ`, `R₀ Δ` have vanishing second-order
expansions, so `R_ℓ, R₀ → 0`. Periodicity then gives `O(e^{-2π Im τ})` for all four.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The `T`-invariant parts of `ψ` -/

/-- `ℓ(τ) = πiτ + 4 log 2`, the linear part of `L`. -/
def ckmrvEll (τ : ℍ) : ℂ := π * I * τ + 4 * Real.log 2

def ckmrvAOne (τ : ℍ) : ℂ := ckmrvPsiBasis τ 1 - ckmrvEll τ * ckmrvXiTwo τ
def ckmrvATwo (τ : ℍ) : ℂ := ckmrvPsiBasis τ 2 - ckmrvEll τ * ckmrvXiFour τ

theorem ckmrvEll_T (τ : ℍ) : ckmrvEll (ModularGroup.T • τ) = ckmrvEll τ + π * I := by
  rw [ckmrvEll, ckmrvEll, coe_T_smul]
  ring

theorem ckmrvAOne_T (τ : ℍ) : ckmrvAOne (ModularGroup.T • τ) = ckmrvAOne τ := by
  rw [ckmrvAOne, ckmrvAOne, ckmrvPsiBasis_T, ckmrvEll_T, ckmrvXiTwo_T]
  have h : ckmrvPsiTranslationSlope τ 1 = π * I * ckmrvXiTwo τ := rfl
  rw [h]
  ring

theorem ckmrvATwo_T (τ : ℍ) : ckmrvATwo (ModularGroup.T • τ) = ckmrvATwo τ := by
  rw [ckmrvATwo, ckmrvATwo, ckmrvPsiBasis_T, ckmrvEll_T, ckmrvXiFour_T]
  have h : ckmrvPsiTranslationSlope τ 2 = π * I * ckmrvXiFour τ := rfl
  rw [h]
  ring

theorem ckmrvAOne_eq (τ : ℍ) : ckmrvAOne τ =
    ckmrvXiTwo τ * (ckmrvL τ - π * I * τ - 4 * Real.log 2) + ckmrvXiTwoS τ * ckmrvLS τ := by
  have h : ckmrvPsiBasis τ 1 = ckmrvXiTwo τ * ckmrvL τ + ckmrvXiTwoS τ * ckmrvLS τ := rfl
  rw [ckmrvAOne, h, ckmrvEll]
  ring

theorem ckmrvATwo_eq (τ : ℍ) : ckmrvATwo τ =
    ckmrvXiFour τ * (ckmrvL τ - π * I * τ - 4 * Real.log 2) + ckmrvXiFourS τ * ckmrvLS τ := by
  have h : ckmrvPsiBasis τ 2 = ckmrvXiFour τ * ckmrvL τ + ckmrvXiFourS τ * ckmrvLS τ := rfl
  rw [ckmrvATwo, h, ckmrvEll]
  ring

theorem mdifferentiable_ckmrvEll : MDiff ckmrvEll :=
  (mdifferentiable_const.mul mdifferentiable_coe).add mdifferentiable_const

theorem mdifferentiable_ckmrvXiTwo : MDiff ckmrvXiTwo :=
  mdifferentiable_thetaU.add mdifferentiable_thetaW

theorem mdifferentiable_ckmrvXiFour : MDiff ckmrvXiFour := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  have hW := mdifferentiable_thetaW
  have hfun : ckmrvXiFour = thetaU * thetaU + thetaW * thetaW -
      (fun _ => (2 : ℂ)) * (thetaV * thetaV) := by
    funext τ
    simp only [ckmrvXiFour, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hfun]
  exact ((hU.mul hU).add (hW.mul hW)).sub (mdifferentiable_const.mul (hV.mul hV))

theorem mdifferentiable_ckmrvAOne : MDiff ckmrvAOne :=
  (mdifferentiable_ckmrvPsiBasis 1).sub (mdifferentiable_ckmrvEll.mul mdifferentiable_ckmrvXiTwo)

theorem mdifferentiable_ckmrvATwo : MDiff ckmrvATwo :=
  (mdifferentiable_ckmrvPsiBasis 2).sub (mdifferentiable_ckmrvEll.mul mdifferentiable_ckmrvXiFour)

/-! ## Second-order expansions -/

theorem hasExp3_ckmrvXiTwo : HasExp3 ckmrvXiTwo 2 0 48 :=
  (hasExp3_thetaU.add hasExp3_thetaW).congr_fun (fun τ => rfl)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_ckmrvXiFour : HasExp3 ckmrvXiFour 2 0 (-288) :=
  ((hasExp3_thetaU.pow.add hasExp3_thetaW.pow).sub ((hasExp3_thetaV.pow).const_mul 2)).congr_fun
    (fun τ => by simp only [ckmrvXiFour]) |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_ckmrvXiTwoS : HasExp3 ckmrvXiTwoS (-1) (-24) (-24) :=
  (hasExp3_thetaU.add hasExp3_thetaV).neg.congr_fun (fun τ => by simp only [ckmrvXiTwoS])
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_ckmrvXiFourS : HasExp3 ckmrvXiFourS (-1) 48 144 :=
  ((hasExp3_thetaU.pow.add hasExp3_thetaV.pow).sub ((hasExp3_thetaW.pow).const_mul 2)).congr_fun
    (fun τ => by simp only [ckmrvXiFourS]) |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_ckmrvAOne : HasExp3 ckmrvAOne 0 0 408 :=
  ((hasExp3_ckmrvXiTwo.mul hasExp3_ckmrvL_sub).add (hasExp3_ckmrvXiTwoS.mul hasExp3_ckmrvLS))
    |>.congr_fun (fun τ => (ckmrvAOne_eq τ).symm)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_ckmrvATwo : HasExp3 ckmrvATwo 0 0 (-744) :=
  ((hasExp3_ckmrvXiFour.mul hasExp3_ckmrvL_sub).add (hasExp3_ckmrvXiFourS.mul hasExp3_ckmrvLS))
    |>.congr_fun (fun τ => (ckmrvATwo_eq τ).symm)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_eisensteinFour_sq :
    HasExp3 (fun τ : ℍ => ModularForm.E₄ τ ^ 2) 1 0 480 :=
  hasExp3_eisensteinFour.pow.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_eisensteinFour_mul_six :
    HasExp3 (fun τ : ℍ => ModularForm.E₄ τ * ModularForm.E₆ τ) 1 0 (-264) :=
  (hasExp3_eisensteinFour.mul hasExp3_eisensteinSix).congr_coeff
    (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_eisensteinFour_cube :
    HasExp3 (fun τ : ℍ => ModularForm.E₄ τ ^ 3) 1 0 720 :=
  (hasExp3_eisensteinFour_sq.mul hasExp3_eisensteinFour).congr_fun (fun τ => by ring)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

/-! ## The combinations `B`, `C`, `R_ℓ`, `R₀` -/

def leechB (τ : ℍ) : ℂ :=
  ckmrvXiFour τ * ModularForm.E₄ τ ^ 2 - ckmrvXiTwo τ * (ModularForm.E₄ τ * ModularForm.E₆ τ)

def leechC (τ : ℍ) : ℂ :=
  ckmrvATwo τ * ModularForm.E₄ τ ^ 2 - ckmrvAOne τ * (ModularForm.E₄ τ * ModularForm.E₆ τ)

def leechREll (τ : ℍ) : ℂ :=
  -3 * kleinModularJ τ * leechB τ + 1728 * ckmrvXiFour τ * ModularForm.E₄ τ ^ 2

def leechRZero (τ : ℍ) : ℂ :=
  -3456 * ModularForm.E₄ τ ^ 3 - 3 * kleinModularJ τ * leechC τ +
    1728 * ckmrvATwo τ * ModularForm.E₄ τ ^ 2

theorem hasExp3_leechB : HasExp3 leechB 0 0 1152 :=
  ((hasExp3_ckmrvXiFour.mul hasExp3_eisensteinFour_sq).sub
    (hasExp3_ckmrvXiTwo.mul hasExp3_eisensteinFour_mul_six)).congr_fun (fun τ => rfl)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem hasExp3_leechC : HasExp3 leechC 0 0 (-1152) :=
  ((hasExp3_ckmrvATwo.mul hasExp3_eisensteinFour_sq).sub
    (hasExp3_ckmrvAOne.mul hasExp3_eisensteinFour_mul_six)).congr_fun (fun τ => rfl)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem kleinModularJ_mul_discriminant (τ : ℍ) :
    kleinModularJ τ * ModularForm.discriminant τ = ModularForm.E₄ τ ^ 3 := by
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [kleinModularJ]
  field_simp

theorem hasExp3_leechREll_mul_discriminant :
    HasExp3 (fun τ => leechREll τ * ModularForm.discriminant τ) 0 0 0 := by
  have h := ((hasExp3_eisensteinFour_cube.mul hasExp3_leechB).const_mul (-3)).add
    (((hasExp3_ckmrvXiFour.mul hasExp3_eisensteinFour_sq).mul hasExp3_discriminant).const_mul 1728)
  refine (h.congr_fun fun τ => ?_).congr_coeff (by norm_num) (by norm_num) (by norm_num)
  rw [leechREll, ← kleinModularJ_mul_discriminant]
  ring

theorem hasExp3_leechRZero_mul_discriminant :
    HasExp3 (fun τ => leechRZero τ * ModularForm.discriminant τ) 0 0 0 := by
  have h := (((hasExp3_eisensteinFour_cube.mul hasExp3_discriminant).const_mul (-3456)).add
    ((hasExp3_eisensteinFour_cube.mul hasExp3_leechC).const_mul (-3))).add
    (((hasExp3_ckmrvATwo.mul hasExp3_eisensteinFour_sq).mul hasExp3_discriminant).const_mul 1728)
  refine (h.congr_fun fun τ => ?_).congr_coeff (by norm_num) (by norm_num) (by norm_num)
  rw [leechRZero, ← kleinModularJ_mul_discriminant]
  ring

/-- If `f Δ = O(|s|³)` then `f → 0`. -/
theorem tendsto_zero_of_mul_discriminant {f : ℍ → ℂ}
    (hf : HasExp3 (fun τ => f τ * ModularForm.discriminant τ) 0 0 0) :
    Tendsto f atImInfty (𝓝 0) := by
  have h3 := hf.isBigO_cube
  have hinv := isBigO_discriminant_inv
  have h := (h3.mul hinv)
  have hs : (fun τ : ℍ => ‖cuspS τ‖ ^ 3 * Real.exp (2 * π * τ.im)) =O[atImInfty]
      fun τ : ℍ => ‖cuspS τ‖ := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
    rw [exp_two_pi_eq_norm_cuspS_sq_inv]
    have hs0 : ‖cuspS τ‖ ≠ 0 := norm_ne_zero_iff.mpr (cuspS_ne_zero τ)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (norm_nonneg _), one_mul]
    apply le_of_eq
    field_simp
  refine ((h.trans hs).trans_tendsto tendsto_norm_cuspS).congr fun τ => ?_
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  field_simp

/-! ## Decay of the four `T`-invariant combinations -/

theorem mdifferentiable_eisensteinFour_sq : MDiff (fun τ : ℍ => ModularForm.E₄ τ ^ 2) := by
  have h := ModularFormClass.holo ModularForm.E₄
  have hfun : (fun τ : ℍ => ModularForm.E₄ τ ^ 2) =
      (ModularForm.E₄ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ) := by
    funext τ; simp only [Pi.mul_apply]; ring
  rw [hfun]
  exact h.mul h

theorem mdifferentiable_eisensteinFour_mul_six :
    MDiff (fun τ : ℍ => ModularForm.E₄ τ * ModularForm.E₆ τ) :=
  (ModularFormClass.holo ModularForm.E₄).mul (ModularFormClass.holo ModularForm.E₆)

theorem eisensteinFour_T (τ : ℍ) : ModularForm.E₄ (ModularGroup.T • τ) = ModularForm.E₄ τ := by
  rw [← vadd_one_eq_T_smul, eisensteinFour_vadd_one]

theorem eisensteinSix_T (τ : ℍ) : ModularForm.E₆ (ModularGroup.T • τ) = ModularForm.E₆ τ := by
  rw [← vadd_one_eq_T_smul, eisensteinSix_vadd_one]

theorem kleinModularJ_T (τ : ℍ) : kleinModularJ (ModularGroup.T • τ) = kleinModularJ τ := by
  have hΔ : ModularForm.discriminant (ModularGroup.T • τ) = ModularForm.discriminant τ := by
    rw [← vadd_one_eq_T_smul]
    have h := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods CuspForm.discriminant τ
      one_mem_strictPeriods_SL
    simpa [CuspForm.coe_discriminant] using h
  rw [kleinModularJ, kleinModularJ, eisensteinFour_T, hΔ]

theorem leechB_T (τ : ℍ) : leechB (ModularGroup.T • τ) = leechB τ := by
  simp only [leechB, ckmrvXiTwo_T, ckmrvXiFour_T, eisensteinFour_T, eisensteinSix_T]

theorem leechC_T (τ : ℍ) : leechC (ModularGroup.T • τ) = leechC τ := by
  simp only [leechC, ckmrvAOne_T, ckmrvATwo_T, eisensteinFour_T, eisensteinSix_T]

theorem leechREll_T (τ : ℍ) : leechREll (ModularGroup.T • τ) = leechREll τ := by
  simp only [leechREll, kleinModularJ_T, leechB_T, ckmrvXiFour_T, eisensteinFour_T]

theorem leechRZero_T (τ : ℍ) : leechRZero (ModularGroup.T • τ) = leechRZero τ := by
  simp only [leechRZero, kleinModularJ_T, leechC_T, ckmrvATwo_T, eisensteinFour_T]

theorem mdifferentiable_leechB : MDiff leechB :=
  (mdifferentiable_ckmrvXiFour.mul mdifferentiable_eisensteinFour_sq).sub
    (mdifferentiable_ckmrvXiTwo.mul mdifferentiable_eisensteinFour_mul_six)

theorem mdifferentiable_leechC : MDiff leechC :=
  (mdifferentiable_ckmrvATwo.mul mdifferentiable_eisensteinFour_sq).sub
    (mdifferentiable_ckmrvAOne.mul mdifferentiable_eisensteinFour_mul_six)

theorem mdifferentiable_leechREll : MDiff leechREll := by
  have hJ := mdifferentiable_kleinModularJ
  have hfun : leechREll = (fun _ => (-3 : ℂ)) * kleinModularJ * leechB +
      (fun _ => (1728 : ℂ)) * ckmrvXiFour * (fun τ : ℍ => ModularForm.E₄ τ ^ 2) := by
    funext τ; simp only [leechREll, Pi.add_apply, Pi.mul_apply]
  rw [hfun]
  exact ((mdifferentiable_const.mul hJ).mul mdifferentiable_leechB).add
    ((mdifferentiable_const.mul mdifferentiable_ckmrvXiFour).mul mdifferentiable_eisensteinFour_sq)

theorem mdifferentiable_leechRZero : MDiff leechRZero := by
  have hJ := mdifferentiable_kleinModularJ
  have h4 := ModularFormClass.holo ModularForm.E₄
  have hfun : leechRZero = (fun _ => (-3456 : ℂ)) * ((ModularForm.E₄ : ℍ → ℂ) *
      (fun τ : ℍ => ModularForm.E₄ τ ^ 2)) - (fun _ => (3 : ℂ)) * kleinModularJ * leechC +
      (fun _ => (1728 : ℂ)) * ckmrvATwo * (fun τ : ℍ => ModularForm.E₄ τ ^ 2) := by
    funext τ; simp only [leechRZero, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring
  rw [hfun]
  exact ((mdifferentiable_const.mul (h4.mul mdifferentiable_eisensteinFour_sq)).sub
    ((mdifferentiable_const.mul hJ).mul mdifferentiable_leechC)).add
    ((mdifferentiable_const.mul mdifferentiable_ckmrvATwo).mul mdifferentiable_eisensteinFour_sq)

theorem isBigO_leechB : leechB =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) :=
  isBigO_exp_of_T_invariant mdifferentiable_leechB leechB_T hasExp3_leechB.tendsto

theorem isBigO_leechC : leechC =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) :=
  isBigO_exp_of_T_invariant mdifferentiable_leechC leechC_T hasExp3_leechC.tendsto

theorem isBigO_leechREll : leechREll =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) :=
  isBigO_exp_of_T_invariant mdifferentiable_leechREll leechREll_T
    (tendsto_zero_of_mul_discriminant hasExp3_leechREll_mul_discriminant)

theorem isBigO_leechRZero : leechRZero =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) :=
  isBigO_exp_of_T_invariant mdifferentiable_leechRZero leechRZero_T
    (tendsto_zero_of_mul_discriminant hasExp3_leechRZero_mul_discriminant)

/-! ## The Leech minus kernel -/

/-- The `j`-th coefficient of the Leech minus kernel; it depends on `z` through `j(τ) - j(z)`. -/
def leechMinusTauCoeff (j : Fin 3) (τ z : ℍ) : ℂ :=
  ∑ i, ckmrvPsiBasis τ i * ckmrvModularFactor τ (![7, 6, 5] i) *
    ckmrvLeechMinusCore (kleinModularJ τ) (kleinModularJ τ - kleinModularJ z) i j

theorem ckmrvLeechMinusKernel_eq_sum (τ z : ℍ) :
    ckmrvLeechMinusKernel τ z =
      (kleinModularJ τ - kleinModularJ z)⁻¹ *
        ∑ j, ((ckmrvMinusScale * ModularForm.discriminant z)⁻¹ *
          (ckmrvModularFactor z (![2, 1, 0] j) * ckmrvTildePsiBasis z j)) *
            leechMinusTauCoeff j τ z := by
  simp only [ckmrvLeechMinusKernel, ckmrvCoreContraction, ckmrvLeechMinusCoefficientMatrix,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply, Matrix.smul_apply, smul_eq_mul,
    leechMinusTauCoeff, Fin.sum_univ_three, mul_inv]
  ring

theorem leechMinusTauCoeff_expand (τ z : ℍ) :
    leechMinusTauCoeff 0 τ z = -(2 * 1728) * ModularForm.discriminant τ ∧
    leechMinusTauCoeff 1 τ z =
      ModularForm.discriminant τ * (-(2 * 1728) * (kleinModularJ τ - kleinModularJ z)) +
      ckmrvPsiBasis τ 1 * (ModularForm.E₄ τ * ModularForm.E₆ τ) *
        (kleinModularJ τ + 2 * (kleinModularJ τ - kleinModularJ z)) +
      ckmrvPsiBasis τ 2 * ModularForm.E₄ τ ^ 2 *
        (1728 - 2 * (kleinModularJ τ - kleinModularJ z) - kleinModularJ τ) ∧
    leechMinusTauCoeff 2 τ z =
      -(ckmrvPsiBasis τ 1 * (ModularForm.E₄ τ * ModularForm.E₆ τ)) +
        ckmrvPsiBasis τ 2 * ModularForm.E₄ τ ^ 2 := by
  have h7 : ckmrvModularFactor τ 7 = ModularForm.discriminant τ := rfl
  have h6 : ckmrvModularFactor τ 6 = ModularForm.E₄ τ * ModularForm.E₆ τ :=
    eisensteinTen_eq_four_mul_six τ
  have h5 : ckmrvModularFactor τ 5 = ModularForm.E₄ τ ^ 2 := eisensteinEight_eq_four_sq τ
  have hp0 : ckmrvPsiBasis τ 0 = 1 := rfl
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [leechMinusTauCoeff, Fin.sum_univ_three, ckmrvLeechMinusCore, h7, h6, h5, hp0]
  ring

/-- `c₂ = ℓ B + C`. -/
theorem leechMinusTauCoeff_two (τ z : ℍ) :
    leechMinusTauCoeff 2 τ z = ckmrvEll τ * leechB τ + leechC τ := by
  rw [(leechMinusTauCoeff_expand τ z).2.2, leechB, leechC, ckmrvAOne, ckmrvATwo]
  ring

/-- `c₁ = ℓ R_ℓ + R₀ + j(z) (3456 Δ + 2 c₂)`. -/
theorem leechMinusTauCoeff_one (τ z : ℍ) :
    leechMinusTauCoeff 1 τ z = ckmrvEll τ * leechREll τ + leechRZero τ +
      kleinModularJ z * (2 * 1728 * ModularForm.discriminant τ +
        2 * (ckmrvEll τ * leechB τ + leechC τ)) := by
  rw [(leechMinusTauCoeff_expand τ z).2.1, leechREll, leechRZero, leechB, leechC, ckmrvAOne,
    ckmrvATwo]
  linear_combination (-(2 * 1728) : ℂ) * kleinModularJ_mul_discriminant τ

theorem isBigO_ckmrvEll : ckmrvEll =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ :=
  isBigO_linear_norm_coe.congr_left fun _ => rfl

theorem isBigO_leechMinusTauCoeff (j : Fin 3) (z : ℍ) :
    (fun τ : ℍ => leechMinusTauCoeff j τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) := by
  have hc2 : (fun τ : ℍ => ckmrvEll τ * leechB τ + leechC τ) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) :=
    (isBigO_ckmrvEll.mul isBigO_leechB).add (isBigO_leechC.trans isBigO_exp_neg_two_pi_norm_mul)
  have hΔ := isBigO_discriminant.trans isBigO_exp_neg_two_pi_norm_mul
  fin_cases j
  · exact ((hΔ.const_mul_left (-(2 * 1728) : ℂ)).congr_left
      fun τ => ((leechMinusTauCoeff_expand τ z).1).symm)
  · have h := ((isBigO_ckmrvEll.mul isBigO_leechREll).add
      (isBigO_leechRZero.trans isBigO_exp_neg_two_pi_norm_mul)).add
      (((hΔ.const_mul_left (2 * 1728 : ℂ)).add (hc2.const_mul_left 2)).const_mul_left
        (kleinModularJ z))
    exact h.congr_left fun τ => (leechMinusTauCoeff_one τ z).symm
  · exact hc2.congr_left fun τ => (leechMinusTauCoeff_two τ z).symm

/-- **CKMRV (4.21), dimension 24, minus kernel.** For fixed `z`,
`K₋^{(24)}(τ, z) = O(|τ| e^{-4π Im τ})` as `Im τ → ∞`. -/
theorem isBigO_ckmrvLeechMinusKernel (z : ℍ) :
    (fun τ : ℍ => ckmrvLeechMinusKernel τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
  have hsum : (fun τ : ℍ => ∑ j, ((ckmrvMinusScale * ModularForm.discriminant z)⁻¹ *
      (ckmrvModularFactor z (![2, 1, 0] j) * ckmrvTildePsiBasis z j)) *
        leechMinusTauCoeff j τ z) =O[atImInfty]
          fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) := by
    simp only [Fin.sum_univ_three]
    exact (((isBigO_leechMinusTauCoeff 0 z).const_mul_left _).add
      ((isBigO_leechMinusTauCoeff 1 z).const_mul_left _)).add
      ((isBigO_leechMinusTauCoeff 2 z).const_mul_left _)
  have h := (isBigO_kleinModularJ_sub_inv z).mul hsum
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · exact (ckmrvLeechMinusKernel_eq_sum τ z).symm
  · dsimp only
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring

end E8Leech
