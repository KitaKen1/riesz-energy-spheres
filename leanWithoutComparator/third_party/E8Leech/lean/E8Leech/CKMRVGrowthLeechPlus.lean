import E8Leech.CKMRVGrowthLeech

/-!
# CKMRV (4.21) for the Leech plus kernel

For fixed `z`, `K₊⁽²⁴⁾(τ, z) = O(|τ| e^{-4π Im τ})` as `Im τ → ∞`.

The `τ`-coefficients of the kernel are polynomials in `τ`, `E₂, E₄, E₆, Δ`, `j(τ)` and
`(j(τ) - j(z))⁻¹ = Δ k` with `k = (E₄³ - j(z) Δ)⁻¹ → 1`. Clearing `k`, every coefficient becomes a
combination of products of two functions that are `T`-invariant, holomorphic and vanish at `i∞`:
`Δ`, `w = E₄² - E₂E₆`, `v = E₆ - E₂E₄` and `E₄ - 1`, plus `ρ = E₄² - E₂E₆ - 1008 Δ = O(q²)`.

Only `ρ` needs a first `q`-coefficient: `E₂ = 1 - 24 q + O(q²)`, which we take from Mathlib's
`q`-expansion of `E₂` through the Taylor estimate of its cusp function.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Second-order expansion of `E₂` -/

theorem qParam_one_eq_cuspS_sq (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) = cuspS τ ^ 2 := by
  rw [Function.Periodic.qParam, cuspS, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `E₂ = 1 - 24 q + O(|q|²)`, from the `q`-expansion of `E₂`. -/
theorem isBigO_eisensteinTwo_sub_linear :
    (fun τ : ℍ => EisensteinSeries.E2 τ - (1 - 24 * Function.Periodic.qParam 1 (τ : ℂ)))
      =O[atImInfty] fun τ : ℍ => ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ 2 := by
  have hper := eisensteinTwo_periodic_comp_ofComplex
  have hps := hasFPowerSeriesOnBall_cuspFunction (h := 1) one_pos
    (analyticAt_cuspFunction_zero one_pos hper E2_mdifferentiable
      EisensteinSeries.isBoundedAtImInfty_E2)
    (fun τ ↦ by
      simpa only [Function.Periodic.qParam, ofReal_one, div_one] using
        EisensteinSeries.hasSum_qExpansion_E2 (z := τ))
  have hO := (hps.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 2).comp_tendsto
    (qParam_tendsto_atImInfty one_pos)
  refine hO.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => rfl)
  simp only [Function.comp_apply, zero_add]
  rw [eq_cuspFunction τ one_ne_zero hper]
  congr 1
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, ArithmeticFunction.sigma_apply]
  ring

theorem hasExp3_eisensteinTwo : HasExp3 (fun τ : ℍ => EisensteinSeries.E2 τ) 1 0 (-24) := by
  have h4 : (fun τ : ℍ => ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ 2) =O[atImInfty]
      fun τ : ℍ => ‖cuspS τ‖ ^ 3 := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul, qParam_one_eq_cuspS_sq, norm_pow, ← pow_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) (norm_cuspS_le_one τ) (by norm_num)
  refine (isBigO_eisensteinTwo_sub_linear.trans h4).congr_left fun τ => ?_
  dsimp only
  rw [qParam_one_eq_cuspS_sq]
  ring

/-! ## Decay of `T`-invariant functions -/

theorem discriminant_vadd_one (τ : ℍ) :
    ModularForm.discriminant ((1 : ℝ) +ᵥ τ) = ModularForm.discriminant τ := by
  have h := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods CuspForm.discriminant τ
    one_mem_strictPeriods_SL
  simpa [CuspForm.coe_discriminant] using h

/-- A `T`-invariant holomorphic function with limit `0` at `i∞` is `O(q)`. -/
theorem isBigO_q_of_vadd {f : ℍ → ℂ} (hf : MDiff f)
    (hper : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (hlim : Tendsto f atImInfty (𝓝 0)) :
    f =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  simpa using isBigO_exp_of_periodic (h := 1) one_pos hf hper hlim

theorem exp_neg_two_pi_mul_self (τ : ℍ) :
    Real.exp (-2 * π * τ.im) * Real.exp (-2 * π * τ.im) = Real.exp (-4 * π * τ.im) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem isBigO_exp_neg_four_pi_two_pi :
    (fun τ : ℍ => Real.exp (-4 * π * τ.im)) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, τ.im_pos])

/-- `O(q) · O(q) = O(q²)`. -/
theorem isBigO_mul_q {f g : ℍ → ℂ}
    (hf : f =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im))
    (hg : g =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im)) :
    (fun τ => f τ * g τ) =O[atImInfty] fun τ : ℍ => Real.exp (-4 * π * τ.im) :=
  (hf.mul hg).congr_right exp_neg_two_pi_mul_self

/-- `O(q) · O(|τ| q) = O(|τ| q²)`. -/
theorem isBigO_mul_norm_q {f g : ℍ → ℂ}
    (hf : f =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im))
    (hg : g =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im)) :
    (fun τ => f τ * g τ) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) :=
  (hf.mul hg).congr_right fun τ => by rw [mul_left_comm, exp_neg_two_pi_mul_self]

/-- A factor with a limit does not change the order. -/
theorem isBigO_tendsto_mul {b f : ℍ → ℂ} {c : ℂ} {r : ℍ → ℝ}
    (hb : Tendsto b atImInfty (𝓝 c)) (hf : f =O[atImInfty] r) :
    (fun τ => b τ * f τ) =O[atImInfty] r :=
  ((hb.isBigO_one ℝ).mul hf).congr_right fun _ => one_mul _

theorem isBigO_le_norm_mul (r : ℍ → ℝ) :
    r =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ * r τ :=
  (isBigO_one_real_norm_coe.mul (isBigO_refl r atImInfty)).congr_left fun _ => one_mul _

/-- `τ P + c Q = O(|τ| r)` when `P, Q = O(r)`. -/
theorem isBigO_coe_mul_add_const_mul {P Q : ℍ → ℂ} {r : ℍ → ℝ} (c : ℂ)
    (hP : P =O[atImInfty] r) (hQ : Q =O[atImInfty] r) :
    (fun τ : ℍ => (τ : ℂ) * P τ + c * Q τ) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ * r τ :=
  (isBigO_coe_norm.mul hP).add ((hQ.const_mul_left c).trans (isBigO_le_norm_mul r))

/-! ## The vanishing atoms -/

/-- `w = E₄² - E₂ E₆ = O(q)`. -/
theorem isBigO_leechW :
    (fun τ : ℍ => ModularForm.E₄ τ ^ 2 - EisensteinSeries.E2 τ * ModularForm.E₆ τ)
      =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  refine isBigO_q_of_vadd (mdifferentiable_eisensteinFour_sq.sub
      (E2_mdifferentiable.mul (ModularFormClass.holo ModularForm.E₆)))
    (fun τ => by
      simp only [eisensteinTwo_vadd_one, eisensteinFour_vadd_one, eisensteinSix_vadd_one]) ?_
  have h := (tendsto_eisensteinFour_atImInfty.pow 2).sub
    (eisensteinTwo_tendsto_one_atImInfty.mul tendsto_eisensteinSix_atImInfty)
  have h0 : (1 : ℂ) ^ 2 - 1 * 1 = 0 := by norm_num
  rw [h0] at h
  exact h

/-- `v = E₆ - E₂ E₄ = O(q)`. -/
theorem isBigO_leechV :
    (fun τ : ℍ => ModularForm.E₆ τ - EisensteinSeries.E2 τ * ModularForm.E₄ τ)
      =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  refine isBigO_q_of_vadd ((ModularFormClass.holo ModularForm.E₆).sub
      (E2_mdifferentiable.mul (ModularFormClass.holo ModularForm.E₄)))
    (fun τ => by
      simp only [eisensteinTwo_vadd_one, eisensteinFour_vadd_one, eisensteinSix_vadd_one]) ?_
  have h := tendsto_eisensteinSix_atImInfty.sub
    (eisensteinTwo_tendsto_one_atImInfty.mul tendsto_eisensteinFour_atImInfty)
  have h0 : (1 : ℂ) - 1 * 1 = 0 := by norm_num
  rw [h0] at h
  exact h

/-- `ρ = E₄² - E₂ E₆ - 1008 Δ`. -/
def leechRho (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 2 - EisensteinSeries.E2 τ * ModularForm.E₆ τ -
    1008 * ModularForm.discriminant τ

theorem hasExp3_leechRho : HasExp3 leechRho 0 0 0 :=
  (((hasExp3_eisensteinFour.pow).sub (hasExp3_eisensteinTwo.mul hasExp3_eisensteinSix)).sub
    (hasExp3_discriminant.const_mul 1008)).congr_fun (fun τ => rfl)
    |>.congr_coeff (by norm_num) (by norm_num) (by norm_num)

theorem mdifferentiable_leechRho : MDiff leechRho :=
  (mdifferentiable_eisensteinFour_sq.sub
    (E2_mdifferentiable.mul (ModularFormClass.holo ModularForm.E₆))).sub
    (mdifferentiable_const.mul mdifferentiable_modularDiscriminant)

/-- `ρ = O(q²)`: `ρ / Δ` is `T`-invariant, holomorphic and tends to `0`. -/
theorem isBigO_leechRho :
    leechRho =O[atImInfty] fun τ : ℍ => Real.exp (-4 * π * τ.im) := by
  have hg := isBigO_q_of_vadd (f := fun τ => leechRho τ / ModularForm.discriminant τ)
    (mdifferentiable_leechRho.div mdifferentiable_modularDiscriminant
      ModularForm.discriminant_ne_zero)
    (fun τ => by
      simp only [leechRho, eisensteinTwo_vadd_one, eisensteinFour_vadd_one,
        eisensteinSix_vadd_one, discriminant_vadd_one])
    (tendsto_zero_of_mul_discriminant (hasExp3_leechRho.congr_fun fun τ =>
      (div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)).symm))
  exact (isBigO_mul_q hg isBigO_discriminant).congr_left fun τ =>
    div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)

/-! ## The factor `k = (E₄³ - j(z) Δ)⁻¹` -/

/-- `k = (E₄³ - j(z) Δ)⁻¹`, so that `(j(τ) - j(z))⁻¹ = Δ k`. -/
def leechPlusK (z τ : ℍ) : ℂ :=
  (ModularForm.E₄ τ ^ 3 - kleinModularJ z * ModularForm.discriminant τ)⁻¹

theorem kleinModularJ_sub_inv_eq (τ z : ℍ) :
    (kleinModularJ τ - kleinModularJ z)⁻¹ = ModularForm.discriminant τ * leechPlusK z τ := by
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  have hJ : kleinModularJ τ - kleinModularJ z =
      (ModularForm.E₄ τ ^ 3 - kleinModularJ z * ModularForm.discriminant τ) /
        ModularForm.discriminant τ := by
    rw [kleinModularJ]
    field_simp
  rw [hJ, inv_div, div_eq_mul_inv, leechPlusK]

theorem tendsto_leechPlusK_den (z : ℍ) :
    Tendsto (fun τ : ℍ => ModularForm.E₄ τ ^ 3 - kleinModularJ z * ModularForm.discriminant τ)
      atImInfty (𝓝 1) := by
  have h := (tendsto_eisensteinFour_atImInfty.pow 3).sub
    (tendsto_discriminant_atImInfty.const_mul (kleinModularJ z))
  have h1 : (1 : ℂ) ^ 3 - kleinModularJ z * 0 = 1 := by ring
  rw [h1] at h
  exact h

theorem tendsto_leechPlusK (z : ℍ) : Tendsto (leechPlusK z) atImInfty (𝓝 1) := by
  have h := (tendsto_leechPlusK_den z).inv₀ one_ne_zero
  rw [inv_one] at h
  exact h

theorem eventually_leechPlusK_mul (z : ℍ) : ∀ᶠ τ in atImInfty,
    leechPlusK z τ * (ModularForm.E₄ τ ^ 3 - kleinModularJ z * ModularForm.discriminant τ) =
      1 := by
  filter_upwards [(tendsto_leechPlusK_den z).eventually_ne one_ne_zero] with τ hτ
  exact inv_mul_cancel₀ hτ

/-! ## The Leech plus kernel -/

/-- The `j`-th coefficient of the Leech plus kernel; it depends on `z` through `j(τ) - j(z)`. -/
def leechPlusTauCoeff (j : Fin 3) (τ z : ℍ) : ℂ :=
  ∑ i, ckmrvPhiBasis τ i * ckmrvModularFactor τ (![8, 7, 6] i) *
    ckmrvLeechPlusCore (kleinModularJ τ) (kleinModularJ τ - kleinModularJ z) i j

theorem ckmrvLeechPlusKernel_eq_sum (τ z : ℍ) :
    ckmrvLeechPlusKernel τ z =
      ∑ j, ((1728 * ckmrvPlusScale * ModularForm.discriminant z)⁻¹ *
          (ckmrvModularFactor z (![3, 2, 1] j) * ckmrvTildePhiBasis z j)) *
            leechPlusTauCoeff j τ z := by
  simp only [ckmrvLeechPlusKernel, ckmrvCoreContraction, ckmrvLeechPlusCoefficientMatrix,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply, Matrix.smul_apply, smul_eq_mul,
    leechPlusTauCoeff, Fin.sum_univ_three]
  ring

theorem leechPlusTauCoeff_expand (τ z : ℍ) :
    leechPlusTauCoeff 0 τ z =
      6 * ((τ : ℂ) * (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ)) +
        (-12 * kleinModularJ τ + 5 * 1728) *
          (ckmrvPhiBasis τ 1 * ModularForm.discriminant τ) +
        (1728 / (kleinModularJ τ - kleinModularJ z) + 6) *
          (ckmrvPhiBasis τ 2 * (ModularForm.E₄ τ * ModularForm.E₆ τ)) ∧
    leechPlusTauCoeff 1 τ z =
      -2 * 1728 / (kleinModularJ τ - kleinModularJ z) *
        (ckmrvPhiBasis τ 1 * ModularForm.discriminant τ) ∧
    leechPlusTauCoeff 2 τ z =
      (1728 / (kleinModularJ τ - kleinModularJ z) - 6) *
          ((τ : ℂ) * (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ)) +
        (12 * kleinModularJ τ - 7 * 1728) *
          (ckmrvPhiBasis τ 1 * ModularForm.discriminant τ) +
        -6 * (ckmrvPhiBasis τ 2 * (ModularForm.E₄ τ * ModularForm.E₆ τ)) := by
  have h8 : ckmrvModularFactor τ 8 = ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ :=
    eisensteinFourteen_eq_four_sq_mul_six τ
  have h7 : ckmrvModularFactor τ 7 = ModularForm.discriminant τ := rfl
  have h6 : ckmrvModularFactor τ 6 = ModularForm.E₄ τ * ModularForm.E₆ τ :=
    eisensteinTen_eq_four_mul_six τ
  have hp0 : ckmrvPhiBasis τ 0 = τ := rfl
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [leechPlusTauCoeff, Fin.sum_univ_three, ckmrvLeechPlusCore, h8, h7, h6, hp0] <;>
    ring

theorem leechPlus_phi_one (τ : ℍ) :
    ckmrvPhiBasis τ 1 = (τ : ℂ) * EisensteinSeries.E2 τ - 3 * Complex.I / (Real.pi : ℂ) :=
  rfl

theorem leechPlus_phi_two (τ : ℍ) :
    ckmrvPhiBasis τ 2 = (τ : ℂ) * EisensteinSeries.E2 τ ^ 2 -
      6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 τ :=
  rfl

/-- The `τ`-part of `X₀`. -/
def leechPlusXP (τ : ℍ) : ℂ :=
  6 * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ -
    12 * EisensteinSeries.E2 τ * ModularForm.E₄ τ ^ 3 +
    8640 * EisensteinSeries.E2 τ * ModularForm.discriminant τ +
    6 * EisensteinSeries.E2 τ ^ 2 * ModularForm.E₄ τ * ModularForm.E₆ τ

/-- The constant part of `X₀` (coefficient of `i/π`). -/
def leechPlusXK (τ : ℍ) : ℂ :=
  36 * ModularForm.E₄ τ ^ 3 - 25920 * ModularForm.discriminant τ -
    36 * EisensteinSeries.E2 τ * ModularForm.E₄ τ * ModularForm.E₆ τ

theorem isBigO_leechPlusXP :
    leechPlusXP =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have h := (((isBigO_mul_q isBigO_leechW isBigO_leechV).trans
    isBigO_exp_neg_four_pi_two_pi).const_mul_left 6).sub
    ((isBigO_tendsto_mul eisensteinTwo_tendsto_one_atImInfty isBigO_discriminant).const_mul_left
      1728)
  refine h.congr_left fun τ => ?_
  rw [leechPlusXP]
  linear_combination (6 * EisensteinSeries.E2 τ) * eisenstein_cubic_square_discriminant τ

theorem isBigO_leechPlusXK :
    leechPlusXK =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have h := ((isBigO_tendsto_mul tendsto_eisensteinFour_atImInfty isBigO_leechW).const_mul_left
    36).sub (isBigO_discriminant.const_mul_left 25920)
  refine h.congr_left fun τ => ?_
  rw [leechPlusXK]
  ring

/-- `X₀ = τ X_P + (i/π) X_K = O(|τ| q)`. -/
theorem isBigO_leechPlusX :
    (fun τ : ℍ => (τ : ℂ) * leechPlusXP τ + Complex.I / (Real.pi : ℂ) * leechPlusXK τ)
      =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) :=
  isBigO_coe_mul_add_const_mul _ isBigO_leechPlusXP isBigO_leechPlusXK

/-- `Y_P = 6 E₄ w (E₄² v - 288 Δ E₂) = O(q²)`. -/
theorem isBigO_leechPlusYP :
    (fun τ : ℍ => 6 * ModularForm.E₄ τ *
      ((ModularForm.E₄ τ ^ 2 - EisensteinSeries.E2 τ * ModularForm.E₆ τ) *
        (ModularForm.E₄ τ ^ 2 *
            (ModularForm.E₆ τ - EisensteinSeries.E2 τ * ModularForm.E₄ τ) -
          288 * (ModularForm.discriminant τ * EisensteinSeries.E2 τ))))
      =O[atImInfty] fun τ : ℍ => Real.exp (-4 * π * τ.im) := by
  have hin := (isBigO_tendsto_mul (tendsto_eisensteinFour_atImInfty.pow 2) isBigO_leechV).sub
    ((isBigO_discriminant.mul (eisensteinTwo_tendsto_one_atImInfty.isBigO_one ℝ)).congr_right
      (fun _ => mul_one _) |>.const_mul_left 288)
  exact isBigO_tendsto_mul (tendsto_eisensteinFour_atImInfty.const_mul 6)
    (isBigO_mul_q isBigO_leechW hin)

/-- `Y_K = 36 (E₄⁴ ρ + Δ (1008 E₄³ (E₄ - 1) + 288 E₄ w)) = O(q²)`. -/
theorem isBigO_leechPlusYK :
    (fun τ : ℍ => 36 * (ModularForm.E₄ τ ^ 4 * leechRho τ +
      ModularForm.discriminant τ * (1008 * (ModularForm.E₄ τ ^ 3 * (ModularForm.E₄ τ - 1)) +
        288 * (ModularForm.E₄ τ *
          (ModularForm.E₄ τ ^ 2 - EisensteinSeries.E2 τ * ModularForm.E₆ τ)))))
      =O[atImInfty] fun τ : ℍ => Real.exp (-4 * π * τ.im) := by
  have hin := ((isBigO_tendsto_mul (tendsto_eisensteinFour_atImInfty.pow 3)
    isBigO_eisensteinFour_sub_one).const_mul_left 1008).add
    ((isBigO_tendsto_mul tendsto_eisensteinFour_atImInfty isBigO_leechW).const_mul_left 288)
  exact ((isBigO_tendsto_mul (tendsto_eisensteinFour_atImInfty.pow 4) isBigO_leechRho).add
    (isBigO_mul_q isBigO_discriminant hin)).const_mul_left 36

theorem isBigO_leechPlusTauCoeff_zero (z : ℍ) :
    (fun τ : ℍ => leechPlusTauCoeff 0 τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
  have hY := isBigO_coe_mul_add_const_mul (Complex.I / (Real.pi : ℂ)) isBigO_leechPlusYP
    isBigO_leechPlusYK
  have hDX := (isBigO_mul_norm_q isBigO_discriminant isBigO_leechPlusX).const_mul_left
    (kleinModularJ z)
  have h := isBigO_tendsto_mul (tendsto_leechPlusK z) (hY.sub hDX)
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_leechPlusK_mul z] with τ hk
  have hinv := kleinModularJ_sub_inv_eq τ z
  have hJ := kleinModularJ_mul_discriminant τ
  have hrel := eisenstein_cubic_square_discriminant τ
  rw [(leechPlusTauCoeff_expand τ z).1]
  simp only [leechPlus_phi_one, leechPlus_phi_two, leechPlusXP, leechPlusXK, leechRho]
  linear_combination
    ((τ : ℂ) * (6 * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ -
        12 * EisensteinSeries.E2 τ * ModularForm.E₄ τ ^ 3 +
        8640 * EisensteinSeries.E2 τ * ModularForm.discriminant τ +
        6 * EisensteinSeries.E2 τ ^ 2 * ModularForm.E₄ τ * ModularForm.E₆ τ) +
      Complex.I / (Real.pi : ℂ) * (36 * ModularForm.E₄ τ ^ 3 -
        25920 * ModularForm.discriminant τ -
        36 * EisensteinSeries.E2 τ * ModularForm.E₄ τ * ModularForm.E₆ τ)) * hk -
      1728 * (((τ : ℂ) * EisensteinSeries.E2 τ ^ 2 -
        6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 τ) *
          ModularForm.E₄ τ * ModularForm.E₆ τ) * hinv +
      6 * leechPlusK z τ * (τ : ℂ) * EisensteinSeries.E2 τ * ModularForm.E₄ τ ^ 3 * hrel +
      12 * ((τ : ℂ) * EisensteinSeries.E2 τ - 3 * Complex.I / (Real.pi : ℂ)) * hJ

theorem isBigO_leechPlusTauCoeff_one (z : ℍ) :
    (fun τ : ℍ => leechPlusTauCoeff 1 τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
  have h := (isBigO_mul_norm_q (isBigO_kleinModularJ_sub_inv z)
    (isBigO_ckmrvPhiBasis_one.mul isBigO_discriminant)).const_mul_left (-2 * 1728 : ℂ)
  refine h.congr_left fun τ => ?_
  rw [(leechPlusTauCoeff_expand τ z).2.1]
  ring

/-- `c₀ + c₂ = 1728 Δ k (τ E₄ (E₄ v - E₂ w) + 6 (i/π) E₄ w + 2 j(z) Δ φ₁) = O(|τ| q²)`. -/
theorem isBigO_leechPlusTauCoeff_zero_add_two (z : ℍ) :
    (fun τ : ℍ => leechPlusTauCoeff 0 τ z + leechPlusTauCoeff 2 τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
  have hA := (isBigO_tendsto_mul tendsto_eisensteinFour_atImInfty
    ((isBigO_tendsto_mul tendsto_eisensteinFour_atImInfty isBigO_leechV).sub
      (isBigO_tendsto_mul eisensteinTwo_tendsto_one_atImInfty isBigO_leechW)))
  have hB := (isBigO_tendsto_mul tendsto_eisensteinFour_atImInfty isBigO_leechW).const_mul_left
    (6 : ℂ)
  have hDφ : (fun τ : ℍ => ModularForm.discriminant τ * ckmrvPhiBasis τ 1) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) :=
    (isBigO_discriminant.mul isBigO_ckmrvPhiBasis_one).congr_right fun _ => mul_comm _ _
  have hin := (isBigO_coe_mul_add_const_mul (Complex.I / (Real.pi : ℂ)) hA hB).add
    (hDφ.const_mul_left (2 * kleinModularJ z))
  have h := ((isBigO_tendsto_mul (tendsto_leechPlusK z)
    (isBigO_mul_norm_q isBigO_discriminant hin)).const_mul_left (1728 : ℂ))
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_leechPlusK_mul z] with τ hk
  have hinv := kleinModularJ_sub_inv_eq τ z
  rw [(leechPlusTauCoeff_expand τ z).1, (leechPlusTauCoeff_expand τ z).2.2]
  simp only [leechPlus_phi_one, leechPlus_phi_two]
  linear_combination
    (-3456 * ModularForm.discriminant τ *
        ((τ : ℂ) * EisensteinSeries.E2 τ - 3 * Complex.I / (Real.pi : ℂ))) * hk +
      (-1728 * ((τ : ℂ) * (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ) +
        ((τ : ℂ) * EisensteinSeries.E2 τ ^ 2 -
          6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 τ) *
            (ModularForm.E₄ τ * ModularForm.E₆ τ))) * hinv

theorem isBigO_leechPlusTauCoeff_two (z : ℍ) :
    (fun τ : ℍ => leechPlusTauCoeff 2 τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) :=
  ((isBigO_leechPlusTauCoeff_zero_add_two z).sub (isBigO_leechPlusTauCoeff_zero z)).congr_left
    fun τ => by ring

theorem isBigO_leechPlusTauCoeff (j : Fin 3) (z : ℍ) :
    (fun τ : ℍ => leechPlusTauCoeff j τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
  fin_cases j
  · exact isBigO_leechPlusTauCoeff_zero z
  · exact isBigO_leechPlusTauCoeff_one z
  · exact isBigO_leechPlusTauCoeff_two z

/-- **CKMRV (4.21), dimension twenty-four, plus kernel.** For fixed `z`,
`K₊(τ, z) = O(|τ| e^{-4π Im τ})` as `Im τ → ∞`. -/
theorem isBigO_ckmrvLeechPlusKernel (z : ℍ) :
    (fun τ : ℍ => ckmrvLeechPlusKernel τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
  have h : (fun τ : ℍ => ∑ j, ((1728 * ckmrvPlusScale * ModularForm.discriminant z)⁻¹ *
      (ckmrvModularFactor z (![3, 2, 1] j) * ckmrvTildePhiBasis z j)) *
        leechPlusTauCoeff j τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-4 * π * τ.im) := by
    simp only [Fin.sum_univ_three]
    exact (((isBigO_leechPlusTauCoeff 0 z).const_mul_left _).add
      ((isBigO_leechPlusTauCoeff 1 z).const_mul_left _)).add
      ((isBigO_leechPlusTauCoeff 2 z).const_mul_left _)
  exact h.congr_left fun τ => (ckmrvLeechPlusKernel_eq_sum τ z).symm

end E8Leech
