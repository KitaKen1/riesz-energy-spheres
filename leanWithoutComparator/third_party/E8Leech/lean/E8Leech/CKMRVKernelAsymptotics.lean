import E8Leech.CKMRVGrowth

/-!
# Cusp asymptotics in `z` of the CKMRV kernels (CKMRV (4.38), dimension eight)

CKMRV §4 expands `K_±(τ, z)` in powers of `e^{πiz}` with coefficients that are functions of `τ`
times polynomials in `z`, and calls `G_±(τ, z)` the sum of the terms `e^{nπiz}` with `n ≤ 0`.
Then `K_±(τ, it) = G_±(τ, it) + O(t² e^{-πt})` as `t → ∞`. In dimension eight
`G^{(8)}_{-1,j,±} = 0`, so `G^{(8)}_±` is the constant term, linear in `z`.

For the minus kernel we use the factorization
`K₋(τ, z) = s⁻¹ D(z)⁻¹ Σ_j c_j(τ) r_j(z) ψ̃_j(z)` with `D(z) = Δ(z) j(τ) - E₄(z)³ → -1`,
`r(z) = (E₄E₆, E₄², E₆)(z) → (1, 1, 1)` and `ψ̃(z) = (L, W, U² - V²)(z) ≈ (πiz + 4 log 2, 1, 1)`.
All deviations decay at least like `e^{-π Im z}`, by the periodicity lemmas of `CKMRVGrowth`.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Decay of the `z`-side factors -/

theorem isBigO_eisensteinFour_sub_one :
    (fun z : ℍ => ModularForm.E₄ z - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h := isBigO_exp_of_periodic (h := 1) one_pos (f := fun z : ℍ => ModularForm.E₄ z - 1)
    ((ModularFormClass.holo ModularForm.E₄).sub mdifferentiable_const)
    (fun z => by
      show ModularForm.E₄ ((1 : ℝ) +ᵥ z) - 1 = ModularForm.E₄ z - 1
      rw [eisensteinFour_vadd_one])
    (by simpa using tendsto_eisensteinFour_atImInfty.sub_const 1)
  simpa using h

theorem isBigO_eisensteinSix_sub_one :
    (fun z : ℍ => ModularForm.E₆ z - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h := isBigO_exp_of_periodic (h := 1) one_pos (f := fun z : ℍ => ModularForm.E₆ z - 1)
    ((ModularFormClass.holo ModularForm.E₆).sub mdifferentiable_const)
    (fun z => by
      show ModularForm.E₆ ((1 : ℝ) +ᵥ z) - 1 = ModularForm.E₆ z - 1
      rw [eisensteinSix_vadd_one])
    (by simpa using tendsto_eisensteinSix_atImInfty.sub_const 1)
  simpa using h

theorem isBigO_exp_neg_two_pi_exp_neg_pi :
    (fun z : ℍ => Real.exp (-2 * π * z.im)) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, Real.exp_le_exp]
  nlinarith [Real.pi_pos, z.im_pos]

theorem isBigO_exp_neg_pi_norm_mul :
    (fun z : ℍ => Real.exp (-π * z.im)) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) :=
  (isBigO_one_real_norm_coe.mul (isBigO_refl _ _)).congr_left fun _ => one_mul _

/-- `f = 1 + O(e^{-2π Im z})` implies `f = O(1)`. -/
theorem isBigO_one_of_sub_one {f : ℍ → ℂ}
    (hf : (fun z : ℍ => f z - 1) =O[atImInfty] fun z : ℍ => Real.exp (-2 * π * z.im)) :
    f =O[atImInfty] fun _ : ℍ => (1 : ℝ) := by
  have h1 : (fun z : ℍ => Real.exp (-2 * π * z.im)) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
    tendsto_exp_neg_two_pi_im.isBigO_one ℝ
  have h := (hf.trans h1).add (isBigO_const_one ℝ (1 : ℂ) atImInfty)
  exact h.congr_left fun z => sub_add_cancel _ _

theorem isBigO_eisensteinFour_mul_eisensteinSix_sub_one :
    (fun z : ℍ => ModularForm.E₄ z * ModularForm.E₆ z - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h6 := isBigO_one_of_sub_one isBigO_eisensteinSix_sub_one
  have h := ((isBigO_eisensteinFour_sub_one.mul h6).congr_right fun z => mul_one _).add
    isBigO_eisensteinSix_sub_one
  refine h.congr_left fun z => ?_
  ring

theorem isBigO_eisensteinFour_sq_sub_one :
    (fun z : ℍ => ModularForm.E₄ z ^ 2 - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h4 : (fun z : ℍ => ModularForm.E₄ z + 1) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
    (isBigO_one_of_sub_one isBigO_eisensteinFour_sub_one).add
      (isBigO_const_one ℝ (1 : ℂ) atImInfty)
  have h := (isBigO_eisensteinFour_sub_one.mul h4).congr_right fun z => mul_one _
  refine h.congr_left fun z => ?_
  ring

theorem isBigO_eisensteinFour_cube_sub_one :
    (fun z : ℍ => ModularForm.E₄ z ^ 3 - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h4 := isBigO_one_of_sub_one isBigO_eisensteinFour_sub_one
  have h := ((isBigO_eisensteinFour_sq_sub_one.mul h4).congr_right fun z => mul_one _).add
    isBigO_eisensteinFour_sub_one
  refine h.congr_left fun z => ?_
  ring

/-! ## Theta quantities and `L` in the cusp variable -/

theorem isBigO_thetaW_sub_one :
    (fun z : ℍ => thetaW z - 1) =O[atImInfty] fun z : ℍ => Real.exp (-π * z.im) :=
  isBigO_exp_half_of_T_sq_invariant (mdifferentiable_thetaW.sub mdifferentiable_const)
    (fun z => by simp only [thetaW_T_T])
    (by simpa using tendsto_thetaW_atImInfty.sub_const 1)

theorem isBigO_thetaU_sq_sub_thetaV_sq_sub_one :
    (fun z : ℍ => (thetaU z ^ 2 - thetaV z ^ 2) - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  refine isBigO_exp_half_of_T_sq_invariant ?_ (fun z => by simp only [thetaU_T_T, thetaV_T_T]) ?_
  · have hfun : (fun z : ℍ => (thetaU z ^ 2 - thetaV z ^ 2) - 1) =
        thetaU * thetaU - thetaV * thetaV - fun _ => (1 : ℂ) := by
      funext z
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    rw [hfun]
    exact ((hU.mul hU).sub (hV.mul hV)).sub mdifferentiable_const
  · have h := ((tendsto_thetaU_atImInfty.pow 2).sub (tendsto_thetaV_atImInfty.pow 2)).sub_const 1
    have h0 : ((1 : ℂ) ^ 2 - 0 ^ 2) - 1 = 0 := by norm_num
    rw [h0] at h
    exact h

theorem ckmrvL_T_T (z : ℍ) :
    ckmrvL (ModularGroup.T • ModularGroup.T • z) = ckmrvL z + 2 * π * I := by
  rw [ckmrvL_T, ckmrvL_T, ckmrvLS_T]
  ring

theorem coe_T_smul_T_smul (z : ℍ) :
    ((ModularGroup.T • ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 2 := by
  rw [← vadd_two_eq_T_smul_T_smul, UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- `L(z) - πiz - 4 log 2 = O(e^{-π Im z})`: the function is `T²`-invariant and tends to `0`. -/
theorem isBigO_ckmrvL_sub_linear :
    (fun z : ℍ => ckmrvL z - π * I * z - 4 * Real.log 2) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) := by
  refine isBigO_exp_half_of_T_sq_invariant ?_ (fun z => ?_) ?_
  · exact (mdifferentiable_ckmrvL.sub (mdifferentiable_const.mul mdifferentiable_coe)).sub
      mdifferentiable_const
  · show ckmrvL (ModularGroup.T • ModularGroup.T • z) -
        π * I * ((ModularGroup.T • ModularGroup.T • z : ℍ) : ℂ) - 4 * Real.log 2 =
      ckmrvL z - π * I * z - 4 * Real.log 2
    rw [ckmrvL_T_T, coe_T_smul_T_smul]
    ring
  · simpa using tendsto_ckmrvL_sub_atImInfty.sub_const (4 * Real.log 2 : ℂ)

theorem isBigO_linear_norm_coe :
    (fun z : ℍ => (π : ℂ) * I * z + 4 * Real.log 2) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ := by
  have h1 : (fun z : ℍ => (π : ℂ) * I * z) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ :=
    (isBigO_coe_norm.const_mul_left ((π : ℂ) * I)).congr_left fun z => by ring
  exact h1.add ((isBigO_const_one ℝ (4 * (Real.log 2 : ℂ)) atImInfty).trans
    isBigO_one_real_norm_coe)

/-! ## The dimension-eight minus kernel as `Im z → ∞` -/

/-- The cusp term `G₋^{(8)}(τ, z)`: the part of `K₋(τ, z)` that does not decay as `Im z → ∞`
(CKMRV (4.38) with `G^{(8)}_{-1,j,-} = 0`). -/
def ckmrvEightMinusG (τ z : ℍ) : ℂ :=
  -ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 τ * (π * I * z + 4 * Real.log 2) +
    eightMinusTauCoeff 1 τ + eightMinusTauCoeff 2 τ)

/-- The `z`-denominator `Δ(z) j(τ) - E₄(z)³`, which tends to `-1`. -/
def eightMinusDenZ (τ z : ℍ) : ℂ :=
  ModularForm.discriminant z * kleinModularJ τ - ModularForm.E₄ z ^ 3

theorem ckmrvEightMinusKernel_eq_z (τ z : ℍ) :
    ckmrvEightMinusKernel τ z = ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ *
      (eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z) +
        eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaW z) +
          eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2))) := by
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have hJ : kleinModularJ z * ModularForm.discriminant z = ModularForm.E₄ z ^ 3 := by
    rw [kleinModularJ]
    field_simp
  have hinv : (kleinModularJ τ - kleinModularJ z)⁻¹ *
      (ckmrvMinusScale * ModularForm.discriminant z)⁻¹ =
        ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ := by
    rw [← mul_inv, ← mul_inv, eightMinusDenZ, ← hJ]
    congr 1
    ring
  have h6 : ckmrvModularFactor z 6 = ModularForm.E₄ z * ModularForm.E₆ z :=
    eisensteinTen_eq_four_mul_six z
  have h5 : ckmrvModularFactor z 5 = ModularForm.E₄ z ^ 2 := eisensteinEight_eq_four_sq z
  have h4 : ckmrvModularFactor z 4 = ModularForm.E₆ z := rfl
  rw [ckmrvEightMinusKernel_eq_sum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, h6, h5, h4, ckmrvTildePsiBasis]
  rw [← hinv]
  ring

theorem isBigO_eightMinusDenZ_add_one (τ : ℍ) :
    (fun z : ℍ => eightMinusDenZ τ z + 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h := (isBigO_discriminant.const_mul_left (kleinModularJ τ)).sub
    isBigO_eisensteinFour_cube_sub_one
  refine h.congr_left fun z => ?_
  simp only [eightMinusDenZ]
  ring

theorem tendsto_eightMinusDenZ (τ : ℍ) :
    Tendsto (fun z : ℍ => eightMinusDenZ τ z) atImInfty (𝓝 (-1)) := by
  have h := ((isBigO_eightMinusDenZ_add_one τ).trans_tendsto tendsto_exp_neg_two_pi_im).sub_const 1
  simpa using h

/-- **CKMRV (4.38), dimension eight, minus kernel.** For fixed `τ`,
`K₋(τ, z) - G₋(τ, z) = O(|z| e^{-π Im z})` as `Im z → ∞`. -/
theorem isBigO_ckmrvEightMinusKernel_sub_G (τ : ℍ) :
    (fun z : ℍ => ckmrvEightMinusKernel τ z - ckmrvEightMinusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
  set c0 := eightMinusTauCoeff 0 τ
  set c1 := eightMinusTauCoeff 1 τ
  set c2 := eightMinusTauCoeff 2 τ
  -- `D⁻¹ = O(1)` and `D⁻¹ + 1 = O(e^{-2π Im z})`.
  have hD := tendsto_eightMinusDenZ τ
  have hDinv : (fun z : ℍ => (eightMinusDenZ τ z)⁻¹) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
    (hD.inv₀ (by norm_num)).isBigO_one ℝ
  have hDne : ∀ᶠ z : ℍ in atImInfty, eightMinusDenZ τ z ≠ 0 :=
    hD.eventually_ne (by norm_num)
  have hDinv1 : (fun z : ℍ => (eightMinusDenZ τ z)⁻¹ + 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
    have h := ((isBigO_eightMinusDenZ_add_one τ).mul hDinv).congr_right fun z => mul_one _
    refine h.congr' ?_ (Eventually.of_forall fun z => rfl)
    filter_upwards [hDne] with z hz
    field_simp
    ring
  -- The sum and its cusp value.
  have hr0 := isBigO_one_of_sub_one isBigO_eisensteinFour_mul_eisensteinSix_sub_one
  have hr1 := isBigO_one_of_sub_one isBigO_eisensteinFour_sq_sub_one
  have hr2 := isBigO_one_of_sub_one isBigO_eisensteinSix_sub_one
  have hA : (fun z : ℍ => ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z -
      ((π : ℂ) * I * z + 4 * Real.log 2)) =O[atImInfty]
        fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
    have h1 := ((hr0.mul isBigO_ckmrvL_sub_linear).congr_right fun z => one_mul _).trans
      isBigO_exp_neg_pi_norm_mul
    have h2 := (((isBigO_eisensteinFour_mul_eisensteinSix_sub_one.trans
      isBigO_exp_neg_two_pi_exp_neg_pi).mul isBigO_linear_norm_coe).congr_right fun z =>
        mul_comm _ _)
    exact (h1.add h2).congr_left fun z => by ring
  have hB : (fun z : ℍ => ModularForm.E₄ z ^ 2 * thetaW z - 1) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
    have h1 := (hr1.mul isBigO_thetaW_sub_one).congr_right fun z => one_mul _
    have h2 := isBigO_eisensteinFour_sq_sub_one.trans isBigO_exp_neg_two_pi_exp_neg_pi
    exact ((h1.add h2).congr_left fun z => by ring).trans isBigO_exp_neg_pi_norm_mul
  have hC : (fun z : ℍ => ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2) - 1) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
    have h1 := (hr2.mul isBigO_thetaU_sq_sub_thetaV_sq_sub_one).congr_right fun z => one_mul _
    have h2 := isBigO_eisensteinSix_sub_one.trans isBigO_exp_neg_two_pi_exp_neg_pi
    exact ((h1.add h2).congr_left fun z => by ring).trans isBigO_exp_neg_pi_norm_mul
  have hdiff := ((hA.const_mul_left c0).add (hB.const_mul_left c1)).add (hC.const_mul_left c2)
  have hS0 : (fun z : ℍ => c0 * ((π : ℂ) * I * z + 4 * Real.log 2) + c1 + c2) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ :=
    ((isBigO_linear_norm_coe.const_mul_left c0).add
      ((isBigO_const_one ℝ c1 atImInfty).trans isBigO_one_real_norm_coe)).add
      ((isBigO_const_one ℝ c2 atImInfty).trans isBigO_one_real_norm_coe)
  have hT1 := (hDinv.mul hdiff).congr_right fun z => one_mul _
  have hT2 := ((hDinv1.mul hS0).congr_right fun z => mul_comm _ _).trans
    ((isBigO_refl (fun z : ℍ => ‖(z : ℂ)‖) atImInfty).mul isBigO_exp_neg_two_pi_exp_neg_pi)
  have h := ((hT1.add hT2).const_mul_left ckmrvMinusScale⁻¹)
  refine h.congr_left fun z => ?_
  rw [ckmrvEightMinusKernel_eq_z, ckmrvEightMinusG]
  ring

/-! ## The dimension-eight plus kernel as `Im z → ∞` -/

theorem isBigO_eisensteinTwo_sub_one :
    (fun z : ℍ => EisensteinSeries.E2 z - 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h := isBigO_exp_of_periodic (h := 1) one_pos (f := fun z : ℍ => EisensteinSeries.E2 z - 1)
    (E2_mdifferentiable.sub mdifferentiable_const)
    (fun z => by
      show EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) - 1 = EisensteinSeries.E2 z - 1
      rw [eisensteinTwo_vadd_one])
    (by simpa using eisensteinTwo_tendsto_one_atImInfty.sub_const 1)
  simpa using h

theorem eventually_one_le_norm_coe_sq :
    ∀ᶠ z : ℍ in atImInfty, ‖(z : ℂ)‖ ≤ ‖(z : ℂ)‖ ^ 2 := by
  filter_upwards [eventually_one_le_norm_coe] with z hz
  nlinarith

theorem isBigO_norm_coe_sq : (fun z : ℍ => ‖(z : ℂ)‖) =O[atImInfty]
    fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_norm_coe_sq] with z hz
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hz

theorem isBigO_coe_sq : (fun z : ℍ => (z : ℂ) ^ 2) =O[atImInfty]
    fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by simp)

/-- A polynomial `α z² + β z + γ` in `z` is `O(|z|²)`. -/
theorem isBigO_quadratic (α β γ : ℂ) :
    (fun z : ℍ => α * (z : ℂ) ^ 2 + β * z + γ) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
  ((isBigO_coe_sq.const_mul_left α).add
    ((isBigO_coe_norm.trans isBigO_norm_coe_sq).const_mul_left β)).add
    (((isBigO_const_one ℝ γ atImInfty).trans isBigO_one_real_norm_coe).trans isBigO_norm_coe_sq)

/-- The cusp term `G₊^{(8)}(τ, z)`: with `a = φ₁(τ) E₄(τ)` and `b = τ E₆(τ)`,
`G₊ = s⁻¹ ((12 i/π)(b - a) z + 36 b/π²)`; the `z²` terms cancel. -/
def ckmrvEightPlusG (τ z : ℍ) : ℂ :=
  ckmrvPlusScale⁻¹ *
    (12 * (Complex.I / (Real.pi : ℂ)) *
        (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) * z +
      36 / (Real.pi : ℂ) ^ 2 * (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ))

theorem eightPlusTauCoeff_zero' (τ z : ℍ) :
    eightPlusTauCoeff 0 τ z = (kleinModularJ τ - kleinModularJ z) *
        (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)) +
      ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 := by
  have h3 : ckmrvModularFactor τ 3 = ModularForm.E₄ τ := rfl
  have h4 : ckmrvModularFactor τ 4 = ModularForm.E₆ τ := rfl
  simp [eightPlusTauCoeff, Fin.sum_univ_three, ckmrvEightPlusCore, h3, h4]
  ring

theorem ckmrvEightPlusKernel_eq_z (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    ckmrvEightPlusKernel τ z = ckmrvPlusScale⁻¹ *
      ((ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)) *
          (z : ℂ) ^ 2 +
        ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 * ModularForm.discriminant z * (z : ℂ) ^ 2 *
          (eightMinusDenZ τ z)⁻¹ +
        (eightMinusDenZ τ z)⁻¹ *
          (-2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
              (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1) +
            ckmrvPhiBasis τ 0 * ModularForm.E₆ τ *
              (ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2))) := by
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have hJ : kleinModularJ z * ModularForm.discriminant z = ModularForm.E₄ z ^ 3 := by
    rw [kleinModularJ]
    field_simp
  have hD : eightMinusDenZ τ z =
      ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z) := by
    rw [eightMinusDenZ, ← hJ]
    ring
  have h7 : ckmrvModularFactor z 7 = ModularForm.discriminant z := rfl
  have h6 : ckmrvModularFactor z 6 = ModularForm.E₄ z * ModularForm.E₆ z :=
    eisensteinTen_eq_four_mul_six z
  have h5 : ckmrvModularFactor z 5 = ModularForm.E₄ z ^ 2 := eisensteinEight_eq_four_sq z
  have ht0 : ckmrvTildePhiBasis z 0 = (z : ℂ) ^ 2 := rfl
  have hc1 := eightPlusTauCoeff_one τ z
  have hc2 := eightPlusTauCoeff_two τ z
  have hp0 : ckmrvPhiBasis τ 0 = (τ : ℂ) := rfl
  rw [ckmrvEightPlusKernel_eq_sum, hD]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, h7, h6, h5, ht0, eightPlusTauCoeff_zero', hc1, hc2, hp0]
  have hs := ckmrvPlusScale_ne_zero
  field_simp
  ring

theorem tendsto_kleinModularJ_sub_ne (τ : ℍ) :
    ∀ᶠ z : ℍ in atImInfty, kleinModularJ τ - kleinModularJ z ≠ 0 := by
  have hD := tendsto_eightMinusDenZ τ
  filter_upwards [hD.eventually_ne (by norm_num : (-1 : ℂ) ≠ 0)] with z hz
  intro h0
  apply hz
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have hJ : kleinModularJ z * ModularForm.discriminant z = ModularForm.E₄ z ^ 3 := by
    rw [kleinModularJ]
    field_simp
  rw [eightMinusDenZ, ← hJ]
  linear_combination ModularForm.discriminant z * h0

/-- **CKMRV (4.38), dimension eight, plus kernel.** For fixed `τ`,
`K₊(τ, z) - G₊(τ, z) = O(|z|² e^{-2π Im z})` as `Im z → ∞`. -/
theorem isBigO_ckmrvEightPlusKernel_sub_G (τ : ℍ) :
    (fun z : ℍ => ckmrvEightPlusKernel τ z - ckmrvEightPlusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
  set a := ckmrvPhiBasis τ 1 * ModularForm.E₄ τ
  set b := ckmrvPhiBasis τ 0 * ModularForm.E₆ τ
  set F := ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2
  have hD := tendsto_eightMinusDenZ τ
  have hDinv : (fun z : ℍ => (eightMinusDenZ τ z)⁻¹) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
    (hD.inv₀ (by norm_num)).isBigO_one ℝ
  have hDne : ∀ᶠ z : ℍ in atImInfty, eightMinusDenZ τ z ≠ 0 :=
    hD.eventually_ne (by norm_num)
  have hDinv1 : (fun z : ℍ => (eightMinusDenZ τ z)⁻¹ + 1) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
    have h := ((isBigO_eightMinusDenZ_add_one τ).mul hDinv).congr_right fun z => mul_one _
    refine h.congr' ?_ (Eventually.of_forall fun z => rfl)
    filter_upwards [hDne] with z hz
    field_simp
    ring
  -- the `z`-side factors
  have hp1 : (fun z : ℍ => ckmrvTildePhiBasis z 1 - ((z : ℂ) ^ 2 -
      6 * (Complex.I / (Real.pi : ℂ)) * z)) =O[atImInfty]
        fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
    have h := (isBigO_coe_sq.mul isBigO_eisensteinTwo_sub_one)
    refine h.congr_left fun z => ?_
    have h1 : ckmrvTildePhiBasis z 1 = (z : ℂ) ^ 2 * EisensteinSeries.E2 z -
        6 * Complex.I / (Real.pi : ℂ) * (z : ℂ) := rfl
    rw [h1]
    ring
  have hp2 : (fun z : ℍ => ckmrvTildePhiBasis z 2 - ((z : ℂ) ^ 2 -
      12 * (Complex.I / (Real.pi : ℂ)) * z - 36 / (Real.pi : ℂ) ^ 2)) =O[atImInfty]
        fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
    have hE2 : (fun z : ℍ => EisensteinSeries.E2 z + 1) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
      (isBigO_one_of_sub_one isBigO_eisensteinTwo_sub_one).add
        (isBigO_const_one ℝ (1 : ℂ) atImInfty)
    have h1 := isBigO_coe_sq.mul
      ((isBigO_eisensteinTwo_sub_one.mul hE2).congr_right fun z => mul_one _)
    have h2 := ((isBigO_coe_norm.trans isBigO_norm_coe_sq).mul
      isBigO_eisensteinTwo_sub_one).const_mul_left (-(12 * (Complex.I / (Real.pi : ℂ))))
    refine (h1.add (h2.trans (isBigO_refl _ _))).congr_left fun z => ?_
    have h2' : ckmrvTildePhiBasis z 2 = (z : ℂ) ^ 2 * EisensteinSeries.E2 z ^ 2 -
        12 * Complex.I / (Real.pi : ℂ) * (z : ℂ) * EisensteinSeries.E2 z -
          36 / (Real.pi : ℂ) ^ 2 := rfl
    rw [h2']
    ring
  have hq1 : (fun z : ℍ => (z : ℂ) ^ 2 - 6 * (Complex.I / (Real.pi : ℂ)) * z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
    (isBigO_quadratic 1 (-(6 * (Complex.I / (Real.pi : ℂ)))) 0).congr_left fun z => by ring
  have hq2 : (fun z : ℍ => (z : ℂ) ^ 2 - 12 * (Complex.I / (Real.pi : ℂ)) * z -
      36 / (Real.pi : ℂ) ^ 2) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
    (isBigO_quadratic 1 (-(12 * (Complex.I / (Real.pi : ℂ)))) (-(36 / (Real.pi : ℂ) ^ 2))).congr_left
      fun z => by ring
  -- `E₄E₆ φ̃₁ - φ̃₁⁰` and `E₄² φ̃₂ - φ̃₂⁰`
  have hr1 := isBigO_one_of_sub_one isBigO_eisensteinFour_mul_eisensteinSix_sub_one
  have hr2 := isBigO_one_of_sub_one isBigO_eisensteinFour_sq_sub_one
  have hA : (fun z : ℍ => ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1 -
      ((z : ℂ) ^ 2 - 6 * (Complex.I / (Real.pi : ℂ)) * z)) =O[atImInfty]
        fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
    have h1 := (hr1.mul hp1).congr_right fun z => one_mul _
    have h2 := (isBigO_eisensteinFour_mul_eisensteinSix_sub_one.mul hq1).congr_right
      fun z => mul_comm _ _
    exact (h1.add h2).congr_left fun z => by ring
  have hB : (fun z : ℍ => ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2 -
      ((z : ℂ) ^ 2 - 12 * (Complex.I / (Real.pi : ℂ)) * z - 36 / (Real.pi : ℂ) ^ 2))
        =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
    have h1 := (hr2.mul hp2).congr_right fun z => one_mul _
    have h2 := (isBigO_eisensteinFour_sq_sub_one.mul hq2).congr_right fun z => mul_comm _ _
    exact (h1.add h2).congr_left fun z => by ring
  -- assemble: `K - G = s⁻¹ (F Δ z² D⁻¹ + D⁻¹ (P - P₀) + (D⁻¹ + 1) P₀)`
  have hP0 : (fun z : ℍ => -2 * a * ((z : ℂ) ^ 2 - 6 * (Complex.I / (Real.pi : ℂ)) * z) +
      b * ((z : ℂ) ^ 2 - 12 * (Complex.I / (Real.pi : ℂ)) * z - 36 / (Real.pi : ℂ) ^ 2))
        =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
    (hq1.const_mul_left (-2 * a)).add (hq2.const_mul_left b)
  have hT1 := ((((isBigO_discriminant.mul isBigO_coe_sq).mul hDinv).congr_right
    fun z => (mul_one _).trans (mul_comm _ _)).const_mul_left F)
  have hT2 := (hDinv.mul ((hA.const_mul_left (-2 * a)).add (hB.const_mul_left b))).congr_right
    fun z => one_mul _
  have hT3 := (hDinv1.mul hP0).congr_right fun z => mul_comm _ _
  have h := ((hT1.add hT2).add hT3).const_mul_left ckmrvPlusScale⁻¹
  refine h.congr' ?_ (Eventually.of_forall fun z => rfl)
  filter_upwards [tendsto_kleinModularJ_sub_ne τ] with z hg
  rw [ckmrvEightPlusKernel_eq_z τ z hg, ckmrvEightPlusG]
  have hp0 : ckmrvPhiBasis τ 0 = (τ : ℂ) := rfl
  ring

end E8Leech
