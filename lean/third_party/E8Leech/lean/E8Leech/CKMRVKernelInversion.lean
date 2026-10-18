import E8Leech.CKMRVKernelAsymptoticsLeech

/-!
# The kernels under `z ↦ -1/z` (CKMRV Lemma 4.11, the `z`-variable)

For fixed `τ`, as `Im z → ∞`,
`(K±⁽ᵈ⁾ ∣_{2-d/2} S)(τ, z) = O(e^{-π n± Im z})` with `n₋ = 1` and `n₊ = 2` (the exponents
`n_{±,z}` of CKMRV (4.39)). Equivalently `K(τ, it)` decays like `e^{-π n± / t}` as `t → 0`,
which is what the Laplace representation (5.1) needs at `t → 0`.

The `z`-side factors are level one, so `z ↦ -1/z` only replaces the basis `ψ̃ = (L, W, U² - V²)`
by `(L_S, -V, U² - W²)` and `φ̃` by `(1, E₂, E₂²)`:
* `K₋⁽⁸⁾ ∣ S = (2·1728π)⁻¹ D⁻¹ (c₀ E₁₀ L_S - c₁ E₈ V + c₂ E₆ (U² - W²))`, each term `O(s)`;
* `K₊⁽⁸⁾ ∣ S = c₊⁻¹ ((a₀ - 2a₁) + D⁻¹ Y)`, whose constant term cancels;
* `K₋⁽²⁴⁾ ∣ S = (2·1728π)⁻¹ (D Δ)⁻¹ N^S` with `N^S = O(|s|³)`;
* `K₊⁽²⁴⁾ ∣ S = (1728 c₊)⁻¹ (D Δ)⁻¹ Ñ₂`, where `Ñ₂` is the `z²`-numerator of (4.38) and is
  `O(q²)` because it is `T`-invariant with vanishing second-order expansion.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Level-one factors at `-1/z` -/

theorem eisensteinFour_S (z : ℍ) :
    ModularForm.E₄ (ModularGroup.S • z) = (z : ℂ) ^ 4 * ModularForm.E₄ z := by
  simpa only [zpow_ofNat] using levelOne_S ModularForm.E₄ z

theorem eisensteinSix_S (z : ℍ) :
    ModularForm.E₆ (ModularGroup.S • z) = (z : ℂ) ^ 6 * ModularForm.E₆ z := by
  simpa only [zpow_ofNat] using levelOne_S ModularForm.E₆ z

theorem eightMinusDenZ_S (τ z : ℍ) :
    eightMinusDenZ τ (ModularGroup.S • z) = (z : ℂ) ^ 12 * eightMinusDenZ τ z := by
  simp only [eightMinusDenZ, discriminant_S, eisensteinFour_S]
  ring

theorem ckmrvTildePhiBasis_S_one (z : ℍ) :
    ckmrvTildePhiBasis (ModularGroup.S • z) 1 = EisensteinSeries.E2 z := by
  have h := ckmrvTildePhiBasis_S_weighted z 1
  have hw : ckmrvPhiWeight 1 = 0 := rfl
  rw [hw, neg_zero, zpow_zero, mul_one] at h
  exact h

theorem ckmrvTildePhiBasis_S_two (z : ℍ) :
    ckmrvTildePhiBasis (ModularGroup.S • z) 2 = (z : ℂ) ^ 2 * EisensteinSeries.E2 z ^ 2 := by
  have h := ckmrvTildePhiBasis_S_weighted z 2
  have hw : ckmrvPhiWeight 2 = 2 := rfl
  rw [hw, zpow_neg, zpow_ofNat] at h
  have hz2 : (z : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 z.ne_zero
  calc ckmrvTildePhiBasis (ModularGroup.S • z) 2
      = (z : ℂ) ^ 2 * (ckmrvTildePhiBasis (ModularGroup.S • z) 2 * ((z : ℂ) ^ 2)⁻¹) := by
        rw [mul_comm, mul_assoc, inv_mul_cancel₀ hz2, mul_one]
    _ = (z : ℂ) ^ 2 * EisensteinSeries.E2 z ^ 2 := by rw [h]; rfl

theorem coe_pow_mul_inv_pow (z : ℍ) (k : ℕ) : (z : ℂ) ^ k * ((z : ℂ)⁻¹) ^ k = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ z.ne_zero, one_pow]

/-- `(j(τ) - j(z))⁻¹ = Δ(z) D(z)⁻¹` with `D(z) = Δ(z) j(τ) - E₄(z)³`. -/
theorem kleinModularJ_sub_inv_eq_z (τ z : ℍ) :
    (kleinModularJ τ - kleinModularJ z)⁻¹ =
      ModularForm.discriminant z * (eightMinusDenZ τ z)⁻¹ := by
  have hΔ : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have h : kleinModularJ τ - kleinModularJ z =
      eightMinusDenZ τ z / ModularForm.discriminant z := by
    rw [eq_div_iff hΔ, eightMinusDenZ, sub_mul, kleinModularJ_mul_discriminant]
    ring
  rw [h, inv_div, div_eq_mul_inv]

/-! ## Expansions used below -/

/-- `f = O(e^{-π Im z})` when the constant term of its expansion vanishes. -/
theorem HasExp3.isBigO_exp_neg_pi {f : ℍ → ℂ} {b c : ℂ} (hf : HasExp3 f 0 b c) :
    f =O[atImInfty] fun z : ℍ => Real.exp (-π * z.im) := by
  have hs : (fun z : ℍ => ‖cuspS z‖) =O[atImInfty] fun z : ℍ => Real.exp (-π * z.im) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [norm_cuspS, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul])
  have h3 : (fun z : ℍ => ‖cuspS z‖ ^ 3) =O[atImInfty] fun z : ℍ => ‖cuspS z‖ :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (norm_nonneg _), one_mul]
      exact pow_le_of_le_one (norm_nonneg _) (norm_cuspS_le_one z) (by norm_num))
  have hlin : (fun z : ℍ => b * cuspS z + c * cuspS z ^ 2) =O[atImInfty]
      fun z : ℍ => ‖cuspS z‖ :=
    IsBigO.of_bound (‖b‖ + ‖c‖) (Eventually.of_forall fun z => by
      have h1 := norm_cuspS_le_one z
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      calc ‖b * cuspS z + c * cuspS z ^ 2‖ ≤ ‖b‖ * ‖cuspS z‖ + ‖c‖ * ‖cuspS z‖ ^ 2 := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_pow]
        _ ≤ ‖b‖ * ‖cuspS z‖ + ‖c‖ * ‖cuspS z‖ := by
            gcongr
            exact pow_le_of_le_one (norm_nonneg _) h1 (by norm_num)
        _ = (‖b‖ + ‖c‖) * ‖cuspS z‖ := by ring)
  exact ((IsBigO.trans hf h3).add hlin).congr_left (fun z => by ring) |>.trans hs

theorem hasExp3_thetaU_sq_sub_thetaW_sq :
    HasExp3 (fun z : ℍ => thetaU z ^ 2 - thetaW z ^ 2) 0 32 0 :=
  (hasExp3_thetaU.pow.sub hasExp3_thetaW.pow).congr_coeff (by norm_num) (by norm_num)
    (by norm_num)

theorem hasExp3_eightMinusDenZ_inv (τ : ℍ) :
    HasExp3 (fun z => (eightMinusDenZ τ z)⁻¹) (-1) 0 (720 - kleinModularJ τ) :=
  ((hasExp3_eightMinusDenZ τ).inv (by norm_num)).congr_coeff (by ring) (by ring) (by ring)

theorem isBigO_eightMinusDenZ_inv (τ : ℍ) :
    (fun z : ℍ => (eightMinusDenZ τ z)⁻¹) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
  ((tendsto_eightMinusDenZ τ).inv₀ (by norm_num)).isBigO_one ℝ

/-- A holomorphic `T`-invariant function with vanishing second-order expansion is `O(q²)`. -/
theorem isBigO_q_sq_of_hasExp3 {f : ℍ → ℂ} (hf : MDiff f)
    (hper : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (h3 : HasExp3 f 0 0 0) :
    f =O[atImInfty] fun τ : ℍ => Real.exp (-4 * π * τ.im) := by
  have hg := isBigO_q_of_vadd (f := fun τ => f τ / ModularForm.discriminant τ)
    (hf.div mdifferentiable_modularDiscriminant ModularForm.discriminant_ne_zero)
    (fun τ => by simp only [hper, discriminant_vadd_one])
    (tendsto_zero_of_mul_discriminant (h3.congr_fun fun τ =>
      (div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)).symm))
  exact (isBigO_mul_q hg isBigO_discriminant).congr_left fun τ =>
    div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)

/-! ## Dimension eight, minus kernel -/

theorem ckmrvEightMinusKernel_S_right (τ z : ℍ) :
    ckmrvEightMinusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 2 =
      ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ *
        (eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvLS z) -
          eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaV z) +
          eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2))) := by
  have h12 := coe_pow_mul_inv_pow z 12
  rw [ckmrvEightMinusKernel_eq_z]
  simp only [eightMinusDenZ_S, eisensteinFour_S, eisensteinSix_S, ckmrvL_S, thetaU_S, thetaV_S,
    thetaW_S]
  linear_combination (ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ *
    (eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvLS z) -
      eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaV z) +
      eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2)))) * h12

/-- **CKMRV (4.39), `d = 8`, minus kernel.** `(K₋ ∣_{-2} S)(τ, z) = O(e^{-π Im z})`. -/
theorem isBigO_ckmrvEightMinusKernel_S_right (τ : ℍ) :
    (fun z : ℍ => ckmrvEightMinusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 2) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) := by
  have hV : thetaV =O[atImInfty] fun z : ℍ => Real.exp (-π * z.im) :=
    hasExp3_thetaV.isBigO_exp_neg_pi
  have hUW := hasExp3_thetaU_sq_sub_thetaW_sq.isBigO_exp_neg_pi
  have hX := (((isBigO_tendsto_mul
      (tendsto_eisensteinFour_atImInfty.mul tendsto_eisensteinSix_atImInfty)
      isBigO_ckmrvLS).const_mul_left (eightMinusTauCoeff 0 τ)).sub
    ((isBigO_tendsto_mul (tendsto_eisensteinFour_atImInfty.pow 2) hV).const_mul_left
      (eightMinusTauCoeff 1 τ))).add
    ((isBigO_tendsto_mul tendsto_eisensteinSix_atImInfty hUW).const_mul_left
      (eightMinusTauCoeff 2 τ))
  have h := (((isBigO_eightMinusDenZ_inv τ).mul hX).congr_right fun _ => one_mul _).const_mul_left
    ckmrvMinusScale⁻¹
  refine h.congr_left fun z => ?_
  rw [ckmrvEightMinusKernel_S_right]
  ring

/-! ## Dimension eight, plus kernel -/

theorem ckmrvEightPlusKernel_S_right (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    ckmrvEightPlusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 2 =
      ckmrvPlusScale⁻¹ *
        ((ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)) +
          (eightMinusDenZ τ z)⁻¹ *
            (ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 * ModularForm.discriminant z -
              2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
                (ModularForm.E₄ z * ModularForm.E₆ z * EisensteinSeries.E2 z) +
              ckmrvPhiBasis τ 0 * ModularForm.E₆ τ *
                (ModularForm.E₄ z ^ 2 * EisensteinSeries.E2 z ^ 2))) := by
  have h2 := coe_pow_mul_inv_pow z 2
  have h12 := coe_pow_mul_inv_pow z 12
  have h14 := coe_pow_mul_inv_pow z 14
  rw [ckmrvEightPlusKernel_eq_z τ (ModularGroup.S • z) (by rwa [kleinModularJ_S])]
  simp only [eightMinusDenZ_S, discriminant_S, eisensteinFour_S, eisensteinSix_S, coe_S_smul,
    ckmrvTildePhiBasis_S_one, ckmrvTildePhiBasis_S_two]
  linear_combination
    (ckmrvPlusScale⁻¹ *
      (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))) * h2 +
    (ckmrvPlusScale⁻¹ * ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 * ModularForm.discriminant z *
      (eightMinusDenZ τ z)⁻¹) * h14 +
    (ckmrvPlusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ *
      (-2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
          (ModularForm.E₄ z * ModularForm.E₆ z * EisensteinSeries.E2 z) +
        ckmrvPhiBasis τ 0 * ModularForm.E₆ τ *
          (ModularForm.E₄ z ^ 2 * EisensteinSeries.E2 z ^ 2))) * h12

/-- **CKMRV (4.39), `d = 8`, plus kernel.** `(K₊ ∣_{-2} S)(τ, z) = O(e^{-2π Im z})`. -/
theorem isBigO_ckmrvEightPlusKernel_S_right (τ : ℍ) :
    (fun z : ℍ => ckmrvEightPlusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 2) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have hY := ((hasExp3_discriminant.const_mul (ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2)).sub
      (((hasExp3_eisensteinFour.mul hasExp3_eisensteinSix).mul hasExp3_eisensteinTwo).const_mul
        (2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)))).add
    ((hasExp3_eisensteinFour.pow.mul hasExp3_eisensteinTwo.pow).const_mul
      (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ))
  have hf := (HasExp3.const (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ -
    2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))).add ((hasExp3_eightMinusDenZ_inv τ).mul hY)
  have hf' := hf.congr_coeff (a' := 0) (b' := 0) (by ring) (by ring) rfl
  have h := ((hf'.isBigO_sq.congr_right fun z => (exp_neg_two_pi_eq_norm_cuspS_sq z).symm)
    ).const_mul_left ckmrvPlusScale⁻¹
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [tendsto_kleinModularJ_sub_ne τ] with z hz
  rw [ckmrvEightPlusKernel_S_right τ z hz]

/-! ## The Leech minus kernel -/

/-- The numerator of `K₋⁽²⁴⁾ ∣ S`. -/
def leechMinusNS (τ z : ℍ) : ℂ :=
  -(2 * 1728) * ModularForm.discriminant τ *
      (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvLS z) -
    thetaV z * (eightMinusDenZ τ z * leechMinusBeta τ +
      ModularForm.discriminant z * leechMinusGamma τ) -
    leechMinusAlpha τ * (ModularForm.E₄ z * ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2))

theorem ckmrvLeechMinusKernel_S_right (τ z : ℍ) :
    ckmrvLeechMinusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 10 =
      ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ * (ModularForm.discriminant z)⁻¹ *
        leechMinusNS τ z := by
  have h24 := coe_pow_mul_inv_pow z 24
  rw [ckmrvLeechMinusKernel_eq_z]
  simp only [leechMinusNEll, leechMinusNZero, ckmrvEll, eightMinusDenZ_S, discriminant_S,
    eisensteinFour_S, eisensteinSix_S, ckmrvL_S, thetaU_S, thetaV_S, thetaW_S, coe_S_smul]
  linear_combination (norm := (simp only [leechMinusNS]; ring1))
    (ckmrvMinusScale⁻¹ * (eightMinusDenZ τ z)⁻¹ * (ModularForm.discriminant z)⁻¹ *
      leechMinusNS τ z) * h24

theorem hasExp3_leechMinusNS (τ : ℍ) : HasExp3 (fun z => leechMinusNS τ z) 0 0 0 :=
  ((((hasExp3_eisensteinFourteen.mul hasExp3_ckmrvLS).const_mul
      (-(2 * 1728) * ModularForm.discriminant τ)).sub
    (hasExp3_thetaV.mul (((hasExp3_eightMinusDenZ τ).mul (HasExp3.const (leechMinusBeta τ))).add
      (hasExp3_discriminant.mul (HasExp3.const (leechMinusGamma τ)))))).sub
    ((hasExp3_eisensteinTen.mul hasExp3_thetaU_sq_sub_thetaW_sq).const_mul
      (leechMinusAlpha τ))).congr_fun (fun z => rfl)
    |>.congr_coeff (by ring) (by simp only [leechMinusBeta]; ring) (by ring)

/-- **CKMRV (4.39), Leech minus kernel.** `(K₋ ∣_{-10} S)(τ, z) = O(e^{-π Im z})`. -/
theorem isBigO_ckmrvLeechMinusKernel_S_right (τ : ℍ) :
    (fun z : ℍ => ckmrvLeechMinusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 10) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) := by
  have hX := ((hasExp3_leechDenInv τ).mul (hasExp3_leechMinusNS τ)).congr_coeff
    (a' := 0) (b' := 0) (c' := 0) (by ring) (by ring) (by ring)
  have hX' : (fun z => (eightMinusDenZ τ z * discriminantCuspQuot z)⁻¹ * leechMinusNS τ z)
      =O[atImInfty] fun z : ℍ => (fun _ : ℍ => (1 : ℝ)) z * ‖cuspS z‖ ^ 3 :=
    (HasExp3.isBigO_cube hX).congr_right fun _ => (one_mul _).symm
  have h := ((isBigO_cuspS_sq_inv_mul (w := fun _ => (1 : ℝ)) hX').congr_right
    fun _ => one_mul _).const_mul_left
    ckmrvMinusScale⁻¹
  refine h.congr_left fun z => ?_
  have hu : (ModularForm.discriminant z)⁻¹ = (cuspS z ^ 2)⁻¹ * (discriminantCuspQuot z)⁻¹ := by
    rw [discriminant_eq_cuspS_sq_mul, mul_inv]
  rw [ckmrvLeechMinusKernel_S_right, hu]
  ring

/-! ## The Leech plus kernel -/

/-- `A₂ = p₀ E₄ + p₂ E₂²`. -/
def leechPlusA2z (τ z : ℍ) : ℂ :=
  leechPlusP0 τ * ModularForm.E₄ z + leechPlusP2 τ * EisensteinSeries.E2 z ^ 2

/-- `B₂`, the `(DΔ)⁻¹` part of the `z²`-coefficient in (4.38). -/
def leechPlusB2z (τ z : ℍ) : ℂ :=
  1728 * leechPlusA2 τ * (ModularForm.E₄ z * ModularForm.discriminant z) -
    2 * 1728 * leechPlusA1 τ * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * EisensteinSeries.E2 z) +
    1728 * leechPlusA0 τ * (EisensteinSeries.E2 z ^ 2 * ModularForm.discriminant z)

theorem ckmrvLeechPlusKernel_S_right (τ z : ℍ) :
    ckmrvLeechPlusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 10 =
      (1728 * ckmrvPlusScale)⁻¹ * ((ModularForm.discriminant z)⁻¹ * leechPlusA2z τ z +
        (eightMinusDenZ τ z)⁻¹ * (ModularForm.discriminant z)⁻¹ * leechPlusB2z τ z) := by
  have h12 := coe_pow_mul_inv_pow z 12
  have h14 := coe_pow_mul_inv_pow z 14
  have h24 := coe_pow_mul_inv_pow z 24
  have h26 := coe_pow_mul_inv_pow z 26
  rw [ckmrvLeechPlusKernel_eq_z]
  simp only [leechPlusAz, leechPlusBz, leechPlusA2z, leechPlusB2z, eightMinusDenZ_S,
    discriminant_S, eisensteinFour_S, eisensteinSix_S, coe_S_smul, ckmrvTildePhiBasis_S_one,
    ckmrvTildePhiBasis_S_two]
  linear_combination
    ((1728 * ckmrvPlusScale)⁻¹ * (ModularForm.discriminant z)⁻¹ * leechPlusP0 τ *
      ModularForm.E₄ z) * h14 +
    ((1728 * ckmrvPlusScale)⁻¹ * (ModularForm.discriminant z)⁻¹ * leechPlusP2 τ *
      EisensteinSeries.E2 z ^ 2) * h12 +
    ((1728 * ckmrvPlusScale)⁻¹ * (eightMinusDenZ τ z)⁻¹ * (ModularForm.discriminant z)⁻¹ *
      (1728 * leechPlusA2 τ * ModularForm.E₄ z * ModularForm.discriminant z)) * h26 +
    ((1728 * ckmrvPlusScale)⁻¹ * (eightMinusDenZ τ z)⁻¹ * (ModularForm.discriminant z)⁻¹ *
      (-(2 * 1728) * leechPlusA1 τ *
          (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * EisensteinSeries.E2 z) +
        1728 * leechPlusA0 τ * (EisensteinSeries.E2 z ^ 2 * ModularForm.discriminant z))) * h24

/-- `Ñ₂ = D A₂ + B₂`, the `z²`-numerator of (4.38); it is `T`-invariant and holomorphic. -/
def leechPlusN2 (τ z : ℍ) : ℂ := eightMinusDenZ τ z * leechPlusA2z τ z + leechPlusB2z τ z

theorem hasExp3_leechPlusN2 (τ : ℍ) : HasExp3 (fun z => leechPlusN2 τ z) 0 0 0 :=
  (((hasExp3_eightMinusDenZ τ).mul ((hasExp3_eisensteinFour.const_mul (leechPlusP0 τ)).add
      (hasExp3_eisensteinTwo.pow.const_mul (leechPlusP2 τ)))).add
    ((((hasExp3_eisensteinFour.mul hasExp3_discriminant).const_mul (1728 * leechPlusA2 τ)).sub
      ((hasExp3_eisensteinFourteen.mul hasExp3_eisensteinTwo).const_mul
        (2 * 1728 * leechPlusA1 τ))).add
      ((hasExp3_eisensteinTwo.pow.mul hasExp3_discriminant).const_mul
        (1728 * leechPlusA0 τ)))).congr_fun (fun z => rfl)
    |>.congr_coeff (by simp only [leechPlusP0, leechPlusP2]; ring) (by ring)
      (by simp only [leechPlusP0, leechPlusP2]; ring)

theorem mdifferentiable_leechPlusN2 (τ : ℍ) : MDiff (fun z => leechPlusN2 τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have h2 := E2_mdifferentiable
  have hΔ := mdifferentiable_modularDiscriminant
  have hD : MDiff (fun z => eightMinusDenZ τ z) :=
    (hΔ.mul mdifferentiable_const).sub (h4.pow 3)
  have hA : MDiff (fun z => leechPlusA2z τ z) :=
    (mdifferentiable_const.mul h4).add (mdifferentiable_const.mul (h2.pow 2))
  have hB : MDiff (fun z => leechPlusB2z τ z) :=
    ((mdifferentiable_const.mul (h4.mul hΔ)).sub
      (mdifferentiable_const.mul (((h4.pow 2).mul h6).mul h2))).add
      (mdifferentiable_const.mul ((h2.pow 2).mul hΔ))
  exact (hD.mul hA).add hB

theorem leechPlusN2_vadd_one (τ z : ℍ) : leechPlusN2 τ ((1 : ℝ) +ᵥ z) = leechPlusN2 τ z := by
  simp only [leechPlusN2, leechPlusA2z, leechPlusB2z, eightMinusDenZ, discriminant_vadd_one,
    eisensteinFour_vadd_one, eisensteinSix_vadd_one, eisensteinTwo_vadd_one]

theorem isBigO_leechPlusN2 (τ : ℍ) :
    (fun z => leechPlusN2 τ z) =O[atImInfty] fun z : ℍ => Real.exp (-4 * π * z.im) :=
  isBigO_q_sq_of_hasExp3 (mdifferentiable_leechPlusN2 τ) (leechPlusN2_vadd_one τ)
    (hasExp3_leechPlusN2 τ)

/-- **CKMRV (4.39), Leech plus kernel.** `(K₊ ∣_{-10} S)(τ, z) = O(e^{-2π Im z})`. -/
theorem isBigO_ckmrvLeechPlusKernel_S_right (τ : ℍ) :
    (fun z : ℍ => ckmrvLeechPlusKernel τ (ModularGroup.S • z) * (z : ℂ) ^ 10) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) := by
  have h0 : (fun z : ℍ => (eightMinusDenZ τ z)⁻¹ *
      ((ModularForm.discriminant z)⁻¹ * leechPlusN2 τ z)) =O[atImInfty]
        fun z : ℍ => Real.exp (-2 * π * z.im) :=
    ((isBigO_eightMinusDenZ_inv τ).mul
      (isBigO_discriminant_inv.mul (isBigO_leechPlusN2 τ))).congr_right fun z => by
        rw [one_mul, ← Real.exp_add]
        congr 1
        ring
  have h := h0.const_mul_left (1728 * ckmrvPlusScale)⁻¹
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [(tendsto_eightMinusDenZ τ).eventually_ne (by norm_num : (-1 : ℂ) ≠ 0)]
    with z hD
  have hDD : eightMinusDenZ τ z * (eightMinusDenZ τ z)⁻¹ = 1 := mul_inv_cancel₀ hD
  rw [ckmrvLeechPlusKernel_S_right]
  simp only [leechPlusN2]
  linear_combination ((1728 * ckmrvPlusScale)⁻¹ * (ModularForm.discriminant z)⁻¹ *
    leechPlusA2z τ z) * hDD

/-! ## Slash form -/

theorem isBigO_ckmrvEightMinusKernel_slash_S_right (τ : ℍ) :
    ((fun z => ckmrvEightMinusKernel τ z) ∣[(-2 : ℤ)] ModularGroup.S) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) :=
  (isBigO_ckmrvEightMinusKernel_S_right τ).congr_left fun z => by
    simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, neg_neg, zpow_ofNat]

theorem isBigO_ckmrvEightPlusKernel_slash_S_right (τ : ℍ) :
    ((fun z => ckmrvEightPlusKernel τ z) ∣[(-2 : ℤ)] ModularGroup.S) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) :=
  (isBigO_ckmrvEightPlusKernel_S_right τ).congr_left fun z => by
    simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, neg_neg, zpow_ofNat]

theorem isBigO_ckmrvLeechMinusKernel_slash_S_right (τ : ℍ) :
    ((fun z => ckmrvLeechMinusKernel τ z) ∣[(-10 : ℤ)] ModularGroup.S) =O[atImInfty]
      fun z : ℍ => Real.exp (-π * z.im) :=
  (isBigO_ckmrvLeechMinusKernel_S_right τ).congr_left fun z => by
    simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, neg_neg, zpow_ofNat]

theorem isBigO_ckmrvLeechPlusKernel_slash_S_right (τ : ℍ) :
    ((fun z => ckmrvLeechPlusKernel τ z) ∣[(-10 : ℤ)] ModularGroup.S) =O[atImInfty]
      fun z : ℍ => Real.exp (-2 * π * z.im) :=
  (isBigO_ckmrvLeechPlusKernel_S_right τ).congr_left fun z => by
    simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S, neg_neg, zpow_ofNat]

end E8Leech
