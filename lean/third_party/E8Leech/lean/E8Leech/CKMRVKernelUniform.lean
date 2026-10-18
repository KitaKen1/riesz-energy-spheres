import E8Leech.CKMRVKernelAsymptotics
import E8Leech.CKMRVLaplaceFull
import E8Leech.E8UnitCost
import E8Leech.EisensteinTwoAxis

/-!
# Uniform-in-`τ` asymptotics of the `d = 8` kernels, and the linear growth of `𝒦̂`

The asymptotics `K±(τ, z) − G±(τ, z) → 0` as `Im z → ∞` (CKMRV (4.38)) hold uniformly for `τ`
in a set on which `j(τ)` and the finitely many `τ`-coefficients are bounded: the proofs only use
these bounds. We state them along the product filter `𝓟 K ×ˢ atImInfty`.

On the axis `τ = iq`, `q ∈ [3, 4]`, the cusp term of `𝒦̂ = (K₊ − K₋)/2` has slope
`(πq/6)(E₂E₄ − E₆)(iq) ≥ (πq/6)·700·e^{−2πq} > 0`, so `𝒦̂(iq, it) ≥ c t` for `t ≥ T`
(the input `hlin` of `e8_analyticUnitCostInput_of_kernel_bounds`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real

/-! ## Lifting to the product filter -/

theorem isBigO_snd_of_isBigO {g : ℍ → ℂ} {h : ℍ → ℝ} (hg : g =O[atImInfty] h) (K : Set ℍ) :
    (fun p : ℍ × ℍ => g p.2) =O[𝓟 K ×ˢ atImInfty] fun p => h p.2 :=
  hg.comp_tendsto tendsto_snd

theorem isBigO_snd_of_isBigO' {g h : ℍ → ℝ} (hg : g =O[atImInfty] h) (K : Set ℍ) :
    (fun p : ℍ × ℍ => g p.2) =O[𝓟 K ×ˢ atImInfty] fun p => h p.2 :=
  hg.comp_tendsto tendsto_snd

theorem isBigO_fst_of_bound {K : Set ℍ} {a : ℍ → ℂ} {M : ℝ} (ha : ∀ τ ∈ K, ‖a τ‖ ≤ M) :
    (fun p : ℍ × ℍ => a p.1) =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ) := by
  refine IsBigO.of_bound M ?_
  filter_upwards [(eventually_principal.mpr fun τ (hτ : τ ∈ K) => hτ).prod_inl atImInfty]
    with p hp
  simpa using ha p.1 hp

/-! ## The `z`-side pieces -/

theorem isBigO_minusPieceA : (fun z : ℍ => ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z -
    ((π : ℂ) * I * z + 4 * Real.log 2)) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
  have hr0 := isBigO_one_of_sub_one isBigO_eisensteinFour_mul_eisensteinSix_sub_one
  have h1 := ((hr0.mul isBigO_ckmrvL_sub_linear).congr_right fun z => one_mul _).trans
    isBigO_exp_neg_pi_norm_mul
  have h2 := (((isBigO_eisensteinFour_mul_eisensteinSix_sub_one.trans
    isBigO_exp_neg_two_pi_exp_neg_pi).mul isBigO_linear_norm_coe).congr_right fun z =>
      mul_comm _ _)
  exact (h1.add h2).congr_left fun z => by ring

theorem isBigO_minusPieceB : (fun z : ℍ => ModularForm.E₄ z ^ 2 * thetaW z - 1) =O[atImInfty]
    fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
  have hr1 := isBigO_one_of_sub_one isBigO_eisensteinFour_sq_sub_one
  have h1 := (hr1.mul isBigO_thetaW_sub_one).congr_right fun z => one_mul _
  have h2 := isBigO_eisensteinFour_sq_sub_one.trans isBigO_exp_neg_two_pi_exp_neg_pi
  exact ((h1.add h2).congr_left fun z => by ring).trans isBigO_exp_neg_pi_norm_mul

theorem isBigO_minusPieceC : (fun z : ℍ => ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2) - 1)
    =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (-π * z.im) := by
  have hr2 := isBigO_one_of_sub_one isBigO_eisensteinSix_sub_one
  have h1 := (hr2.mul isBigO_thetaU_sq_sub_thetaV_sq_sub_one).congr_right fun z => one_mul _
  have h2 := isBigO_eisensteinSix_sub_one.trans isBigO_exp_neg_two_pi_exp_neg_pi
  exact ((h1.add h2).congr_left fun z => by ring).trans isBigO_exp_neg_pi_norm_mul

theorem isBigO_plusPieceQ1 : (fun z : ℍ => (z : ℂ) ^ 2 - 6 * (Complex.I / (Real.pi : ℂ)) * z)
    =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
  (isBigO_quadratic 1 (-(6 * (Complex.I / (Real.pi : ℂ)))) 0).congr_left fun z => by ring

theorem isBigO_plusPieceQ2 : (fun z : ℍ => (z : ℂ) ^ 2 - 12 * (Complex.I / (Real.pi : ℂ)) * z -
    36 / (Real.pi : ℂ) ^ 2) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
  (isBigO_quadratic 1 (-(12 * (Complex.I / (Real.pi : ℂ)))) (-(36 / (Real.pi : ℂ) ^ 2))).congr_left
    fun z => by ring

theorem isBigO_plusPieceA : (fun z : ℍ => ModularForm.E₄ z * ModularForm.E₆ z *
    ckmrvTildePhiBasis z 1 - ((z : ℂ) ^ 2 - 6 * (Complex.I / (Real.pi : ℂ)) * z)) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
  have hp1 : (fun z : ℍ => ckmrvTildePhiBasis z 1 - ((z : ℂ) ^ 2 -
      6 * (Complex.I / (Real.pi : ℂ)) * z)) =O[atImInfty]
        fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
    have h := (isBigO_coe_sq.mul isBigO_eisensteinTwo_sub_one)
    refine h.congr_left fun z => ?_
    have h1 : ckmrvTildePhiBasis z 1 = (z : ℂ) ^ 2 * EisensteinSeries.E2 z -
        6 * Complex.I / (Real.pi : ℂ) * (z : ℂ) := rfl
    rw [h1]
    ring
  have hr1 := isBigO_one_of_sub_one isBigO_eisensteinFour_mul_eisensteinSix_sub_one
  have h1 := (hr1.mul hp1).congr_right fun z => one_mul _
  have h2 := (isBigO_eisensteinFour_mul_eisensteinSix_sub_one.mul isBigO_plusPieceQ1).congr_right
    fun z => mul_comm _ _
  exact (h1.add h2).congr_left fun z => by ring

theorem isBigO_plusPieceB : (fun z : ℍ => ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2 -
    ((z : ℂ) ^ 2 - 12 * (Complex.I / (Real.pi : ℂ)) * z - 36 / (Real.pi : ℂ) ^ 2))
      =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im) := by
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
  have hr2 := isBigO_one_of_sub_one isBigO_eisensteinFour_sq_sub_one
  have h1 := (hr2.mul hp2).congr_right fun z => one_mul _
  have h2 := (isBigO_eisensteinFour_sq_sub_one.mul isBigO_plusPieceQ2).congr_right
    fun z => mul_comm _ _
  exact (h1.add h2).congr_left fun z => by ring

/-! ## Uniform asymptotics -/

section Uniform

variable {K : Set ℍ} {Mj : ℝ} (hMj : ∀ τ ∈ K, ‖kleinModularJ τ‖ ≤ Mj)
include hMj

theorem isBigO_eightMinusDenZ_add_one_unif :
    (fun p : ℍ × ℍ => eightMinusDenZ p.1 p.2 + 1) =O[𝓟 K ×ˢ atImInfty]
      fun p => Real.exp (-2 * π * p.2.im) := by
  have h := (((isBigO_fst_of_bound hMj).mul (isBigO_snd_of_isBigO isBigO_discriminant K)).congr_right
    fun p => one_mul _).sub (isBigO_snd_of_isBigO isBigO_eisensteinFour_cube_sub_one K)
  refine h.congr_left fun p => ?_
  simp only [eightMinusDenZ]
  ring

theorem tendsto_eightMinusDenZ_unif :
    Tendsto (fun p : ℍ × ℍ => eightMinusDenZ p.1 p.2) (𝓟 K ×ˢ atImInfty) (𝓝 (-1)) := by
  have h := ((isBigO_eightMinusDenZ_add_one_unif hMj).trans_tendsto
    (tendsto_exp_neg_two_pi_im.comp tendsto_snd)).sub_const 1
  simpa using h

theorem isBigO_eightMinusDenZ_inv_unif :
    (fun p : ℍ × ℍ => (eightMinusDenZ p.1 p.2)⁻¹) =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ) :=
  ((tendsto_eightMinusDenZ_unif hMj).inv₀ (by norm_num)).isBigO_one ℝ

theorem isBigO_eightMinusDenZ_inv_add_one_unif :
    (fun p : ℍ × ℍ => (eightMinusDenZ p.1 p.2)⁻¹ + 1) =O[𝓟 K ×ˢ atImInfty]
      fun p => Real.exp (-2 * π * p.2.im) := by
  have hDne : ∀ᶠ p : ℍ × ℍ in 𝓟 K ×ˢ atImInfty, eightMinusDenZ p.1 p.2 ≠ 0 :=
    (tendsto_eightMinusDenZ_unif hMj).eventually_ne (by norm_num)
  have h := ((isBigO_eightMinusDenZ_add_one_unif hMj).mul
    (isBigO_eightMinusDenZ_inv_unif hMj)).congr_right fun p => mul_one _
  refine h.congr' ?_ (Eventually.of_forall fun p => rfl)
  filter_upwards [hDne] with p hp
  field_simp
  ring

/-- **(4.38) for `K₋`, uniformly in `τ`.** -/
theorem isBigO_ckmrvEightMinusKernel_sub_G_unif {M0 M1 M2 : ℝ}
    (h0 : ∀ τ ∈ K, ‖eightMinusTauCoeff 0 τ‖ ≤ M0) (h1 : ∀ τ ∈ K, ‖eightMinusTauCoeff 1 τ‖ ≤ M1)
    (h2 : ∀ τ ∈ K, ‖eightMinusTauCoeff 2 τ‖ ≤ M2) :
    (fun p : ℍ × ℍ => ckmrvEightMinusKernel p.1 p.2 - ckmrvEightMinusG p.1 p.2)
      =O[𝓟 K ×ˢ atImInfty] fun p => ‖(p.2 : ℂ)‖ * Real.exp (-π * p.2.im) := by
  have hc0 := isBigO_fst_of_bound h0
  have hc1 := isBigO_fst_of_bound h1
  have hc2 := isBigO_fst_of_bound h2
  have hA := isBigO_snd_of_isBigO isBigO_minusPieceA K
  have hB := isBigO_snd_of_isBigO isBigO_minusPieceB K
  have hC := isBigO_snd_of_isBigO isBigO_minusPieceC K
  have hdiff := (((hc0.mul hA).congr_right fun p => one_mul _).add
    ((hc1.mul hB).congr_right fun p => one_mul _)).add ((hc2.mul hC).congr_right fun p => one_mul _)
  have hlin := isBigO_snd_of_isBigO isBigO_linear_norm_coe K
  have hone := isBigO_snd_of_isBigO' isBigO_one_real_norm_coe K
  have hS0 : (fun p : ℍ × ℍ => eightMinusTauCoeff 0 p.1 * ((π : ℂ) * I * p.2 + 4 * Real.log 2) +
      eightMinusTauCoeff 1 p.1 + eightMinusTauCoeff 2 p.1) =O[𝓟 K ×ˢ atImInfty]
        fun p => ‖(p.2 : ℂ)‖ :=
    (((hc0.mul hlin).congr_right fun p => one_mul _).add (hc1.trans hone)).add (hc2.trans hone)
  have hT1 := ((isBigO_eightMinusDenZ_inv_unif hMj).mul hdiff).congr_right fun p => one_mul _
  have hT2 := (((isBigO_eightMinusDenZ_inv_add_one_unif hMj).mul hS0).congr_right
    fun p => mul_comm _ _).trans ((isBigO_refl (fun p : ℍ × ℍ => ‖(p.2 : ℂ)‖) _).mul
      (isBigO_snd_of_isBigO' isBigO_exp_neg_two_pi_exp_neg_pi K))
  have h := ((hT1.add hT2).const_mul_left ckmrvMinusScale⁻¹)
  refine h.congr_left fun p => ?_
  rw [ckmrvEightMinusKernel_eq_z, ckmrvEightMinusG]
  ring

/-- **(4.38) for `K₊`, uniformly in `τ`.** -/
theorem isBigO_ckmrvEightPlusKernel_sub_G_unif {Ma Mb MF : ℝ}
    (ha : ∀ τ ∈ K, ‖ckmrvPhiBasis τ 1 * ModularForm.E₄ τ‖ ≤ Ma)
    (hb : ∀ τ ∈ K, ‖ckmrvPhiBasis τ 0 * ModularForm.E₆ τ‖ ≤ Mb)
    (hF : ∀ τ ∈ K, ‖ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2‖ ≤ MF) :
    (fun p : ℍ × ℍ => ckmrvEightPlusKernel p.1 p.2 - ckmrvEightPlusG p.1 p.2)
      =O[𝓟 K ×ˢ atImInfty] fun p => ‖(p.2 : ℂ)‖ ^ 2 * Real.exp (-2 * π * p.2.im) := by
  have hca := isBigO_fst_of_bound ha
  have hcb := isBigO_fst_of_bound hb
  have hcF := isBigO_fst_of_bound hF
  have hDinv := isBigO_eightMinusDenZ_inv_unif hMj
  have hDinv1 := isBigO_eightMinusDenZ_inv_add_one_unif hMj
  have hA := isBigO_snd_of_isBigO isBigO_plusPieceA K
  have hB := isBigO_snd_of_isBigO isBigO_plusPieceB K
  have hq1 := isBigO_snd_of_isBigO isBigO_plusPieceQ1 K
  have hq2 := isBigO_snd_of_isBigO isBigO_plusPieceQ2 K
  have hP0 : (fun p : ℍ × ℍ => -2 * (ckmrvPhiBasis p.1 1 * ModularForm.E₄ p.1) *
      ((p.2 : ℂ) ^ 2 - 6 * (Complex.I / (Real.pi : ℂ)) * p.2) +
      ckmrvPhiBasis p.1 0 * ModularForm.E₆ p.1 * ((p.2 : ℂ) ^ 2 -
        12 * (Complex.I / (Real.pi : ℂ)) * p.2 - 36 / (Real.pi : ℂ) ^ 2))
        =O[𝓟 K ×ˢ atImInfty] fun p => ‖(p.2 : ℂ)‖ ^ 2 :=
    ((((hca.const_mul_left (-2)).mul hq1).congr_right fun p => one_mul _).congr_left
      (fun p => by ring)).add ((hcb.mul hq2).congr_right fun p => one_mul _)
  have hT1 : (fun p : ℍ × ℍ => ckmrvPhiBasis p.1 2 * ckmrvModularFactor p.1 2 *
      (ModularForm.discriminant p.2 * (p.2 : ℂ) ^ 2 * (eightMinusDenZ p.1 p.2)⁻¹))
        =O[𝓟 K ×ˢ atImInfty] fun p => ‖(p.2 : ℂ)‖ ^ 2 * Real.exp (-2 * π * p.2.im) :=
    (hcF.mul (((isBigO_snd_of_isBigO isBigO_discriminant K).mul
      (isBigO_snd_of_isBigO isBigO_coe_sq K)).mul hDinv)).congr_right fun p => by ring
  have hT2 := (hDinv.mul ((((hca.const_mul_left (-2)).mul hA).congr_right fun p => one_mul _).add
    ((hcb.mul hB).congr_right fun p => one_mul _))).congr_right fun p => one_mul _
  have hT3 := (hDinv1.mul hP0).congr_right fun p => mul_comm _ _
  have h := ((hT1.add hT2).add hT3).const_mul_left ckmrvPlusScale⁻¹
  have hne : ∀ᶠ p : ℍ × ℍ in 𝓟 K ×ˢ atImInfty, kleinModularJ p.1 - kleinModularJ p.2 ≠ 0 := by
    filter_upwards [(tendsto_eightMinusDenZ_unif hMj).eventually_ne
      (by norm_num : (-1 : ℂ) ≠ 0)] with p hp
    intro h0
    apply hp
    have hΔ : ModularForm.discriminant p.2 ≠ 0 := ModularForm.discriminant_ne_zero p.2
    have hJ : kleinModularJ p.2 * ModularForm.discriminant p.2 = ModularForm.E₄ p.2 ^ 3 := by
      rw [kleinModularJ]
      field_simp
    rw [eightMinusDenZ, ← hJ]
    linear_combination ModularForm.discriminant p.2 * h0
  refine h.congr' ?_ (Eventually.of_forall fun p => rfl)
  filter_upwards [hne] with p hg
  rw [ckmrvEightPlusKernel_eq_z p.1 p.2 hg, ckmrvEightPlusG]
  have hp0 : ckmrvPhiBasis p.1 0 = (p.1 : ℂ) := rfl
  ring

end Uniform

end E8Leech
