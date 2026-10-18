import E8Leech.CKMRVMinusBasis
import E8Leech.KleinModularIdentification
import E8Leech.EisensteinCuspDerivative
import E8Leech.CKMRVCoefficientMatrices
import E8Leech.CKMRVPlusKernels
import E8Leech.CKMRVRightRelations
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Decay at `i∞` for the CKMRV kernels (CKMRV (4.21))

CKMRV Theorem 4.3(4) states that, for fixed `z`, the kernels satisfy
`K^{(8)}_±(τ, z) = O(|τ e^{2πiτ}|)` and `K^{(24)}_±(τ, z) = O(|τ e^{4πiτ}|)` as `Im τ → ∞`.
The paper only says that this "follows from a q-expansion calculation".

This file builds the decay toolkit and treats the dimension-eight minus kernel.
The proof avoids explicit `q`-expansions:

* combinations whose constant terms cancel are `T`-invariant, so Mathlib's exponential decay
  at the cusp applies with period `1` (decay `e^{-2π Im τ}`);
* the remaining cancellations are products of two factors that are `T²`-invariant and tend
  to `0`, each decaying like `e^{-π Im τ}`.

Which combinations cancel was found first by an exact truncated `q`-series computation
(`research/check-ckmrv-growth-421-20261010.py`).
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Exponential decay from periodicity -/

theorem periodic_comp_ofComplex_of_vadd {f : ℍ → ℂ} {h : ℝ}
    (hper : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) : Function.Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + h).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert! hper ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw0 : w.im ≤ 0 := not_lt.mp hw
    have hw' : (w + h).im ≤ 0 := by simpa using hw0
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw0]

theorem vadd_one_eq_T_smul (τ : ℍ) : ((1 : ℝ) +ᵥ τ) = ModularGroup.T • τ :=
  (UpperHalfPlane.modular_T_smul τ).symm

theorem vadd_two_eq_T_smul_T_smul (τ : ℍ) :
    ((2 : ℝ) +ᵥ τ) = ModularGroup.T • ModularGroup.T • τ := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul, vadd_vadd]
  norm_num

/-- A holomorphic `h`-periodic function on `ℍ` tending to `0` at `i∞` decays like
`exp (-2π Im τ / h)`. -/
theorem isBigO_exp_of_periodic {f : ℍ → ℂ} {h : ℝ} (hh : 0 < h) (hf : MDiff f)
    (hper : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) (hlim : Tendsto f atImInfty (𝓝 0)) :
    f =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im / h) := by
  have hz : IsZeroAtImInfty f := hlim
  exact hz.exp_decay_atImInfty hh (periodic_comp_ofComplex_of_vadd hper) hf
    hz.isBoundedAtImInfty

/-- `T`-invariant version: decay `e^{-2π Im τ}`. -/
theorem isBigO_exp_of_T_invariant {f : ℍ → ℂ} (hf : MDiff f)
    (hT : ∀ τ : ℍ, f (ModularGroup.T • τ) = f τ) (hlim : Tendsto f atImInfty (𝓝 0)) :
    f =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have h := isBigO_exp_of_periodic (h := 1) one_pos hf
    (fun τ => by rw [vadd_one_eq_T_smul, hT]) hlim
  simpa using h

/-- `T²`-invariant version: decay `e^{-π Im τ}`. -/
theorem isBigO_exp_half_of_T_sq_invariant {f : ℍ → ℂ} (hf : MDiff f)
    (hT : ∀ τ : ℍ, f (ModularGroup.T • ModularGroup.T • τ) = f τ)
    (hlim : Tendsto f atImInfty (𝓝 0)) :
    f =O[atImInfty] fun τ : ℍ => Real.exp (-π * τ.im) := by
  have h := isBigO_exp_of_periodic (h := 2) two_pos hf
    (fun τ => by rw [vadd_two_eq_T_smul_T_smul, hT]) hlim
  refine h.congr_right fun τ => ?_
  congr 1
  ring

/-! ## The theta quantities -/

theorem thetaU_T_T (τ : ℍ) : thetaU (ModularGroup.T • ModularGroup.T • τ) = thetaU τ := by
  rw [thetaU_T, thetaW_T]

theorem thetaV_T_T (τ : ℍ) : thetaV (ModularGroup.T • ModularGroup.T • τ) = thetaV τ := by
  rw [thetaV_T, thetaV_T, neg_neg]

theorem thetaW_T_T (τ : ℍ) : thetaW (ModularGroup.T • ModularGroup.T • τ) = thetaW τ := by
  rw [thetaW_T, thetaU_T]

theorem ckmrvLS_T_T (τ : ℍ) : ckmrvLS (ModularGroup.T • ModularGroup.T • τ) = ckmrvLS τ := by
  rw [ckmrvLS_T, ckmrvLS_T, neg_neg]

/-- `ξ₂ - ξ₄` is `T`-invariant and vanishes at `i∞`, hence is `O(e^{-2π Im τ})`. -/
theorem isBigO_ckmrvXiTwo_sub_ckmrvXiFour :
    (fun τ : ℍ => ckmrvXiTwo τ - ckmrvXiFour τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  have hW := mdifferentiable_thetaW
  refine isBigO_exp_of_T_invariant ?_ (fun τ => by rw [ckmrvXiTwo_T, ckmrvXiFour_T]) ?_
  · have hfun : (fun τ : ℍ => ckmrvXiTwo τ - ckmrvXiFour τ) =
        thetaU + thetaW - (thetaU * thetaU + thetaW * thetaW -
          (fun _ => (2 : ℂ)) * (thetaV * thetaV)) := by
      funext τ
      simp only [ckmrvXiTwo, ckmrvXiFour, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
    rw [hfun]
    exact (hU.add hW).sub (((hU.mul hU).add (hW.mul hW)).sub
      (mdifferentiable_const.mul (hV.mul hV)))
  · have h := (tendsto_thetaU_atImInfty.add tendsto_thetaW_atImInfty).sub
      (((tendsto_thetaU_atImInfty.pow 2).add (tendsto_thetaW_atImInfty.pow 2)).sub
        ((tendsto_const_nhds (x := (2 : ℂ))).mul (tendsto_thetaV_atImInfty.pow 2)))
    have h0 : ((1 : ℂ) + 1) - ((1 ^ 2 + 1 ^ 2) - 2 * 0 ^ 2) = 0 := by norm_num
    rw [h0] at h
    exact h

/-- `ξ₂^S - ξ₄^S` is `T²`-invariant and vanishes at `i∞`, hence is `O(e^{-π Im τ})`. -/
theorem isBigO_ckmrvXiTwoS_sub_ckmrvXiFourS :
    (fun τ : ℍ => ckmrvXiTwoS τ - ckmrvXiFourS τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-π * τ.im) := by
  have hU := mdifferentiable_thetaU
  have hV := mdifferentiable_thetaV
  have hW := mdifferentiable_thetaW
  refine isBigO_exp_half_of_T_sq_invariant ?_
    (fun τ => by simp only [ckmrvXiTwoS, ckmrvXiFourS, thetaU_T_T, thetaV_T_T, thetaW_T_T]) ?_
  · have hfun : (fun τ : ℍ => ckmrvXiTwoS τ - ckmrvXiFourS τ) =
        -(thetaU + thetaV) - (thetaU * thetaU + thetaV * thetaV -
          (fun _ => (2 : ℂ)) * (thetaW * thetaW)) := by
      funext τ
      simp only [ckmrvXiTwoS, ckmrvXiFourS, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Pi.neg_apply]
      ring
    rw [hfun]
    exact (hU.add hV).neg.sub (((hU.mul hU).add (hV.mul hV)).sub
      (mdifferentiable_const.mul (hW.mul hW)))
  · have h := ((tendsto_thetaU_atImInfty.add tendsto_thetaV_atImInfty).neg).sub
      (((tendsto_thetaU_atImInfty.pow 2).add (tendsto_thetaV_atImInfty.pow 2)).sub
        ((tendsto_const_nhds (x := (2 : ℂ))).mul (tendsto_thetaW_atImInfty.pow 2)))
    have h0 : -((1 : ℂ) + 0) - ((1 ^ 2 + 0 ^ 2) - 2 * 1 ^ 2) = 0 := by norm_num
    rw [h0] at h
    exact h

/-- `L_S` is `T²`-invariant and tends to `0`, hence is `O(e^{-π Im τ})`. -/
theorem isBigO_ckmrvLS : ckmrvLS =O[atImInfty] fun τ : ℍ => Real.exp (-π * τ.im) :=
  isBigO_exp_half_of_T_sq_invariant mdifferentiable_ckmrvLS ckmrvLS_T_T
    tendsto_ckmrvLS_atImInfty

/-! ## Polynomial growth of `L` -/

theorem eventually_one_le_norm_coe : ∀ᶠ τ : ℍ in atImInfty, (1 : ℝ) ≤ ‖(τ : ℂ)‖ := by
  filter_upwards [(atImInfty_basis.mem_of_mem (i := 1) trivial)] with τ hτ
  have h1 : (1 : ℝ) ≤ τ.im := hτ
  calc (1 : ℝ) ≤ τ.im := h1
    _ = (τ : ℂ).im := rfl
    _ ≤ |(τ : ℂ).im| := le_abs_self _
    _ ≤ ‖(τ : ℂ)‖ := Complex.abs_im_le_norm _

theorem isBigO_one_norm_coe : (fun _ : ℍ => (1 : ℂ)) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_norm_coe] with τ hτ
  simpa using hτ

/-- `L(τ) = O(|τ|)` at `i∞`. -/
theorem isBigO_ckmrvL : ckmrvL =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  have hb : (fun τ : ℍ => ckmrvL τ - π * I * τ) =O[atImInfty] fun _ : ℍ => (1 : ℂ) :=
    tendsto_ckmrvL_sub_atImInfty.isBigO_one ℂ
  have hlin : (fun τ : ℍ => (π : ℂ) * I * τ) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
    refine IsBigO.of_bound (π) ?_
    filter_upwards with τ
    simp [abs_of_pos Real.pi_pos]
  have h := (hb.trans isBigO_one_norm_coe).add hlin
  refine h.congr_left fun τ => ?_
  ring

/-! ## Eisenstein series, the discriminant and `j` -/

theorem tendsto_exp_neg_two_pi_im :
    Tendsto (fun τ : ℍ => Real.exp (-2 * π * τ.im)) atImInfty (𝓝 0) := by
  have h1 : Tendsto (fun τ : ℍ => 2 * π * τ.im) atImInfty atTop :=
    tendsto_upperHalfPlaneIm_atImInfty.const_mul_atTop (by positivity)
  have h2 : Tendsto (fun τ : ℍ => -2 * π * τ.im) atImInfty atBot := by
    refine (tendsto_neg_atTop_atBot.comp h1).congr fun τ => ?_
    simp only [Function.comp_apply]
    ring
  exact Real.tendsto_exp_atBot.comp h2

theorem tendsto_eisensteinFour_atImInfty :
    Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h4 : (qExpansion 1 ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide)
  simpa only [h4] using levelOne_tendsto_qExpansion_constant ModularForm.E₄

theorem tendsto_eisensteinSix_atImInfty :
    Tendsto (ModularForm.E₆ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h6 : (qExpansion 1 ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide)
  simpa only [h6] using levelOne_tendsto_qExpansion_constant ModularForm.E₆

/-- `E₄ - E₆ = O(e^{-2π Im τ})`. -/
theorem isBigO_eisensteinFour_sub_eisensteinSix :
    (fun τ : ℍ => ModularForm.E₄ τ - ModularForm.E₆ τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have h := isBigO_exp_of_periodic (h := 1) one_pos
    (f := fun τ : ℍ => ModularForm.E₄ τ - ModularForm.E₆ τ)
    ((ModularFormClass.holo ModularForm.E₄).sub (ModularFormClass.holo ModularForm.E₆))
    (fun τ => by
      show ModularForm.E₄ ((1 : ℝ) +ᵥ τ) - ModularForm.E₆ ((1 : ℝ) +ᵥ τ) =
        ModularForm.E₄ τ - ModularForm.E₆ τ
      rw [SlashInvariantForm.vAdd_apply_of_mem_strictPeriods ModularForm.E₄ τ
          one_mem_strictPeriods_SL,
        SlashInvariantForm.vAdd_apply_of_mem_strictPeriods ModularForm.E₆ τ
          one_mem_strictPeriods_SL])
    (by simpa using tendsto_eisensteinFour_atImInfty.sub tendsto_eisensteinSix_atImInfty)
  simpa using h

/-- `(θ₂ θ₃ θ₄)⁸`, written with `jacobiTheta₂ (τ/2) τ`. -/
def thetaProductEight (τ : ℍ) : ℂ :=
  (jacobiTheta₂ ((τ : ℂ) / 2) τ * thetaThree τ * thetaFour τ) ^ 8

theorem discriminant_eq_qParam_mul (τ : ℍ) :
    ModularForm.discriminant τ =
      Function.Periodic.qParam 1 (τ : ℂ) * (thetaProductEight τ / 256) := by
  have h : 256 * ModularForm.discriminant τ =
      Function.Periodic.qParam 1 (τ : ℂ) * thetaProductEight τ := by
    rw [← thetaProductSq_eq_discriminant, thetaProductSq_eq_qParam_mul, thetaProductEight]
  calc ModularForm.discriminant τ = (256 * ModularForm.discriminant τ) / 256 := by ring
    _ = Function.Periodic.qParam 1 (τ : ℂ) * thetaProductEight τ / 256 := by rw [h]
    _ = _ := by ring

theorem tendsto_thetaProductEight_div :
    Tendsto (fun τ : ℍ => thetaProductEight τ / 256) atImInfty (𝓝 1) := by
  have h := tendsto_thetaProduct_div_qParam.div_const (256 : ℂ)
  have h1 : (256 : ℂ) / 256 = 1 := by norm_num
  rw [h1] at h
  exact h

theorem norm_qParam_one (τ : ℍ) :
    ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-2 * π * τ.im) := by
  rw [Function.Periodic.norm_qParam]
  simp

/-- `Δ = O(e^{-2π Im τ})`. -/
theorem isBigO_discriminant :
    (fun τ : ℍ => ModularForm.discriminant τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have hq : (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ)) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
    rw [norm_qParam_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  have h := hq.mul (tendsto_thetaProductEight_div.isBigO_one ℝ)
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · exact (discriminant_eq_qParam_mul τ).symm
  · simp

/-- `Δ⁻¹ = O(e^{2π Im τ})`. -/
theorem isBigO_discriminant_inv :
    (fun τ : ℍ => (ModularForm.discriminant τ)⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (2 * π * τ.im) := by
  have hq : (fun τ : ℍ => (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (2 * π * τ.im) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
    rw [norm_inv, norm_qParam_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul,
      ← Real.exp_neg]
    apply le_of_eq
    congr 1
    ring
  have hP : Tendsto (fun τ : ℍ => (thetaProductEight τ / 256)⁻¹) atImInfty (𝓝 1) := by
    simpa using tendsto_thetaProductEight_div.inv₀ one_ne_zero
  have h := hq.mul (hP.isBigO_one ℝ)
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · dsimp only
    rw [discriminant_eq_qParam_mul, mul_inv]
  · simp

theorem tendsto_discriminant_atImInfty :
    Tendsto (fun τ : ℍ => ModularForm.discriminant τ) atImInfty (𝓝 0) :=
  isBigO_discriminant.trans_tendsto tendsto_exp_neg_two_pi_im

/-- `j = O(e^{2π Im τ})`. -/
theorem isBigO_kleinModularJ :
    kleinModularJ =O[atImInfty] fun τ : ℍ => Real.exp (2 * π * τ.im) := by
  have h := ((tendsto_eisensteinFour_atImInfty.pow 3).isBigO_one ℝ).mul isBigO_discriminant_inv
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · simp [kleinModularJ, div_eq_mul_inv]
  · simp

/-- For fixed `z`, `(j(τ) - j(z))⁻¹ = O(e^{-2π Im τ})`. -/
theorem isBigO_kleinModularJ_sub_inv (z : ℍ) :
    (fun τ : ℍ => (kleinModularJ τ - kleinModularJ z)⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have hden : Tendsto (fun τ : ℍ => (ModularForm.E₄ τ ^ 3 -
      kleinModularJ z * ModularForm.discriminant τ)⁻¹) atImInfty (𝓝 1) := by
    have h := ((tendsto_eisensteinFour_atImInfty.pow 3).sub
      (tendsto_discriminant_atImInfty.const_mul (kleinModularJ z))).inv₀ (by simp)
    simpa using h
  have h := isBigO_discriminant.mul (hden.isBigO_one ℝ)
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
    have hJ : kleinModularJ τ - kleinModularJ z =
        (ModularForm.E₄ τ ^ 3 - kleinModularJ z * ModularForm.discriminant τ) /
          ModularForm.discriminant τ := by
      rw [kleinModularJ]
      field_simp
    dsimp only
    rw [hJ, inv_div, div_eq_mul_inv]
  · simp

/-! ## Bounded and logarithmic factors -/

theorem isBigO_one_real_norm_coe :
    (fun _ : ℍ => (1 : ℝ)) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_norm_coe] with τ hτ
  simpa using hτ

theorem isBigO_exp_neg_pi_norm_coe :
    (fun τ : ℍ => Real.exp (-π * τ.im)) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_norm_coe] with τ hτ
  have hle : Real.exp (-π * τ.im) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, τ.im_pos]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, Real.norm_eq_abs, abs_norm]
  exact hle.trans hτ

theorem exp_neg_two_pi_mul_exp_two_pi (τ : ℍ) :
    Real.exp (-2 * π * τ.im) * Real.exp (2 * π * τ.im) = 1 := by
  rw [← Real.exp_add]
  simp

theorem exp_neg_pi_mul_exp_neg_pi (τ : ℍ) :
    Real.exp (-π * τ.im) * Real.exp (-π * τ.im) = Real.exp (-2 * π * τ.im) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem tendsto_ckmrvXiTwo_atImInfty : Tendsto ckmrvXiTwo atImInfty (𝓝 2) := by
  have h := tendsto_thetaU_atImInfty.add tendsto_thetaW_atImInfty
  norm_num at h
  exact h

theorem tendsto_ckmrvXiFour_atImInfty : Tendsto ckmrvXiFour atImInfty (𝓝 2) := by
  have h := ((tendsto_thetaU_atImInfty.pow 2).add (tendsto_thetaW_atImInfty.pow 2)).sub
    ((tendsto_const_nhds (x := (2 : ℂ))).mul (tendsto_thetaV_atImInfty.pow 2))
  norm_num at h
  exact h

theorem tendsto_ckmrvXiTwoS_atImInfty : Tendsto ckmrvXiTwoS atImInfty (𝓝 (-1)) := by
  have h := (tendsto_thetaU_atImInfty.add tendsto_thetaV_atImInfty).neg
  have h0 : -((1 : ℂ) + 0) = -1 := by norm_num
  rw [h0] at h
  exact h

theorem tendsto_ckmrvXiFourS_atImInfty : Tendsto ckmrvXiFourS atImInfty (𝓝 (-1)) := by
  have h := ((tendsto_thetaU_atImInfty.pow 2).add (tendsto_thetaV_atImInfty.pow 2)).sub
    ((tendsto_const_nhds (x := (2 : ℂ))).mul (tendsto_thetaW_atImInfty.pow 2))
  norm_num at h
  exact h

/-- `ξ L + ξ^S L_S = O(|τ|)` for bounded `ξ, ξ^S`. -/
theorem isBigO_xi_mul_L_add {a b : ℍ → ℂ} {ca cb : ℂ} (ha : Tendsto a atImInfty (𝓝 ca))
    (hb : Tendsto b atImInfty (𝓝 cb)) :
    (fun τ : ℍ => a τ * ckmrvL τ + b τ * ckmrvLS τ) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ := by
  have h1 := ((ha.isBigO_one ℝ).mul isBigO_ckmrvL).congr_right fun τ => one_mul _
  have h2 := (((hb.isBigO_one ℝ).mul isBigO_ckmrvLS).congr_right fun τ => one_mul _).trans
    isBigO_exp_neg_pi_norm_coe
  exact h1.add h2

theorem isBigO_ckmrvPsiBasis_one :
    (fun τ : ℍ => ckmrvPsiBasis τ 1) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ :=
  isBigO_xi_mul_L_add tendsto_ckmrvXiTwo_atImInfty tendsto_ckmrvXiTwoS_atImInfty

theorem isBigO_ckmrvPsiBasis_two :
    (fun τ : ℍ => ckmrvPsiBasis τ 2) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ :=
  isBigO_xi_mul_L_add tendsto_ckmrvXiFour_atImInfty tendsto_ckmrvXiFourS_atImInfty

/-- The main cancellation: `(ψ₁ - ψ₂) j = O(|τ|)` although `j` grows like `e^{2π Im τ}`. -/
theorem isBigO_psi_sub_mul_kleinModularJ :
    (fun τ : ℍ => (ckmrvPsiBasis τ 1 - ckmrvPsiBasis τ 2) * kleinModularJ τ) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ := by
  -- `(ξ₂ - ξ₄) j = O(1)` and `(ξ₂^S - ξ₄^S) L_S j = O(1)`.
  have hA : (fun τ : ℍ => (ckmrvXiTwo τ - ckmrvXiFour τ) * kleinModularJ τ) =O[atImInfty]
      fun _ : ℍ => (1 : ℝ) :=
    (isBigO_ckmrvXiTwo_sub_ckmrvXiFour.mul isBigO_kleinModularJ).congr_right
      exp_neg_two_pi_mul_exp_two_pi
  have hB : (fun τ : ℍ => (ckmrvXiTwoS τ - ckmrvXiFourS τ) * ckmrvLS τ * kleinModularJ τ)
      =O[atImInfty] fun _ : ℍ => (1 : ℝ) := by
    have h := (isBigO_ckmrvXiTwoS_sub_ckmrvXiFourS.mul isBigO_ckmrvLS).mul isBigO_kleinModularJ
    refine h.congr_right fun τ => ?_
    rw [exp_neg_pi_mul_exp_neg_pi, exp_neg_two_pi_mul_exp_two_pi]
  have h := ((hA.mul isBigO_ckmrvL).congr_right fun τ => one_mul _).add
    (hB.trans isBigO_one_real_norm_coe)
  refine h.congr_left fun τ => ?_
  simp [ckmrvPsiBasis]
  ring

/-- `j - E₁₄/Δ = E₄² (E₄ - E₆)/Δ = O(1)`. -/
theorem isBigO_kleinModularJ_sub_factor :
    (fun τ : ℍ => kleinModularJ τ - ckmrvModularFactor τ 2) =O[atImInfty]
      fun _ : ℍ => (1 : ℝ) := by
  have h := ((tendsto_eisensteinFour_atImInfty.pow 2).isBigO_one ℝ).mul
    (isBigO_eisensteinFour_sub_eisensteinSix.mul isBigO_discriminant_inv)
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · dsimp only
    rw [ckmrvModularFactor_eq_products, kleinModularJ]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  · dsimp only
    rw [exp_neg_two_pi_mul_exp_two_pi, one_mul]

/-! ## The dimension-eight minus kernel -/

/-- The `j`-th `τ`-coefficient of the dimension-eight minus kernel. -/
def eightMinusTauCoeff (j : Fin 3) (τ : ℍ) : ℂ :=
  ∑ i, ckmrvPsiBasis τ i * ckmrvModularFactor τ (![3, 2, 1] i) *
    ckmrvEightMinusCore (kleinModularJ τ) i j

theorem ckmrvEightMinusKernel_eq_sum (τ z : ℍ) :
    ckmrvEightMinusKernel τ z =
      (kleinModularJ τ - kleinModularJ z)⁻¹ *
        ∑ j, ((ckmrvMinusScale * ModularForm.discriminant z)⁻¹ *
          (ckmrvModularFactor z (![6, 5, 4] j) * ckmrvTildePsiBasis z j)) *
            eightMinusTauCoeff j τ := by
  simp only [ckmrvEightMinusKernel, ckmrvCoreContraction, ckmrvEightMinusCoefficientMatrix,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply, Matrix.smul_apply, smul_eq_mul,
    eightMinusTauCoeff, Fin.sum_univ_three, mul_inv]
  ring

theorem eightMinusTauCoeff_zero (τ : ℍ) :
    eightMinusTauCoeff 0 τ = -(2 * 1728) * ModularForm.E₄ τ := by
  simp [eightMinusTauCoeff, Fin.sum_univ_three, ckmrvPsiBasis, ckmrvEightMinusCore,
    ckmrvModularFactor]
  ring

theorem eightMinusTauCoeff_one (τ : ℍ) :
    eightMinusTauCoeff 1 τ =
      (ckmrvPsiBasis τ 1 - ckmrvPsiBasis τ 2) * kleinModularJ τ -
        ckmrvPsiBasis τ 1 * (kleinModularJ τ - ckmrvModularFactor τ 2) +
          1728 * ckmrvPsiBasis τ 2 := by
  have h1 : ckmrvModularFactor τ 1 = 1 := rfl
  simp [eightMinusTauCoeff, Fin.sum_univ_three, ckmrvEightMinusCore, h1]
  ring

theorem eightMinusTauCoeff_two (τ : ℍ) :
    eightMinusTauCoeff 2 τ =
      -((ckmrvPsiBasis τ 1 - ckmrvPsiBasis τ 2) * kleinModularJ τ) +
        ckmrvPsiBasis τ 1 * (kleinModularJ τ - ckmrvModularFactor τ 2) := by
  have h1 : ckmrvModularFactor τ 1 = 1 := rfl
  simp [eightMinusTauCoeff, Fin.sum_univ_three, ckmrvEightMinusCore, h1]
  ring

theorem isBigO_eightMinusTauCoeff (j : Fin 3) :
    eightMinusTauCoeff j =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  have hD := isBigO_ckmrvPsiBasis_one.mul isBigO_kleinModularJ_sub_factor
  have hD' : (fun τ : ℍ => ckmrvPsiBasis τ 1 * (kleinModularJ τ - ckmrvModularFactor τ 2))
      =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := hD.congr_right fun τ => mul_one _
  fin_cases j
  · have h := (((tendsto_eisensteinFour_atImInfty.isBigO_one ℝ).const_mul_left
      (-(2 * 1728) : ℂ)).trans isBigO_one_real_norm_coe)
    exact h.congr_left fun τ => (eightMinusTauCoeff_zero τ).symm
  · have h := (isBigO_psi_sub_mul_kleinModularJ.sub hD').add
      (isBigO_ckmrvPsiBasis_two.const_mul_left (1728 : ℂ))
    exact h.congr_left fun τ => (eightMinusTauCoeff_one τ).symm
  · have h := isBigO_psi_sub_mul_kleinModularJ.neg_left.add hD'
    exact h.congr_left fun τ => (eightMinusTauCoeff_two τ).symm

/-- **CKMRV (4.21), dimension eight, minus kernel.** For fixed `z`,
`K₋(τ, z) = O(|τ| e^{-2π Im τ})` as `Im τ → ∞`. -/
theorem isBigO_ckmrvEightMinusKernel (z : ℍ) :
    (fun τ : ℍ => ckmrvEightMinusKernel τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) := by
  have hsum : (fun τ : ℍ => ∑ j, ((ckmrvMinusScale * ModularForm.discriminant z)⁻¹ *
      (ckmrvModularFactor z (![6, 5, 4] j) * ckmrvTildePsiBasis z j)) *
        eightMinusTauCoeff j τ) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
    simp only [Fin.sum_univ_three]
    exact (((isBigO_eightMinusTauCoeff 0).const_mul_left _).add
      ((isBigO_eightMinusTauCoeff 1).const_mul_left _)).add
      ((isBigO_eightMinusTauCoeff 2).const_mul_left _)
  have h := (isBigO_kleinModularJ_sub_inv z).mul hsum
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · exact (ckmrvEightMinusKernel_eq_sum τ z).symm
  · dsimp only
    ring

/-! ## The dimension-eight plus kernel -/

theorem eisensteinTwo_vadd_one (τ : ℍ) :
    EisensteinSeries.E2 ((1 : ℝ) +ᵥ τ) = EisensteinSeries.E2 τ := by
  rw [vadd_one_eq_T_smul, eisensteinTwo_T]

theorem eisensteinFour_vadd_one (τ : ℍ) : ModularForm.E₄ ((1 : ℝ) +ᵥ τ) = ModularForm.E₄ τ :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods ModularForm.E₄ τ one_mem_strictPeriods_SL

theorem eisensteinSix_vadd_one (τ : ℍ) : ModularForm.E₆ ((1 : ℝ) +ᵥ τ) = ModularForm.E₆ τ :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods ModularForm.E₆ τ one_mem_strictPeriods_SL

/-- `E₆ - 2 E₂ E₄ + E₂² = O(e^{-2π Im τ})`. -/
theorem isBigO_eisenstein_quasimodular :
    (fun τ : ℍ => ModularForm.E₆ τ - 2 * EisensteinSeries.E2 τ * ModularForm.E₄ τ +
      EisensteinSeries.E2 τ ^ 2) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have h2 := E2_mdifferentiable
  have hfun : (fun τ : ℍ => ModularForm.E₆ τ - 2 * EisensteinSeries.E2 τ * ModularForm.E₄ τ +
      EisensteinSeries.E2 τ ^ 2) =
      (ModularForm.E₆ : ℍ → ℂ) - (fun _ => (2 : ℂ)) * EisensteinSeries.E2 *
        (ModularForm.E₄ : ℍ → ℂ) + EisensteinSeries.E2 * EisensteinSeries.E2 := by
    funext τ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  have h := isBigO_exp_of_periodic (h := 1) one_pos
    (f := fun τ : ℍ => ModularForm.E₆ τ - 2 * EisensteinSeries.E2 τ * ModularForm.E₄ τ +
      EisensteinSeries.E2 τ ^ 2)
    (by rw [hfun]; exact (h6.sub ((mdifferentiable_const.mul h2).mul h4)).add (h2.mul h2))
    (fun τ => by
      show ModularForm.E₆ ((1 : ℝ) +ᵥ τ) - 2 * EisensteinSeries.E2 ((1 : ℝ) +ᵥ τ) *
          ModularForm.E₄ ((1 : ℝ) +ᵥ τ) + EisensteinSeries.E2 ((1 : ℝ) +ᵥ τ) ^ 2 =
        ModularForm.E₆ τ - 2 * EisensteinSeries.E2 τ * ModularForm.E₄ τ +
          EisensteinSeries.E2 τ ^ 2
      rw [eisensteinTwo_vadd_one, eisensteinFour_vadd_one, eisensteinSix_vadd_one])
    (by
      have hl := (tendsto_eisensteinSix_atImInfty.sub
        (((tendsto_const_nhds (x := (2 : ℂ))).mul eisensteinTwo_tendsto_one_atImInfty).mul
          tendsto_eisensteinFour_atImInfty)).add (eisensteinTwo_tendsto_one_atImInfty.pow 2)
      have h0 : (1 : ℂ) - 2 * 1 * 1 + 1 ^ 2 = 0 := by norm_num
      rw [h0] at hl
      exact hl)
  simpa using h

/-- `E₄ - E₂ = O(e^{-2π Im τ})`. -/
theorem isBigO_eisensteinFour_sub_eisensteinTwo :
    (fun τ : ℍ => ModularForm.E₄ τ - EisensteinSeries.E2 τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * π * τ.im) := by
  have h := isBigO_exp_of_periodic (h := 1) one_pos
    (f := fun τ : ℍ => ModularForm.E₄ τ - EisensteinSeries.E2 τ)
    ((ModularFormClass.holo ModularForm.E₄).sub E2_mdifferentiable)
    (fun τ => by
      show ModularForm.E₄ ((1 : ℝ) +ᵥ τ) - EisensteinSeries.E2 ((1 : ℝ) +ᵥ τ) =
        ModularForm.E₄ τ - EisensteinSeries.E2 τ
      rw [eisensteinTwo_vadd_one, eisensteinFour_vadd_one])
    (by simpa using tendsto_eisensteinFour_atImInfty.sub eisensteinTwo_tendsto_one_atImInfty)
  simpa using h

theorem isBigO_coe_norm : (fun τ : ℍ => (τ : ℂ)) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun τ => by simp)

theorem isBigO_exp_neg_two_pi_norm_mul :
    (fun τ : ℍ => Real.exp (-2 * π * τ.im)) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) :=
  (isBigO_one_real_norm_coe.mul (isBigO_refl _ _)).congr_left fun _ => one_mul _

theorem isBigO_const_exp_two_pi (c : ℂ) :
    (fun _ : ℍ => c) =O[atImInfty] fun τ : ℍ => Real.exp (2 * π * τ.im) := by
  refine IsBigO.of_bound ‖c‖ (Eventually.of_forall fun τ => ?_)
  have h1 : (1 : ℝ) ≤ Real.exp (2 * π * τ.im) := by
    rw [Real.one_le_exp_iff]
    nlinarith [Real.pi_pos, τ.im_pos]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith [norm_nonneg c]

/-- Bounded times `|τ|` plus bounded is `O(|τ|)`. -/
theorem isBigO_coe_mul_add {a b : ℍ → ℂ} {ca cb : ℂ} (ha : Tendsto a atImInfty (𝓝 ca))
    (hb : Tendsto b atImInfty (𝓝 cb)) :
    (fun τ : ℍ => (τ : ℂ) * a τ + b τ) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  have h1 := (isBigO_coe_norm.mul (ha.isBigO_one ℝ)).congr_right fun τ => mul_one _
  exact h1.add ((hb.isBigO_one ℝ).trans isBigO_one_real_norm_coe)

theorem isBigO_ckmrvPhiBasis_one :
    (fun τ : ℍ => ckmrvPhiBasis τ 1) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  have h := isBigO_coe_mul_add eisensteinTwo_tendsto_one_atImInfty
    (tendsto_const_nhds (x := -(3 * Complex.I / (Real.pi : ℂ))))
  refine h.congr_left fun τ => ?_
  simp [ckmrvPhiBasis, sub_eq_add_neg]

theorem isBigO_ckmrvPhiBasis_two :
    (fun τ : ℍ => ckmrvPhiBasis τ 2) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  have h := isBigO_coe_mul_add (eisensteinTwo_tendsto_one_atImInfty.pow 2)
    ((tendsto_const_nhds (x := -(6 * Complex.I / (Real.pi : ℂ)))).mul
      eisensteinTwo_tendsto_one_atImInfty)
  refine h.congr_left fun τ => ?_
  simp [ckmrvPhiBasis]
  ring

/-- The `j`-th coefficient of the dimension-eight plus kernel (it also depends on `z`). -/
def eightPlusTauCoeff (j : Fin 3) (τ z : ℍ) : ℂ :=
  ∑ i, ckmrvPhiBasis τ i * ckmrvModularFactor τ (![4, 3, 2] i) *
    ckmrvEightPlusCore (kleinModularJ τ - kleinModularJ z) i j

theorem ckmrvEightPlusKernel_eq_sum (τ z : ℍ) :
    ckmrvEightPlusKernel τ z =
      (kleinModularJ τ - kleinModularJ z)⁻¹ *
        ∑ j, ((ckmrvPlusScale * ModularForm.discriminant z)⁻¹ *
          (ckmrvModularFactor z (![7, 6, 5] j) * ckmrvTildePhiBasis z j)) *
            eightPlusTauCoeff j τ z := by
  simp only [ckmrvEightPlusKernel, ckmrvCoreContraction, ckmrvEightPlusCoefficientMatrix,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply, Matrix.smul_apply, smul_eq_mul,
    eightPlusTauCoeff, Fin.sum_univ_three, mul_inv]
  ring

theorem eightPlusTauCoeff_zero (τ z : ℍ) :
    eightPlusTauCoeff 0 τ z =
      (kleinModularJ τ - kleinModularJ z) *
          ((τ : ℂ) * (ModularForm.E₆ τ - 2 * EisensteinSeries.E2 τ * ModularForm.E₄ τ +
              EisensteinSeries.E2 τ ^ 2) +
            6 * (Complex.I / (Real.pi : ℂ)) * (ModularForm.E₄ τ - EisensteinSeries.E2 τ)) +
        ckmrvPhiBasis τ 2 * (kleinModularJ z - (kleinModularJ τ - ckmrvModularFactor τ 2)) := by
  have h3 : ckmrvModularFactor τ 3 = ModularForm.E₄ τ := rfl
  have h4 : ckmrvModularFactor τ 4 = ModularForm.E₆ τ := rfl
  simp [eightPlusTauCoeff, Fin.sum_univ_three, ckmrvEightPlusCore, ckmrvPhiBasis, h3, h4]
  ring

theorem eightPlusTauCoeff_one (τ z : ℍ) :
    eightPlusTauCoeff 1 τ z = -2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) := by
  have h3 : ckmrvModularFactor τ 3 = ModularForm.E₄ τ := rfl
  simp [eightPlusTauCoeff, Fin.sum_univ_three, ckmrvEightPlusCore, h3]
  ring

theorem eightPlusTauCoeff_two (τ z : ℍ) :
    eightPlusTauCoeff 2 τ z = (τ : ℂ) * ModularForm.E₆ τ := by
  have h4 : ckmrvModularFactor τ 4 = ModularForm.E₆ τ := rfl
  simp [eightPlusTauCoeff, Fin.sum_univ_three, ckmrvEightPlusCore, ckmrvPhiBasis, h4]

theorem isBigO_eightPlusTauCoeff (j : Fin 3) (z : ℍ) :
    (fun τ : ℍ => eightPlusTauCoeff j τ z) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
  fin_cases j
  · -- `g X + φ₂ (j(z) - D)`
    have hX : (fun τ : ℍ => (τ : ℂ) * (ModularForm.E₆ τ -
        2 * EisensteinSeries.E2 τ * ModularForm.E₄ τ + EisensteinSeries.E2 τ ^ 2) +
          6 * (Complex.I / (Real.pi : ℂ)) * (ModularForm.E₄ τ - EisensteinSeries.E2 τ))
        =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) :=
      (isBigO_coe_norm.mul isBigO_eisenstein_quasimodular).add
        ((isBigO_eisensteinFour_sub_eisensteinTwo.const_mul_left _).trans
          isBigO_exp_neg_two_pi_norm_mul)
    have hg : (fun τ : ℍ => kleinModularJ τ - kleinModularJ z) =O[atImInfty]
        fun τ : ℍ => Real.exp (2 * π * τ.im) :=
      isBigO_kleinModularJ.sub (isBigO_const_exp_two_pi _)
    have h1 := (hg.mul hX).congr_right fun τ => by
      rw [mul_comm (‖(τ : ℂ)‖), ← mul_assoc, mul_comm (Real.exp (2 * π * τ.im)),
        exp_neg_two_pi_mul_exp_two_pi, one_mul]
    have hD : (fun τ : ℍ => kleinModularJ z - (kleinModularJ τ - ckmrvModularFactor τ 2))
        =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
      (isBigO_const_one ℝ (kleinModularJ z) atImInfty).sub isBigO_kleinModularJ_sub_factor
    have h2 := (isBigO_ckmrvPhiBasis_two.mul hD).congr_right fun τ => mul_one _
    exact (h1.add h2).congr_left fun τ => (eightPlusTauCoeff_zero τ z).symm
  · have h := ((isBigO_ckmrvPhiBasis_one.mul
      (tendsto_eisensteinFour_atImInfty.isBigO_one ℝ)).congr_right fun τ => mul_one _)
    exact (h.const_mul_left (-2 : ℂ)).congr_left fun τ => (eightPlusTauCoeff_one τ z).symm
  · have h := ((isBigO_coe_norm.mul
      (tendsto_eisensteinSix_atImInfty.isBigO_one ℝ)).congr_right fun τ => mul_one _)
    exact h.congr_left fun τ => (eightPlusTauCoeff_two τ z).symm

/-- **CKMRV (4.21), dimension eight, plus kernel.** For fixed `z`,
`K₊(τ, z) = O(|τ| e^{-2π Im τ})` as `Im τ → ∞`. -/
theorem isBigO_ckmrvEightPlusKernel (z : ℍ) :
    (fun τ : ℍ => ckmrvEightPlusKernel τ z) =O[atImInfty]
      fun τ : ℍ => ‖(τ : ℂ)‖ * Real.exp (-2 * π * τ.im) := by
  have hsum : (fun τ : ℍ => ∑ j, ((ckmrvPlusScale * ModularForm.discriminant z)⁻¹ *
      (ckmrvModularFactor z (![7, 6, 5] j) * ckmrvTildePhiBasis z j)) *
        eightPlusTauCoeff j τ z) =O[atImInfty] fun τ : ℍ => ‖(τ : ℂ)‖ := by
    simp only [Fin.sum_univ_three]
    exact (((isBigO_eightPlusTauCoeff 0 z).const_mul_left _).add
      ((isBigO_eightPlusTauCoeff 1 z).const_mul_left _)).add
      ((isBigO_eightPlusTauCoeff 2 z).const_mul_left _)
  have h := (isBigO_kleinModularJ_sub_inv z).mul hsum
  refine h.congr' (Eventually.of_forall fun τ => ?_) (Eventually.of_forall fun τ => ?_)
  · exact (ckmrvEightPlusKernel_eq_sum τ z).symm
  · dsimp only
    ring

end E8Leech
