import E8Leech.ThetaFunctions
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Jacobi's identity, the theta product of the discriminant, and the lambda function

Known answers are fixed first and checked by level-one dimension counts:

* `P = V + W - U` is anti-invariant under `S` and `T`, so `P²` is a level-one weight four
  cusp form, hence `0`. This is Jacobi's identity `U = V + W`; no `Γ(2)` dimension theory is
  needed.
* `Q = (U V W)²` is a level-one weight twelve cusp form, so `Q = c Δ`. Dividing by
  `q = exp(2π i τ)` and letting `Im τ → ∞` identifies `c = 2⁸ = 256`.

`Δ ≠ 0` then gives `U, V, W ≠ 0`, so `λ = V / U` is holomorphic with `λ ≠ 0, 1`
(CKMRV Section 2.1). The inversion `λ ∘ S = 1 - λ` and `S i = i` give `λ(i) = 1/2`.
On the positive imaginary axis `U, V, W` are positive reals and `0 < λ < 1`.
Holomorphic logarithm branches of `λ` and `1 - λ` are not constructed here.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## A level-one cusp form from the `S` and `T` laws -/

private theorem slash_S_apply_theta {k : ℤ} (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] ModularGroup.S) τ = f (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S]

private theorem slash_T_apply_theta {k : ℤ} (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] ModularGroup.T) τ = f (ModularGroup.T • τ) := by
  rw [ModularForm.SL_slash_apply]
  have hd : denom ModularGroup.T (τ : ℂ) = 1 := by
    simp [denom, ModularGroup.T, Matrix.SpecialLinearGroup.map]
  rw [hd, one_zpow, mul_one]

theorem slash_invariant_of_S_T (k : ℤ) (f : ℍ → ℂ)
    (hT : ∀ τ : ℍ, f (ModularGroup.T • τ) = f τ)
    (hS : ∀ τ : ℍ, f (ModularGroup.S • τ) = (τ : ℂ) ^ k * f τ) :
    ∀ γ : SL(2, ℤ), f ∣[k] γ = f := by
  refine SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_
  · funext τ
    rw [slash_S_apply_theta, hS, mul_right_comm, ← zpow_add₀ τ.ne_zero, add_neg_cancel,
      zpow_zero, one_mul]
  · funext τ
    rw [slash_T_apply_theta, hT]

/-- A holomorphic function with the level-one `S`/`T` laws that tends to `0` at `i∞`. -/
def levelOneCuspFormOf (k : ℤ) (f : ℍ → ℂ)
    (hT : ∀ τ : ℍ, f (ModularGroup.T • τ) = f τ)
    (hS : ∀ τ : ℍ, f (ModularGroup.S • τ) = (τ : ℂ) ^ k * f τ)
    (hf : MDiff f) (h0 : Tendsto f atImInfty (𝓝 0)) : CuspForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_invariant_of_S_T k f hT hS A
  holo' := hf
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_invariant_of_S_T k f hT hS γ]
    exact h0

@[simp]
theorem levelOneCuspFormOf_apply (k : ℤ) (f : ℍ → ℂ) (hT hS hf h0) (τ : ℍ) :
    levelOneCuspFormOf k f hT hS hf h0 τ = f τ :=
  rfl

/-! ## Jacobi's identity -/

/-- Jacobi's defect `P = V + W - U`. -/
def jacobiDefect (τ : ℍ) : ℂ := thetaV τ + thetaW τ - thetaU τ

theorem jacobiDefect_T (τ : ℍ) : jacobiDefect (ModularGroup.T • τ) = -jacobiDefect τ := by
  rw [jacobiDefect, jacobiDefect, thetaU_T, thetaV_T, thetaW_T]
  ring

theorem jacobiDefect_S (τ : ℍ) :
    jacobiDefect (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * jacobiDefect τ := by
  rw [jacobiDefect, jacobiDefect, thetaU_S, thetaV_S, thetaW_S]
  ring

theorem mdifferentiable_jacobiDefect : MDiff jacobiDefect :=
  (mdifferentiable_thetaV.add mdifferentiable_thetaW).sub mdifferentiable_thetaU

theorem tendsto_jacobiDefect_atImInfty : Tendsto jacobiDefect atImInfty (𝓝 0) := by
  have h := (tendsto_thetaV_atImInfty.add tendsto_thetaW_atImInfty).sub tendsto_thetaU_atImInfty
  rw [show (0 : ℂ) + 1 - 1 = 0 by ring] at h
  exact h

/-- The weight four cusp form `P²`. -/
def jacobiDefectSqCuspForm : CuspForm 𝒮ℒ 4 :=
  levelOneCuspFormOf 4 (fun τ => jacobiDefect τ * jacobiDefect τ)
    (fun τ => by rw [jacobiDefect_T]; ring)
    (fun τ => by rw [jacobiDefect_S]; simp only [zpow_ofNat]; ring)
    (mdifferentiable_jacobiDefect.mul mdifferentiable_jacobiDefect)
    (by
      have h := tendsto_jacobiDefect_atImInfty.mul tendsto_jacobiDefect_atImInfty
      rw [mul_zero] at h
      exact h)

theorem jacobiDefect_eq_zero (τ : ℍ) : jacobiDefect τ = 0 := by
  have hzero : jacobiDefectSqCuspForm = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) _
  have h := congrArg (fun G : CuspForm 𝒮ℒ 4 => G τ) hzero
  simp only [jacobiDefectSqCuspForm, levelOneCuspFormOf_apply, zero_apply] at h
  exact mul_self_eq_zero.mp h

/-- Jacobi's identity `θ₃⁴ = θ₂⁴ + θ₄⁴`, i.e. `U = V + W`. -/
theorem thetaU_eq_add (τ : ℍ) : thetaU τ = thetaV τ + thetaW τ := by
  have h := jacobiDefect_eq_zero τ
  rw [jacobiDefect] at h
  linear_combination -h

/-! ## The theta product of the discriminant -/

/-- `Q = (U V W)²`. -/
def thetaProductSq (τ : ℍ) : ℂ := (thetaU τ * thetaV τ * thetaW τ) ^ 2

theorem thetaProductSq_T (τ : ℍ) : thetaProductSq (ModularGroup.T • τ) = thetaProductSq τ := by
  rw [thetaProductSq, thetaProductSq, thetaU_T, thetaV_T, thetaW_T]
  ring

theorem thetaProductSq_S (τ : ℍ) :
    thetaProductSq (ModularGroup.S • τ) = (τ : ℂ) ^ (12 : ℤ) * thetaProductSq τ := by
  rw [thetaProductSq, thetaProductSq, thetaU_S, thetaV_S, thetaW_S]
  simp only [zpow_ofNat]
  ring

theorem mdifferentiable_thetaProductSq : MDiff thetaProductSq := by
  have h := (mdifferentiable_thetaU.mul mdifferentiable_thetaV).mul mdifferentiable_thetaW
  have hf : thetaProductSq = thetaU * thetaV * thetaW * (thetaU * thetaV * thetaW) := by
    funext τ
    simp only [thetaProductSq, Pi.mul_apply]
    ring
  rw [hf]
  exact h.mul h

theorem tendsto_thetaProductSq_atImInfty : Tendsto thetaProductSq atImInfty (𝓝 0) := by
  have h := ((tendsto_thetaU_atImInfty.mul tendsto_thetaV_atImInfty).mul
    tendsto_thetaW_atImInfty).pow 2
  rw [show ((1 : ℂ) * 0 * 1) ^ 2 = 0 by ring] at h
  exact h

/-- The weight twelve cusp form `(U V W)²`. -/
def thetaProductSqCuspForm : CuspForm 𝒮ℒ 12 :=
  levelOneCuspFormOf 12 thetaProductSq thetaProductSq_T thetaProductSq_S
    mdifferentiable_thetaProductSq tendsto_thetaProductSq_atImInfty

/-- Pull out the cusp parameter: `θ₂ = q^(1/8) θ(τ/2, τ)` gives `Q = q (θ(τ/2,τ) θ₃ θ₄)⁸`. -/
theorem thetaProductSq_eq_qParam_mul (τ : ℍ) :
    thetaProductSq τ = Function.Periodic.qParam 1 τ *
      (jacobiTheta₂ ((τ : ℂ) / 2) τ * thetaThree τ * thetaFour τ) ^ 8 := by
  have he : cexp (π * I * (τ : ℂ) / 4) ^ 8 = Function.Periodic.qParam 1 τ := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← he, thetaProductSq, thetaU, thetaV, thetaW, thetaTwo]
  ring

theorem tendsto_thetaProduct_div_qParam :
    Tendsto (fun τ : ℍ => (jacobiTheta₂ ((τ : ℂ) / 2) τ * thetaThree τ * thetaFour τ) ^ 8)
      atImInfty (𝓝 256) := by
  have h := ((tendsto_jacobiTheta₂_half_atImInfty.mul tendsto_thetaThree_atImInfty).mul
    tendsto_thetaFour_atImInfty).pow 8
  rw [show ((2 : ℂ) * 1 * 1) ^ 8 = 256 by norm_num] at h
  exact h

/-- `(θ₂ θ₃ θ₄)⁸ = 256 Δ`. -/
theorem thetaProductSq_eq_discriminant (τ : ℍ) :
    thetaProductSq τ = 256 * ModularForm.discriminant τ := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve thetaProductSqCuspForm
  have hpt : ∀ w : ℍ, thetaProductSq w = c * ModularForm.discriminant w := by
    intro w
    have h := congrArg (fun G : CuspForm 𝒮ℒ 12 => G w) hc
    simp only [smul_apply, CuspForm.coe_discriminant, thetaProductSqCuspForm,
      levelOneCuspFormOf_apply, smul_eq_mul] at h
    exact h.symm
  have hcmp : ∀ w : ℍ, (jacobiTheta₂ ((w : ℂ) / 2) w * thetaThree w * thetaFour w) ^ 8 =
      c * ∏' n : ℕ, (1 - ModularForm.eta_q n w) ^ 24 := by
    intro w
    have h := hpt w
    rw [thetaProductSq_eq_qParam_mul, ModularForm.discriminant_eq_q_prod] at h
    have hq : Function.Periodic.qParam 1 (w : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have h' : Function.Periodic.qParam 1 (w : ℂ) *
        ((jacobiTheta₂ ((w : ℂ) / 2) w * thetaThree w * thetaFour w) ^ 8 -
          c * ∏' n : ℕ, (1 - ModularForm.eta_q n w) ^ 24) = 0 := by
      rw [mul_sub, h]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hq)
  have hlim : Tendsto (fun w : ℍ => c * ∏' n : ℕ, (1 - ModularForm.eta_q n w) ^ 24)
      atImInfty (𝓝 (c * 1)) :=
    tendsto_const_nhds.mul ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow
  have h256 : (256 : ℂ) = c * 1 :=
    tendsto_nhds_unique (tendsto_thetaProduct_div_qParam.congr hcmp) hlim
  rw [hpt τ, mul_one] at *
  rw [← h256]

/-! ## Non-vanishing and the lambda function -/

theorem thetaU_mul_thetaV_mul_thetaW_ne_zero (τ : ℍ) :
    thetaU τ * thetaV τ * thetaW τ ≠ 0 := by
  intro h
  have hq := thetaProductSq_eq_discriminant τ
  rw [thetaProductSq, h, zero_pow two_ne_zero] at hq
  exact ModularForm.discriminant_ne_zero τ
    ((mul_eq_zero.mp hq.symm).resolve_left (by norm_num))

theorem thetaU_ne_zero (τ : ℍ) : thetaU τ ≠ 0 := by
  have h := thetaU_mul_thetaV_mul_thetaW_ne_zero τ
  intro hu
  exact h (by rw [hu]; ring)

theorem thetaV_ne_zero (τ : ℍ) : thetaV τ ≠ 0 := by
  have h := thetaU_mul_thetaV_mul_thetaW_ne_zero τ
  intro hv
  exact h (by rw [hv]; ring)

theorem thetaW_ne_zero (τ : ℍ) : thetaW τ ≠ 0 := by
  have h := thetaU_mul_thetaV_mul_thetaW_ne_zero τ
  intro hw
  exact h (by rw [hw]; ring)

/-- The modular lambda function `λ = V / U = θ₂⁴ / θ₃⁴`. -/
def modularLambda (τ : ℍ) : ℂ := thetaV τ / thetaU τ

theorem one_sub_modularLambda (τ : ℍ) : 1 - modularLambda τ = thetaW τ / thetaU τ := by
  rw [modularLambda, eq_div_iff (thetaU_ne_zero τ), sub_mul, one_mul,
    div_mul_cancel₀ _ (thetaU_ne_zero τ), thetaU_eq_add]
  ring

theorem modularLambda_ne_zero (τ : ℍ) : modularLambda τ ≠ 0 :=
  div_ne_zero (thetaV_ne_zero τ) (thetaU_ne_zero τ)

theorem modularLambda_ne_one (τ : ℍ) : modularLambda τ ≠ 1 := by
  intro h
  have h' := one_sub_modularLambda τ
  rw [h, sub_self] at h'
  exact div_ne_zero (thetaW_ne_zero τ) (thetaU_ne_zero τ) h'.symm

theorem modularLambda_S (τ : ℍ) :
    modularLambda (ModularGroup.S • τ) = 1 - modularLambda τ := by
  rw [one_sub_modularLambda, modularLambda, thetaV_S, thetaU_S]
  have hτ : (τ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 τ.ne_zero
  field_simp [thetaU_ne_zero τ, hτ, τ.ne_zero]

theorem modularLambda_T (τ : ℍ) :
    modularLambda (ModularGroup.T • τ) = modularLambda τ / (modularLambda τ - 1) := by
  have hl : modularLambda τ - 1 = -(thetaW τ / thetaU τ) := by
    rw [← one_sub_modularLambda]
    ring
  rw [hl, modularLambda, modularLambda, thetaV_T, thetaU_T]
  field_simp [thetaU_ne_zero τ, thetaW_ne_zero τ]

theorem mdifferentiable_modularLambda : MDiff modularLambda := by
  intro τ
  exact (mdifferentiable_thetaV τ).div (mdifferentiable_thetaU τ) (thetaU_ne_zero τ)

theorem tendsto_modularLambda_atImInfty : Tendsto modularLambda atImInfty (𝓝 0) := by
  have h := tendsto_thetaV_atImInfty.div tendsto_thetaU_atImInfty one_ne_zero
  rw [zero_div] at h
  exact h

theorem S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul]
  change -1 / Complex.I = Complex.I
  rw [neg_div, one_div, Complex.inv_I, neg_neg]

/-- The known special value `λ(i) = 1/2`, from `S i = i` and `λ ∘ S = 1 - λ`. -/
theorem modularLambda_I : modularLambda UpperHalfPlane.I = 1 / 2 := by
  have h := modularLambda_S UpperHalfPlane.I
  rw [S_smul_I] at h
  linear_combination h / 2

/-! ## The positive imaginary axis -/

private theorem thetaThree_I_mul_eq (t : ℝ) :
    thetaThree (Complex.I * t) = ((∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
  rw [thetaThree_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem thetaTwo_I_mul_eq (t : ℝ) :
    thetaTwo (Complex.I * t) =
      ((∑' n : ℤ, Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) := by
  rw [thetaTwo_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem summable_exp_neg_sq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Summable fun n : ℤ => Real.exp (-π * ((n : ℝ) + a) ^ 2 * t) := by
  have h := summable_norm_iff.mpr
    ((summable_jacobiTheta₂_term_iff ((a * t : ℝ) * Complex.I) (t * Complex.I)).mpr
      (by simpa using ht))
  refine (h.mul_left (Real.exp (-π * a ^ 2 * t))).congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one]
  ring

private theorem tsum_exp_neg_sq_pos {t : ℝ} (ht : 0 < t) (a : ℝ) :
    0 < ∑' n : ℤ, Real.exp (-π * ((n : ℝ) + a) ^ 2 * t) :=
  (summable_exp_neg_sq ht a).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- The point `i t` of the upper half-plane. -/
def imagAxisPoint (t : ℝ) (ht : 0 < t) : ℍ := ⟨Complex.I * t, by simpa using ht⟩

theorem thetaU_imagAxis_pos {t : ℝ} (ht : 0 < t) :
    ∃ u : ℝ, 0 < u ∧ thetaU (imagAxisPoint t ht) = u := by
  refine ⟨(∑' n : ℤ, Real.exp (-π * ((n : ℝ) + 0) ^ 2 * t)) ^ 4,
    pow_pos (tsum_exp_neg_sq_pos ht 0) 4, ?_⟩
  change thetaThree (Complex.I * t) ^ 4 = _
  rw [thetaThree_I_mul_eq]
  push_cast
  simp

theorem thetaV_imagAxis_pos {t : ℝ} (ht : 0 < t) :
    ∃ v : ℝ, 0 < v ∧ thetaV (imagAxisPoint t ht) = v := by
  refine ⟨(∑' n : ℤ, Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t)) ^ 4,
    pow_pos (tsum_exp_neg_sq_pos ht (1 / 2)) 4, ?_⟩
  change thetaTwo (Complex.I * t) ^ 4 = _
  rw [thetaTwo_I_mul_eq]
  push_cast
  rfl

theorem S_smul_imagAxisPoint_inv {t : ℝ} (ht : 0 < t) :
    ModularGroup.S • imagAxisPoint t⁻¹ (inv_pos.mpr ht) = imagAxisPoint t ht := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul]
  change -1 / (Complex.I * ((t⁻¹ : ℝ) : ℂ)) = Complex.I * (t : ℂ)
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp
  rw [Complex.I_sq]

theorem thetaW_imagAxis_pos {t : ℝ} (ht : 0 < t) :
    ∃ w : ℝ, 0 < w ∧ thetaW (imagAxisPoint t ht) = w := by
  obtain ⟨v, hv, hV⟩ := thetaV_imagAxis_pos (inv_pos.mpr ht)
  have h := thetaW_S (imagAxisPoint t⁻¹ (inv_pos.mpr ht))
  rw [S_smul_imagAxisPoint_inv ht, hV] at h
  refine ⟨(t⁻¹) ^ 2 * v, mul_pos (pow_pos (inv_pos.mpr ht) 2) hv, ?_⟩
  rw [h]
  change -(Complex.I * ((t⁻¹ : ℝ) : ℂ)) ^ 2 * (v : ℂ) = _
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- On the positive imaginary axis, `0 < λ(i t) < 1`. -/
theorem modularLambda_imagAxis_mem_Ioo {t : ℝ} (ht : 0 < t) :
    ∃ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 ∧ modularLambda (imagAxisPoint t ht) = l := by
  obtain ⟨v, hv, hV⟩ := thetaV_imagAxis_pos ht
  obtain ⟨w, hw, hW⟩ := thetaW_imagAxis_pos ht
  have hU : thetaU (imagAxisPoint t ht) = ((v + w : ℝ) : ℂ) := by
    rw [thetaU_eq_add, hV, hW]
    push_cast
    ring
  refine ⟨v / (v + w), ⟨div_pos hv (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩,
    ?_⟩
  rw [modularLambda, hV, hU]
  push_cast
  ring

end E8Leech
