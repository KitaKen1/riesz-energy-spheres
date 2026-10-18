import E8Leech.ImagAxisDerivative
import E8Leech.CKMRVAxisNumerator
import E8Leech.KronSeries

/-!
# Derivatives of the axis generators

The real generators `E₂(it), V(it), W(it), L(it)` of the kernel numerators satisfy the first-order
system

`E₂' = −(π/6)(E₂² − E₄)`, `V' = −(π/3) V (E₂ + V + 2W)`, `W' = −(π/3) W (E₂ − 2V − W)`,
`L' = −π W`,

with `E₄ = V² + VW + W²`. Hence every derivative in `t` of a polynomial in the generators is
again such a polynomial; this is used for the concavity argument at the corner `u = t = 1`.

* `hasDerivAt_axE2`, `hasDerivAt_axV`, `hasDerivAt_axW`, `hasDerivAt_axL`: the system.
* `axV_pos`, `axW_pos`, `axL_eq_log`: positivity and `L = log (V/(V + W))` on the axis.
* `nomeTheta4_pos`: `θ₄ > 0` for nomes below `1/3`.
-/

noncomputable section

namespace E8Leech

open Complex Set Taylor
open UpperHalfPlane hiding I
open scoped Real Topology

variable {t : ℝ}

theorem E₂_ofComplex_eq_axE2 (ht : 0 < t) : E₂ (ofComplex (I * t)) = (axE2 t : ℂ) := by
  rw [E₂_eq_E2]
  exact E2_imagPt_eq_axE2 ht

theorem H₂_ofComplex_eq_axV (ht : 0 < t) : H₂ (ofComplex (I * t)) = (axV t : ℂ) := by
  rw [H₂_eq_thetaV]
  exact thetaV_imagPt_eq_axV ht

theorem H₄_ofComplex_eq_axW (ht : 0 < t) : H₄ (ofComplex (I * t)) = (axW t : ℂ) := by
  rw [H₄_eq_thetaW]
  exact thetaW_imagPt_eq_axW ht

/-- `d/dt E₂(it) = −(π/6)(E₂² − E₄)`. -/
theorem hasDerivAt_axE2 (ht : 0 < t) :
    HasDerivAt axE2 (-(π / 6) * (axE2 t ^ 2 - axE4 (axV t) (axW t))) t := by
  have h := hasDerivAt_E₂_axis ht
  have hE4 : E₄ (ofComplex (I * t)) = (axE4 (axV t) (axW t) : ℂ) := E4_imagPt_eq_ax ht
  have hval : -(2 * (π : ℂ)) * (12⁻¹ * (E₂ (ofComplex (I * t)) * E₂ (ofComplex (I * t)) -
      E₄ (ofComplex (I * t)))) =
      ((-(π / 6) * (axE2 t ^ 2 - axE4 (axV t) (axW t)) : ℝ) : ℂ) := by
    rw [E₂_ofComplex_eq_axE2 ht, hE4]
    push_cast
    ring
  have hfun : (fun x : ℝ => E₂ (ofComplex (I * x))) =
      fun x : ℝ => EisensteinSeries.E2 (imagPt x) := funext fun x => E₂_eq_E2 _
  rw [hval, hfun] at h
  exact hasDerivAt_re_of_ofReal h

/-- `d/dt V(it) = −(π/3) V (E₂ + V + 2W)`. -/
theorem hasDerivAt_axV (ht : 0 < t) :
    HasDerivAt axV (-(π / 3) * (axV t * (axE2 t + axV t + 2 * axW t))) t := by
  have h := hasDerivAt_H₂_axis ht
  have hval : -(2 * (π : ℂ)) * (6⁻¹ * (H₂ (ofComplex (I * t)) *
      (E₂ (ofComplex (I * t)) + H₂ (ofComplex (I * t)) + 2 * H₄ (ofComplex (I * t))))) =
      ((-(π / 3) * (axV t * (axE2 t + axV t + 2 * axW t)) : ℝ) : ℂ) := by
    rw [E₂_ofComplex_eq_axE2 ht, H₂_ofComplex_eq_axV ht, H₄_ofComplex_eq_axW ht]
    push_cast
    ring
  have hfun : (fun x : ℝ => H₂ (ofComplex (I * x))) = fun x : ℝ => thetaV (imagPt x) :=
    funext fun x => H₂_eq_thetaV _
  rw [hval, hfun] at h
  exact hasDerivAt_re_of_ofReal h

/-- `d/dt W(it) = −(π/3) W (E₂ − 2V − W)`. -/
theorem hasDerivAt_axW (ht : 0 < t) :
    HasDerivAt axW (-(π / 3) * (axW t * (axE2 t - 2 * axV t - axW t))) t := by
  have h := hasDerivAt_H₄_axis ht
  have hval : -(2 * (π : ℂ)) * (6⁻¹ * (H₄ (ofComplex (I * t)) *
      (E₂ (ofComplex (I * t)) - 2 * H₂ (ofComplex (I * t)) - H₄ (ofComplex (I * t))))) =
      ((-(π / 3) * (axW t * (axE2 t - 2 * axV t - axW t)) : ℝ) : ℂ) := by
    rw [E₂_ofComplex_eq_axE2 ht, H₂_ofComplex_eq_axV ht, H₄_ofComplex_eq_axW ht]
    push_cast
    ring
  have hfun : (fun x : ℝ => H₄ (ofComplex (I * x))) = fun x : ℝ => thetaW (imagPt x) :=
    funext fun x => H₄_eq_thetaW _
  rw [hval, hfun] at h
  exact hasDerivAt_re_of_ofReal h

theorem axV_pos (ht : 0 < t) : 0 < axV t := by
  obtain ⟨hx0, hx1⟩ := exp_neg_pi_mem ht
  have hη := nomeEta1_pos hx0 hx1
  rw [axV_eq_nome ht]
  positivity

theorem axW_pos (ht : 0 < t) : 0 < axW t := by
  obtain ⟨w, hw, hW⟩ := thetaW_imagAxis_pos ht
  rw [← imagPt_eq_imagAxisPoint ht, thetaW_imagPt_eq_axW ht] at hW
  have h : axW t = w := by exact_mod_cast hW
  rw [h]
  exact hw

/-- On the axis `L = log (V/(V + W))`. -/
theorem axL_eq_log (ht : 0 < t) : axL t = Real.log (axV t / (axV t + axW t)) := by
  have h := ckmrvL_imagAxis ht
  rw [← imagPt_eq_imagAxisPoint ht] at h
  have hlam : (modularLambda (imagPt t)).re = axV t / (axV t + axW t) := by
    rw [modularLambda, thetaV_imagPt_eq_axV ht, thetaU_imagPt_eq_ax ht, ← ofReal_div, ofReal_re]
  rw [axL, h, ofReal_re, hlam]

/-- The algebra of `(log (V/(V + W)))'` for the system of the generators. -/
theorem log_quotient_deriv (V W E : ℝ) (hV : V ≠ 0) (hU : V + W ≠ 0) :
    (-(π / 3) * (V * (E + V + 2 * W)) * (V + W) -
        V * (-(π / 3) * (V * (E + V + 2 * W)) + -(π / 3) * (W * (E - 2 * V - W)))) /
      (V + W) ^ 2 / (V / (V + W)) = -(π * W) := by
  have hq : V / (V + W) ≠ 0 := div_ne_zero hV hU
  have e : -(π * W) * (V / (V + W)) * (V + W) ^ 2 = -(π * W) * (V * (V + W)) := by
    rw [mul_assoc, pow_two, ← mul_assoc (V / (V + W)), div_mul_cancel₀ _ hU]
  rw [div_eq_iff hq, div_eq_iff (pow_ne_zero 2 hU), e]
  ring

/-- `d/dt L(it) = −π W`. -/
theorem hasDerivAt_axL (ht : 0 < t) : HasDerivAt axL (-(π * axW t)) t := by
  have hV := hasDerivAt_axV ht
  have hW := hasDerivAt_axW ht
  have hVp := axV_pos ht
  have hWp := axW_pos ht
  have hU : 0 < axV t + axW t := by linarith
  have hq : 0 < axV t / (axV t + axW t) := div_pos hVp hU
  have hUd : HasDerivAt (fun x => axV x + axW x)
      (-(π / 3) * (axV t * (axE2 t + axV t + 2 * axW t)) +
        -(π / 3) * (axW t * (axE2 t - 2 * axV t - axW t))) t := hV.add hW
  have h := (hV.div hUd hU.ne').log hq.ne'
  have hev : axL =ᶠ[𝓝 t] fun x => Real.log (axV x / (axV x + axW x)) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact axL_eq_log hx
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  exact log_quotient_deriv _ _ _ hVp.ne' hU.ne'

/-- `θ₄ > 0` for nomes below `1/3`: `|θ₄(x) − 1| ≤ 2x/(1 − x)`. -/
theorem nomeTheta4_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1 / 3) : 0 < nomeTheta4 x := by
  have hρx : (1 : ℝ) * x < 1 := by linarith
  have h := Kron.series_tail_le sqE_strictMono (w := fun k => ((th4w k : ℚ) : ℝ)) (W := 2)
    (ρ := 1)
    (fun k => by
      have h : ((|th4w k| : ℚ) : ℝ) ≤ ((2 : ℚ) : ℝ) := Rat.cast_le.mpr (abs_th4w k)
      rw [Rat.cast_abs] at h
      simpa using h)
    le_rfl hx0 hρx 1 0
  have e1 : (2 : ℝ) * 1 ^ 0 * x ^ sqE 0 / (1 - 1 * x) = 2 * x / (1 - x) := by
    norm_num [sqE]
  have e2 : ((1 : ℝ) + ∑' k, ((th4w k : ℚ) : ℝ) * x ^ sqE k) -
      (1 + ∑ k ∈ Finset.range 0, ((th4w k : ℚ) : ℝ) * x ^ sqE k) = nomeTheta4 x - 1 := by
    rw [nomeTheta4_eq_series, Finset.sum_range_zero]
    push_cast
    ring
  rw [e1, e2] at h
  have h1 : 2 * x / (1 - x) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h2 := (abs_le.mp h).1
  linarith

end E8Leech
