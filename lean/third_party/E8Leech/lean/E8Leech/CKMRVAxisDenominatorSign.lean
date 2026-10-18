import E8Leech.CKMRVLaplaceAxisClean
import E8Leech.CKMRVKernelExpr

/-!
# Exact denominator signs on both sides of the inverse curve

The known minimum j(i) = 1728 determines the orientation of the existing
Darboux argument. Inversion then determines the sign for every positive
pair away from u = t and ut = 1. Numerical boxes need only establish the
appropriate sign of the divided numerator.
-/

noncomputable section

namespace E8Leech

open Complex Set
open UpperHalfPlane hiding I
open scoped Real

/-- The minimum at height one rules out the decreasing Darboux branch. -/
theorem strictMonoOn_kleinImaginaryJ_re :
    StrictMonoOn (fun y => (kleinImaginaryJ y).re) (Ici (1 : ℝ)) := by
  have hpos : ∀ x ∈ Ioi (1 : ℝ), (0 : ℝ) < x := fun x hx => lt_trans one_pos hx
  have hd : ∀ x ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun y => (kleinImaginaryJ y).re)
      ((kleinModularJDerivative (imagPt x) * I).re) (Ioi 1) x := fun x hx =>
    (hasDerivAt_kleinImaginaryJ_re (hpos x hx)).hasDerivWithinAt
  have hcont : ContinuousOn (fun y => (kleinImaginaryJ y).re) (Ici 1) := fun x hx =>
    (hasDerivAt_kleinImaginaryJ_re (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Ici (1 : ℝ)), deriv (fun y => (kleinImaginaryJ y).re) x =
      (kleinModularJDerivative (imagPt x) * I).re := by
    intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivAt_kleinImaginaryJ_re (hpos x hx)).deriv
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioi 1) hd
      (fun x hx => kleinImaginaryJ_deriv_re_ne_zero hx) with h | h
  · have ha : StrictAntiOn (fun y => (kleinImaginaryJ y).re) (Ici (1 : ℝ)) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici 1) hcont
      intro x hx
      rw [hderiv x hx]
      rw [interior_Ici] at hx
      exact h x hx
    have bad := ha (show (1 : ℝ) ∈ Ici 1 by norm_num)
      (show (2 : ℝ) ∈ Ici 1 by norm_num) (by norm_num : (1 : ℝ) < 2)
    change (kleinImaginaryJ 2).re < (kleinImaginaryJ 1).re at bad
    rw [kleinImaginaryJ_at_one_eq_1728] at bad
    norm_num at bad
    have lower := kleinImaginaryJ_re_ge_1728 (by norm_num : (0 : ℝ) < 2)
    linarith
  · apply strictMonoOn_of_deriv_pos (convex_Ici 1) hcont
    intro x hx
    rw [hderiv x hx]
    rw [interior_Ici] at hx
    exact h x hx

theorem axDelta_pos {u : ℝ} (hu : 0 < u) : 0 < axDelta (axV u) (axW u) := by
  have h : 0 ≤ axDelta (axV u) (axW u) := by unfold axDelta; positivity
  exact lt_of_le_of_ne h (Ne.symm (axDelta_ne_zero hu))

theorem axNu_eq_delta_mul_kleinImaginaryJ_sub {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    axNu (axV u) (axW u) (axV t) (axW t) =
      axDelta (axV u) (axW u) * axDelta (axV t) (axW t) *
        ((kleinImaginaryJ u).re - (kleinImaginaryJ t).re) := by
  have hju := congrArg Complex.re (kleinModularJ_imagPt_eq_ax hu)
  have hjt := congrArg Complex.re (kleinModularJ_imagPt_eq_ax ht)
  simp only [Complex.ofReal_re] at hju hjt
  rw [kleinImaginaryJ_eq_imagPt, kleinImaginaryJ_eq_imagPt, hju, hjt]
  unfold axNu
  field_simp [axDelta_ne_zero hu, axDelta_ne_zero ht]

theorem kleinImaginaryJ_re_lt_of_lt_of_one_lt_mul {u t : ℝ} (hu : 0 < u) (_ht : 0 < t)
    (hut : u < t) (hprod : 1 < u * t) :
    (kleinImaginaryJ u).re < (kleinImaginaryJ t).re := by
  by_cases hu1 : 1 ≤ u
  · exact strictMonoOn_kleinImaginaryJ_re hu1 (hu1.trans hut.le) hut
  · have hule : u ≤ 1 := (lt_of_not_ge hu1).le
    have hi1 : 1 ≤ u⁻¹ := (one_le_inv₀ hu).mpr hule
    have hit : u⁻¹ < t := (inv_lt_iff_one_lt_mul₀' hu).mpr hprod
    have h := strictMonoOn_kleinImaginaryJ_re hi1 (hi1.trans hit.le) hit
    change (kleinImaginaryJ u⁻¹).re < (kleinImaginaryJ t).re at h
    rwa [kleinImaginaryJ_inv hu] at h

theorem kleinImaginaryJ_re_lt_of_lt_of_mul_lt_one {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hut : u < t) (hprod : u * t < 1) :
    (kleinImaginaryJ t).re < (kleinImaginaryJ u).re := by
  have hti : t⁻¹ < u⁻¹ := (inv_lt_inv₀ ht hu).mpr hut
  have hi : 1 < t⁻¹ * u⁻¹ := by
    have h := (one_lt_inv₀ (mul_pos hu ht)).mpr hprod
    simpa only [mul_inv_rev] using h
  have h := kleinImaginaryJ_re_lt_of_lt_of_one_lt_mul (inv_pos.mpr ht)
    (inv_pos.mpr hu) hti hi
  simpa only [kleinImaginaryJ_inv hu, kleinImaginaryJ_inv ht] using h

/-- The divided denominator is positive throughout the side ut > 1. -/
theorem ckmrvAxisDividedDenominator_pos {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hut : u ≠ t) (hprod : 1 < u * t) :
    0 < axNu (axV u) (axW u) (axV t) (axW t) /
      (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u)) := by
  rw [axNu_eq_delta_mul_kleinImaginaryJ_sub hu ht]
  have hD := mul_pos (axDelta_pos hu) (axDelta_pos ht)
  rcases lt_or_gt_of_ne hut with h | h
  · have hj := kleinImaginaryJ_re_lt_of_lt_of_one_lt_mul hu ht h hprod
    have he : Real.exp (-Real.pi * t) < Real.exp (-Real.pi * u) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hD (sub_neg.mpr hj)) (sub_neg.mpr he)
  · have hj := kleinImaginaryJ_re_lt_of_lt_of_one_lt_mul ht hu h (by nlinarith only [hprod])
    have he : Real.exp (-Real.pi * u) < Real.exp (-Real.pi * t) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    exact div_pos (mul_pos hD (sub_pos.mpr hj)) (sub_pos.mpr he)

/-- Below ut = 1 the same divided denominator is strictly negative. -/
theorem ckmrvAxisDividedDenominator_neg {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hut : u ≠ t) (hprod : u * t < 1) :
    axNu (axV u) (axW u) (axV t) (axW t) /
      (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u)) < 0 := by
  rw [axNu_eq_delta_mul_kleinImaginaryJ_sub hu ht]
  have hD := mul_pos (axDelta_pos hu) (axDelta_pos ht)
  rcases lt_or_gt_of_ne hut with h | h
  · have hj := kleinImaginaryJ_re_lt_of_lt_of_mul_lt_one hu ht h hprod
    have he : Real.exp (-Real.pi * t) < Real.exp (-Real.pi * u) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    exact div_neg_of_pos_of_neg (mul_pos hD (sub_pos.mpr hj)) (sub_neg.mpr he)
  · have hj := kleinImaginaryJ_re_lt_of_lt_of_mul_lt_one ht hu h (by nlinarith only [hprod])
    have he : Real.exp (-Real.pi * u) < Real.exp (-Real.pi * t) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hD (sub_neg.mpr hj)) (sub_pos.mpr he)

end E8Leech
