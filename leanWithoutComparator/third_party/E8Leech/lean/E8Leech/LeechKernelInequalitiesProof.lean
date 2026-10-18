import E8Leech.KronLU
import E8Leech.KronLW
import E8Leech.KronLB
import E8Leech.LeechKernelReduction

/-!
# The kernel inequalities of CKMRV (6.4) in dimension 24

The truncated inequality (6.4)(2), `𝒦̂⁽²⁴⁾(iq, it) ≥ e^{2πt}(a₁(q) t + a₀(q))` for `t ≥ 1`, off the
singular points `t = q`, `t = q⁻¹`, is assembled from four kernel-checked pieces:

* `q, t ≥ 1` outside the box `q, t ≤ 107/100`: `leechHatTrunc_ge_one` (third-order jets of the
  numerator of `KronLeechH2`, vertex-check cover);
* `q ≤ 1 ≤ t` outside the box `1/q, t ≤ 59/50`: `leechHatTrunc_le_one` (the numerator of
  `KronLeechH2K` at the inverted first variable, with the explicit diagonal term);
* inside the two boxes the subtracted term is not positive, because `a₁ ≥ 0` and
  `a₀ + (107/100) a₁ < 0`, respectively `a₀ + (118/100) a₁ < 0` (`leechAxisCusp_box_neg`,
  `leechAxisCusp_box_neg_inv`), and the inequality follows from the positivity (6.4)(1) of the
  kernel (`leechHatTrunc_of_nonpos`).

With (6.4)(1), (3a), (3b) (`LeechKernelReduction`) this proves all four inequalities.

* `leechHatTrunc`: the truncated inequality (6.4)(2) for all `q > 0`, `t ≥ 1`.
* `leechKernelInequalities`: the structure `LeechKernelInequalities` is inhabited.
-/

noncomputable section

namespace E8Leech

open scoped Real

/-- **The truncated inequality (6.4)(2) for the Leech kernel**: for every `q > 0` and `t ≥ 1` off
the singular points, the kernel is at least the growing part of its cusp profile. -/
theorem leechHatTrunc {q t : ℝ} (hq : 0 < q) (ht : 1 ≤ t) (h1 : t ≠ q) (h2 : t ≠ q⁻¹) :
    ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t) ≤
      (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hJ := kleinModularJ_imagPt_ne hq ht0 h1 h2
  rcases lt_or_ge q 1 with hq1 | hq1
  · -- `q < 1`
    by_cases hbox : q⁻¹ ≤ 59 / 50 ∧ t ≤ 59 / 50
    · refine leechHatTrunc_of_nonpos hq ht0 h1 h2 ?_
      have hb := leechAxisCusp_box_neg_inv hq hq1.le (hbox.1.trans (by norm_num))
      have ha1 := leechAxisCusp_lead_nonneg hq hq1.ne
      nlinarith [mul_le_mul_of_nonneg_left hbox.2 ha1]
    · have hout : (59 / 50 : ℝ) < q⁻¹ ∨ (59 / 50 : ℝ) < t := by
        by_contra h
        rw [not_or, not_lt, not_lt] at h
        exact hbox h
      exact (mul_comm _ _).trans_le (leechHatTrunc_le_one hq hq1.le ht hout hJ).le
  · -- `q ≥ 1`
    by_cases hbox : q ≤ 107 / 100 ∧ t ≤ 107 / 100
    · refine leechHatTrunc_of_nonpos hq ht0 h1 h2 ?_
      have hb := leechAxisCusp_box_neg hq1 hbox.1
      have ha1 := (leechAxisCusp_lead_pos hq1).le
      nlinarith [mul_le_mul_of_nonneg_left hbox.2 ha1]
    · have hout : (107 / 100 : ℝ) < q ∨ (107 / 100 : ℝ) < t := by
        by_contra h
        rw [not_or, not_lt, not_lt] at h
        exact hbox h
      exact (mul_comm _ _).trans_le (leechHatTrunc_ge_one hq1 ht (Ne.symm h1) hout hJ).le

/-- **The kernel inequalities of CKMRV (6.4) in dimension 24.** -/
theorem leechKernelInequalities : LeechKernelInequalities :=
  leechKernelInequalities_of_hat_trunc fun _ _ hq _ ht h1 h2 _ => leechHatTrunc hq ht h1 h2

end E8Leech
