import E8Leech.KronLH
import E8Leech.LeechCuspLead
import E8Leech.LeechHatProfileSign

/-!
# The Leech kernel inequalities reduced to the truncated inequality (6.4)(2)

Three of the four inequalities of `LeechKernelInequalities` are theorems:

* (1) `𝒦̂(iq, it) ≥ 0` off the singular points (`ckmrvLeechHatKernel_nonneg`);
* (3a) `a₀ + a₁ ≤ 0` (`leechAxisCusp_sum_neg`);
* (3b) `a₁ ≥ 0` (`leechAxisCusp_lead_nonneg`).

The remaining one, (2) `𝒦̂(iq, it) ≥ e^{2πt}(a₁ t + a₀)` for `t ≥ 1`, is not proved here.

* `leechHatTrunc_of_nonpos`: (2) holds at every point where `a₁ t + a₀ ≤ 0`, by (1).
* `leechKernelInequalities_of_hat_trunc`: the four inequalities from (2) at the points with
  `a₁ t + a₀ > 0`.
-/

noncomputable section

namespace E8Leech

open scoped Real

/-- The truncated inequality (6.4)(2) at a point where the subtracted term is not positive. -/
theorem leechHatTrunc_of_nonpos {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (h1 : t ≠ q) (h2 : t ≠ q⁻¹)
    (hneg : (leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re ≤ 0) :
    ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t) ≤
      (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re :=
  (mul_nonpos_of_nonpos_of_nonneg hneg (Real.exp_pos _).le).trans
    (ckmrvLeechHatKernel_nonneg hq ht h1 h2)

/-- **The kernel inequalities of CKMRV (6.4) in dimension 24 from the truncated inequality (2)**
at the points where the subtracted term is positive. -/
theorem leechKernelInequalities_of_hat_trunc
    (h : ∀ q t : ℝ, 0 < q → q ≠ 1 → 1 ≤ t → t ≠ q → t ≠ q⁻¹ →
      0 < (leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re →
      ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t) ≤
        (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re) :
    LeechKernelInequalities where
  hat_nonneg := fun _ _ hq ht h1 h2 => ckmrvLeechHatKernel_nonneg hq ht h1 h2
  hat_trunc := fun q t hq hq1 ht h1 h2 => by
    rcases le_or_gt ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) 0 with hs | hs
    · exact leechHatTrunc_of_nonpos hq (lt_of_lt_of_le one_pos ht) h1 h2 hs
    · exact h q t hq hq1 ht h1 h2 hs
  cusp_sum_nonpos := fun _ hq _ => (leechAxisCusp_sum_neg hq).le
  cusp_lead_nonneg := fun _ hq hq1 => leechAxisCusp_lead_nonneg hq hq1

end E8Leech
