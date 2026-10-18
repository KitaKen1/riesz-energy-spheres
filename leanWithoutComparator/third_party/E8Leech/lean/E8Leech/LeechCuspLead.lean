import E8Leech.KronLeechAll
import E8Leech.LeechSchwartzProfile

/-!
# The leading cusp coefficient of the Leech kernel is nonnegative

The kernel inequality (6.4)(3b) of Cohn–Kumar–Miller–Radchenko–Viazovska in dimension 24 says that
the coefficient `a₁(q)` of `t e^{2πt}` in the cusp profile of `𝒦̂(iq, i·)` is nonnegative. It needs
no computation: the kernel is positive (`ckmrvLeechHatKernel_pos`) and differs from its profile
`e^{2πt}(a₁ t + a₀) + c₁ t + c₀` by a bounded function for large `t` (`exists_leechAxis`), while the
profile tends to `−∞` if `a₁ < 0`.

* `leechAxisCusp_lead_nonneg`: `0 ≤ Re a₁(q)` for `q > 0`, `q ≠ 1`; this is the field
  `cusp_lead_nonneg` of `LeechKernelInequalities`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Asymptotics Topology
open scoped Real

/-- **(6.4)(3b) for the Leech lattice.** The leading cusp coefficient of `𝒦̂⁽²⁴⁾(iq, i·)` is
nonnegative. -/
theorem leechAxisCusp_lead_nonneg {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) :
    0 ≤ (leechAxisCusp (-1) q 0).re := by
  obtain ⟨g, -, hgK, -, -, -, hsub⟩ := exists_leechAxis (-1) hq hq1
  obtain ⟨C, hC, hbound⟩ := hsub.exists_pos
  by_contra hneg
  rw [not_le] at hneg
  have hπ := Real.pi_gt_three
  set a := (leechAxisCusp (-1) q 0).re with ha
  set b := (leechAxisCusp (-1) q 1).re with hb
  set c := (leechAxisCusp (-1) q 2).re with hc
  set d := (leechAxisCusp (-1) q 3).re with hd
  have ha' : 0 < -a := by linarith
  -- a large `t` at which the bound of the difference holds
  obtain ⟨t, hbt, hT⟩ := (hbound.bound.and (eventually_ge_atTop
    (max (max q q⁻¹ + 1) ((|b| + |c| + |d| + C + 1) / (-a))))).exists
  have ht1 : max q q⁻¹ + 1 ≤ t := le_trans (le_max_left _ _) hT
  have ht2 : (|b| + |c| + |d| + C + 1) / (-a) ≤ t := le_trans (le_max_right _ _) hT
  have hqt : q < t := by linarith [le_max_left q q⁻¹]
  have hqt' : q⁻¹ < t := by linarith [le_max_right q q⁻¹]
  have ht0 : 0 < t := lt_trans hq hqt
  have ht1' : 1 ≤ t := by linarith [lt_of_lt_of_le hq (le_max_left q q⁻¹)]
  -- the kernel is nonnegative at `t`
  have hg : 0 ≤ (g t).re := by
    rw [hgK t hqt.ne' hqt'.ne', leechAxisKernel_neg_one]
    exact ckmrvLeechHatKernel_nonneg hq ht0 hqt.ne' hqt'.ne'
  -- the difference with the profile is at most `C`
  have hexp : t * Real.exp ((-π + π / 4) * t) ≤ 1 := by
    have h1 := Real.add_one_le_exp ((π - π / 4) * t)
    have h2 : t ≤ Real.exp ((π - π / 4) * t) := by nlinarith
    have h3 : Real.exp ((-π + π / 4) * t) = (Real.exp ((π - π / 4) * t))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [h3, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2
  have hdiff : ‖g t - leechAxisProfile (-1) q t‖ ≤ C := by
    refine hbt.trans ?_
    rw [Real.norm_of_nonneg (mul_nonneg ht0.le (Real.exp_pos _).le)]
    calc C * (t * Real.exp ((-π + π / 4) * t)) ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hC.le
      _ = C := mul_one C
  have hPlow : -C ≤ (leechAxisProfile (-1) q t).re := by
    have h1 := (Complex.abs_re_le_norm (g t - leechAxisProfile (-1) q t)).trans hdiff
    rw [Complex.sub_re] at h1
    linarith [(abs_le.mp h1).2]
  -- but the profile is below `−C`
  have hre : (leechAxisProfile (-1) q t).re =
      Real.exp (2 * π * t) * (a * t + b) + c * t + d := by
    simp only [leechAxisProfile, cuspProfile]
    rw [← Complex.ofReal_mul, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.re_mul_ofReal]
    ring
  have hat : |b| + |c| + |d| + C + 1 ≤ -a * t := by
    rw [div_le_iff₀ ha'] at ht2
    linarith
  have hexp2 : t ≤ Real.exp (2 * π * t) := by
    have h1 := Real.add_one_le_exp (2 * π * t)
    nlinarith
  have hneg2 : a * t + b ≤ -(|c| + |d| + C + 1) := by linarith [le_abs_self b]
  have hpos2 : 0 ≤ -(a * t + b) := by linarith [abs_nonneg c, abs_nonneg d]
  have h1 : Real.exp (2 * π * t) * (a * t + b) ≤ t * (a * t + b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hexp2) hpos2]
  have h2 : t * (a * t + b) ≤ -t * (|c| + |d| + C + 1) := by nlinarith
  have h3 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0.le
  have h4 : d ≤ |d| * t := by nlinarith [le_abs_self d, abs_nonneg d]
  rw [hre] at hPlow
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr ht1')]

end E8Leech
