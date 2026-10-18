import E8Leech.LeechAxisRadialProfile

/-!
# The sign of the Leech profile `F̃(iq, ·)` from the kernel inequalities

`LeechKernelInequalities` collects the four inequalities of CKMRV (6.4) for `d = 24`, with the
truncation point `p = 1` (CKMRV use `p = 1.01`; numerically `−a₀/a₁ ≥ 1.064`, so `p = 1` is
admissible). With `a₁ t e^{2πt} + a₀ e^{2πt}` the growing part of the cusp profile of
`𝒦̂(iq, i·)`:

1. `𝒦̂(iq, it) ≥ 0` (off the singular points `t = q`, `t = q⁻¹`);
2. `𝒦̂(iq, it) ≥ e^{2πt}(a₁ t + a₀)` for `t ≥ 1` (off the removable points);
3. `a₀ + a₁ ≤ 0` and `a₁ ≥ 0`.

They are hypotheses here: none of them is proved in this file. From them, the profile
`P̂_q(b) = F̃(iq, √(b/π))` is real and nonnegative for every `b > 0`
(`leechHatProfile_re_nonneg`): for `b > 2π` by the Laplace representation, for `b ≤ 2π` by the
truncated form. By `leechAxisRadialProfile_one_eq` the profile of `𝒦(iy, ·)` is then nonpositive
(`leechProfile_re_nonpos`), which is the minorant inequality of Lemma 6.2 at all radii.
-/

noncomputable section

namespace E8Leech

open Complex MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real

/-- **The kernel inequalities of CKMRV (6.4) in dimension 24**, with truncation point `1`.

The two inequalities for the kernel are asked off the singular points `t = q`, `t = q⁻¹` only:
there `j(iq) = j(it)`, the kernel has a division by zero, and its Lean value (unlike in dimension
8, where it is `0`) is the regular part of the plus kernel, of which nothing is known. The
singular points are a null set of every integral in which the inequalities are used. -/
structure LeechKernelInequalities : Prop where
  hat_nonneg : ∀ q t : ℝ, 0 < q → 0 < t → t ≠ q → t ≠ q⁻¹ →
    0 ≤ (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re
  hat_trunc : ∀ q t : ℝ, 0 < q → q ≠ 1 → 1 ≤ t → t ≠ q → t ≠ q⁻¹ →
    ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t) ≤
      (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re
  cusp_sum_nonpos : ∀ q : ℝ, 0 < q → q ≠ 1 →
    (leechAxisCusp (-1) q 1).re + (leechAxisCusp (-1) q 0).re ≤ 0
  cusp_lead_nonneg : ∀ q : ℝ, 0 < q → q ≠ 1 → 0 ≤ (leechAxisCusp (-1) q 0).re

/-- An integral of a function with real values is the integral of its real part. -/
theorem setIntegral_eq_ofReal_of_im_eq_zero {f : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (h : ∀ t ∈ S, (f t).im = 0) : ∫ t in S, f t = ((∫ t in S, (f t).re : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact setIntegral_congr_fun hS fun t ht => Complex.ext (by simp) (by simp [h t ht])

theorem im_neg_one : ((-1 : ℂ)).im = 0 := by simp

/-! ## Realness -/

/-- The cusp profile with real coefficients is real. -/
theorem leechAxisProfile_im {s : ℂ} (hs : s.im = 0) {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    (leechAxisProfile s β t).im = 0 := by
  have h0 := leechAxisCusp_im hs hβ 0
  have h1 := leechAxisCusp_im hs hβ 1
  have h2 := leechAxisCusp_im hs hβ 2
  have h3 := leechAxisCusp_im hs hβ 3
  simp only [leechAxisProfile, cuspProfile, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, h0, h1, h2, h3]
  ring

/-- **The profile of `(K₊ + s K₋)/2 (iβ, ·)` is real for real `s`.** -/
theorem leechAxisRadialProfile_im {s : ℂ} (hs : s.im = 0) {β : ℝ} (hβ : 0 < β) (b : ℝ) :
    (leechAxisRadialProfile s β b).im = 0 := by
  have h0 := leechAxisCusp_im hs hβ 0
  have h1 := leechAxisCusp_im hs hβ 1
  have h2 := leechAxisCusp_im hs hβ 2
  have h3 := leechAxisCusp_im hs hβ 3
  have hint : (∫ t in Ioi 0, (leechAxisKernel s β t - leechAxisProfile s β t) *
      (Real.exp (-b * t) : ℂ)).im = 0 := by
    rw [setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioi fun t ht => by
      rw [Complex.im_mul_ofReal, Complex.sub_im, leechAxisKernel_im hs hβ ht,
        leechAxisProfile_im hs hβ, sub_zero, zero_mul]]
    exact Complex.ofReal_im _
  simp only [leechAxisRadialProfile, radialProfile, cuspProfileSinc, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hint, h0, h1, h2, h3]
  ring

/-! ## The sign of `F̃` -/

/-- **`F̃(iq, ·) ≥ 0` at every radius**, from the kernel inequalities. -/
theorem leechHatProfile_re_nonneg (H : LeechKernelInequalities) {q : ℝ} (hq : 0 < q)
    (hq1 : q ≠ 1) {b : ℝ} (hb : 0 < b) : 0 ≤ (leechAxisRadialProfile (-1) q b).re := by
  have hπ := Real.pi_pos
  have hKim : ∀ t : ℝ, 0 < t → (leechAxisKernel (-1) q t).im = 0 := fun t ht =>
    leechAxisKernel_im im_neg_one hq ht
  have hKre : ∀ t : ℝ, 0 < t → t ≠ q → t ≠ q⁻¹ → 0 ≤ (leechAxisKernel (-1) q t).re :=
    fun t ht h1 h2 => by
      rw [leechAxisKernel_neg_one]
      exact H.hat_nonneg q t hq ht h1 h2
  -- the singular points are a null set
  have hfin : volume ({q, q⁻¹} : Set ℝ) = 0 := (Set.toFinite {q, q⁻¹}).measure_zero _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({q, q⁻¹} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  rcases lt_or_ge (2 * π) b with hbig | hsmall
  · -- the Laplace representation
    rw [leechAxisRadialProfile_eq_laplace (-1) hq hq1 hbig,
      setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioi fun t ht => by
        rw [Complex.im_mul_ofReal, hKim t ht, zero_mul], ← Complex.ofReal_mul, Complex.ofReal_re]
    refine mul_nonneg (by positivity) (integral_nonneg_of_ae ?_)
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    simp only [Pi.zero_apply, Complex.re_mul_ofReal]
    exact mul_nonneg (hKre t ht0 ht.1 ht.2) (Real.exp_pos _).le
  · -- the truncated form with `p = 1`
    have hA := leechAxisCusp_im im_neg_one hq 0
    have hB := leechAxisCusp_im im_neg_one hq 1
    have h1 := H.cusp_sum_nonpos q hq hq1
    have h2 := H.cusp_lead_nonneg q hq hq1
    have htr := H.hat_trunc q
    rw [leechAxisRadialProfile_truncated (-1) hq hq1 hb zero_le_one]
    generalize leechAxisCusp (-1) q 0 = A at *
    generalize leechAxisCusp (-1) q 1 = B at *
    have hz : ∀ t : ℝ, 0 < t → (leechAxisKernel (-1) q t -
        (A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ))).im = 0 := by
      intro t ht
      rw [← Complex.ofReal_mul, Complex.sub_im, Complex.add_im, Complex.im_mul_ofReal,
        Complex.im_mul_ofReal, hKim t ht, hA, hB]
      ring
    have hzre : ∀ t : ℝ, 0 < t → (leechAxisKernel (-1) q t -
        (A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ))).re =
        (leechAxisKernel (-1) q t).re - (A.re * t + B.re) * Real.exp (2 * π * t) := by
      intro t ht
      rw [← Complex.ofReal_mul, Complex.sub_re, Complex.add_re, Complex.re_mul_ofReal,
        Complex.re_mul_ofReal]
      ring
    rw [setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioc fun t ht => by
        rw [Complex.im_mul_ofReal, hKim t ht.1, zero_mul],
      setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioi fun t ht => by
        rw [Complex.im_mul_ofReal, hz t (lt_trans zero_lt_one ht), zero_mul]]
    have hsum : 0 ≤ (∫ t in Ioc (0 : ℝ) 1, (leechAxisKernel (-1) q t).re * Real.exp (-b * t)) +
        ∫ t in Ioi (1 : ℝ), (leechAxisKernel (-1) q t -
          (A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ))).re *
            Real.exp (-b * t) := by
      refine add_nonneg (integral_nonneg_of_ae ?_) (integral_nonneg_of_ae ?_)
      · filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht ht01
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
        exact mul_nonneg (hKre t ht01.1 ht.1 ht.2) (Real.exp_pos _).le
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht ht1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht1
      show 0 ≤ (leechAxisKernel (-1) q t -
        (A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ))).re *
          Real.exp (-b * t)
      rw [hzre t ht0]
      refine mul_nonneg ?_ (Real.exp_pos _).le
      have h := htr t hq hq1 (le_of_lt ht1) ht.1 ht.2
      rw [leechAxisKernel_neg_one]
      linarith
    have hexp : 0 ≤ A.re + (B.re + 1 * A.re) * (b - 2 * π) := by
      have h3 : 0 ≤ (B.re + 1 * A.re) * (b - 2 * π) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      linarith
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.re_mul_ofReal, Complex.ofReal_re]
    exact add_nonneg (mul_nonneg (by positivity) hsum)
      (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hexp)

/-- **`e^{−α|x|²} − f(x) ≥ 0` at every radius**: the profile of `𝒦(iy, ·)` is nonpositive. -/
theorem leechProfile_re_nonpos (H : LeechKernelInequalities) {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    {b : ℝ} (hb : 0 < b) : (leechAxisRadialProfile 1 y b).re ≤ 0 := by
  have hy' : 0 < y⁻¹ := inv_pos.mpr hy
  have hy1' : y⁻¹ ≠ 1 := fun h => hy1 (inv_eq_one.mp h)
  have h := leechHatProfile_re_nonneg H hy' hy1' hb
  rw [leechAxisRadialProfile_one_eq hy hy1,
    show -((y : ℂ) ^ 12)⁻¹ = ((-(y ^ 12)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  have hpos : 0 < (y ^ 12)⁻¹ := by positivity
  nlinarith

end E8Leech
