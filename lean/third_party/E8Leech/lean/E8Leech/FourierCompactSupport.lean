import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# A Schwartz function supported in a ball whose Fourier transform is supported in a ball is zero

If `h` vanishes outside a ball, its Fourier integral along a line `t ↦ t • e` extends to an entire
function of `t`. If the Fourier transform vanishes outside a ball too, this entire function has
the zeros `t > R/‖e‖` and is identically zero; hence `𝓕 h = 0` and `h = 0`.

* `fourierLine`: the Fourier integral along the complex line `w ↦ w • e`.
* `differentiable_fourierLine`: it is entire when `h` is integrable with support in a ball.
* `schwartz_eq_zero_of_compact_supports`: the statement.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Complex Filter Topology Set
open scoped FourierTransform RealInnerProductSpace Real SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier integral of `h` along the complex line `w ↦ w • e`. -/
def fourierLine (h : V → ℂ) (e : V) (w : ℂ) : ℂ :=
  ∫ v, cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)) * h v

/-- On the real line it is the Fourier transform at `t • e`. -/
theorem fourierLine_ofReal (h : V → ℂ) (e : V) (t : ℝ) : fourierLine h e t = 𝓕 h (t • e) := by
  rw [fourierLine, Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, inner_smul_right]
  congr 2
  push_cast
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_cexp_line_le {R : ℝ} {e v : V} (hv : ‖v‖ ≤ R) (w : ℂ) :
    ‖cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ))‖ ≤ Real.exp (2 * π * |w.im| * (R * ‖e‖)) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)).re = 2 * π * w.im * ⟪v, e⟫ := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hre]
  have h1 : |⟪v, e⟫| ≤ R * ‖e‖ :=
    (abs_real_inner_le_norm v e).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg e))
  have hπ := Real.pi_pos
  calc 2 * π * w.im * ⟪v, e⟫ ≤ |2 * π * w.im * ⟪v, e⟫| := le_abs_self _
    _ = 2 * π * |w.im| * |⟪v, e⟫| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hπ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * π * |w.im| * (R * ‖e‖) := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The Fourier integral along a line is entire** for an integrable function that vanishes
outside a ball. -/
theorem differentiable_fourierLine {h : V → ℂ} (hint : Integrable h) {R : ℝ}
    (hR : ∀ v, R < ‖v‖ → h v = 0) (e : V) : Differentiable ℂ (fourierLine h e) := by
  intro w₀
  have hπ := Real.pi_pos
  set M : ℝ := Real.exp (2 * π * (|w₀.im| + 1) * (|R| * ‖e‖)) with hM
  set F : ℂ → V → ℂ := fun w v => cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)) * h v with hF
  set F' : ℂ → V → ℂ := fun w v =>
    (-(2 * π * I) * ((⟪v, e⟫ : ℝ) : ℂ)) * cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)) * h v
    with hF'
  have hcont : ∀ w : ℂ, Continuous fun v : V => cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)) :=
    fun w => by fun_prop
  have hinner : Continuous fun v : V => ((⟪v, e⟫ : ℝ) : ℂ) := by fun_prop
  -- the size of the exponential on the support, for `w` near `w₀`
  have hsize : ∀ w ∈ Metric.ball w₀ 1, ∀ v : V,
      ‖cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)) * h v‖ ≤ M * ‖h v‖ := by
    intro w hw v
    by_cases hv : R < ‖v‖
    · rw [hR v hv]
      simp
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hvR : ‖v‖ ≤ |R| := (not_lt.mp hv).trans (le_abs_self R)
      refine (norm_cexp_line_le hvR w).trans (Real.exp_le_exp.mpr ?_)
      have him : |w.im| ≤ |w₀.im| + 1 := by
        have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
          rw [← Complex.sub_im]
          exact Complex.abs_im_le_norm _
        have h2 : ‖w - w₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
        have h3 := abs_sub_abs_le_abs_sub w.im w₀.im
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left him (by positivity))
        (by positivity)
  have hFmeas : ∀ w : ℂ, AEStronglyMeasurable (F w) volume := fun w =>
    (hcont w).aestronglyMeasurable.mul hint.aestronglyMeasurable
  have hFint : Integrable (F w₀) volume :=
    (hint.norm.const_mul M).mono' (hFmeas w₀)
      (Eventually.of_forall fun v => hsize w₀ (Metric.mem_ball_self one_pos) v)
  have hF'meas : AEStronglyMeasurable (F' w₀) volume :=
    ((continuous_const.mul hinner).mul (hcont w₀)).aestronglyMeasurable.mul
      hint.aestronglyMeasurable
  have hbound : ∀ᵐ v ∂(volume : Measure V), ∀ w ∈ Metric.ball w₀ 1,
      ‖F' w v‖ ≤ 2 * π * (|R| * ‖e‖) * M * ‖h v‖ := by
    refine Eventually.of_forall fun v w hw => ?_
    by_cases hv : R < ‖v‖
    · simp only [hF', hR v hv, mul_zero, norm_zero, le_refl]
    · have hvR : ‖v‖ ≤ |R| := (not_lt.mp hv).trans (le_abs_self R)
      have h1 : |⟪v, e⟫| ≤ |R| * ‖e‖ :=
        (abs_real_inner_le_norm v e).trans (mul_le_mul_of_nonneg_right hvR (norm_nonneg e))
      have h2 : ‖-(2 * π * I) * ((⟪v, e⟫ : ℝ) : ℂ)‖ ≤ 2 * π * (|R| * ‖e‖) := by
        have hc : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos hπ]
        rw [norm_mul, norm_neg, hc, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 := hsize w hw v
      calc ‖F' w v‖ = ‖-(2 * π * I) * ((⟪v, e⟫ : ℝ) : ℂ)‖ *
            ‖cexp (-(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ)) * h v‖ := by
            simp only [hF', norm_mul]
            ring
        _ ≤ 2 * π * (|R| * ‖e‖) * (M * ‖h v‖) :=
            mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
        _ = 2 * π * (|R| * ‖e‖) * M * ‖h v‖ := by ring
  have hdiff : ∀ᵐ v ∂(volume : Measure V), ∀ w ∈ Metric.ball w₀ 1,
      HasDerivAt (fun w => F w v) (F' w v) w := by
    refine Eventually.of_forall fun v w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -(2 * π * I) * w * ((⟪v, e⟫ : ℝ) : ℂ))
        (-(2 * π * I) * ((⟪v, e⟫ : ℝ) : ℂ)) w := by
      have := ((hasDerivAt_id w).const_mul (-(2 * π * I))).mul_const ((⟪v, e⟫ : ℝ) : ℂ)
      simpa using this
    have h2 := (h1.cexp).mul_const (h v)
    refine h2.congr_deriv ?_
    simp only [hF']
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall hFmeas) hFint hF'meas hbound (hint.norm.const_mul _) hdiff
  exact key.2.differentiableAt

/-- An entire function that vanishes on a real half line is zero. -/
theorem eq_zero_of_differentiable_of_real_ray {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a : ℝ}
    (h : ∀ t : ℝ, a < t → g t = 0) (w : ℂ) : g w = 0 := by
  have han : AnalyticOnNhd ℂ g univ := analyticOnNhd_univ_iff_differentiable.mpr hg
  set z₀ : ℂ := ((a + 1 : ℝ) : ℂ) with hz₀
  have hu : Tendsto (fun n : ℕ => ((a + 1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => a + 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (a + 1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    · rw [mem_compl_iff, mem_singleton_iff, hz₀, Complex.ofReal_inj]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 :=
    hu.frequently (Frequently.of_forall fun n => h _ (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith))
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ z₀)
    hfreq (mem_univ w)

/-- **A Schwartz function that vanishes outside a ball and whose Fourier transform vanishes
outside a ball is zero.** -/
theorem schwartz_eq_zero_of_compact_supports [Nontrivial V] (h : 𝓢(V, ℂ)) {R : ℝ}
    (h1 : ∀ v : V, R < ‖v‖ → h v = 0) (h2 : ∀ w : V, R < ‖w‖ → 𝓕 (⇑h) w = 0) : h = 0 := by
  have hline : ∀ e : V, e ≠ 0 → ∀ w : ℂ, fourierLine (⇑h) e w = 0 := by
    intro e he w
    have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
    refine eq_zero_of_differentiable_of_real_ray (differentiable_fourierLine h.integrable h1 e)
      (a := |R| / ‖e‖) (fun t ht => ?_) w
    rw [fourierLine_ofReal]
    refine h2 _ ?_
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    have := (div_lt_iff₀ hepos).mp ht
    exact lt_of_le_of_lt (le_abs_self R) this
  have hF : ∀ w : V, 𝓕 (⇑h) w = 0 := by
    intro w
    by_cases hw : w = 0
    · obtain ⟨e, he⟩ := exists_ne (0 : V)
      have := hline e he 0
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, fourierLine_ofReal, zero_smul] at this
      rw [hw]
      exact this
    · have := hline w hw 1
      rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, fourierLine_ofReal, one_smul] at this
      exact this
  have hzero : (𝓕 h : 𝓢(V, ℂ)) = 0 := by
    ext w
    rw [SchwartzMap.fourier_coe]
    exact hF w
  have hinv : 𝓕⁻ (𝓕 h : 𝓢(V, ℂ)) = h := FourierTransform.fourierInv_fourier_eq h
  rw [hzero] at hinv
  rw [← hinv]
  exact map_zero _

end E8Leech
