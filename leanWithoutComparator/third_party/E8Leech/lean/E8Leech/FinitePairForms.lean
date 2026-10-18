import E8Leech.LocalizedPairIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite-window real pair forms

Local finiteness makes each bounded-window restriction an atomic finite measure.
Thus arbitrary real kernels, without a measurability or boundedness hypothesis,
have a genuine samplewise double integral and finite pair sum. The previously
proved Jordan form agrees with both. Measurability and expectation integrability
are then inherited under the original energy hypotheses.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

theorem finite_window_points {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hb : Bornology.IsBounded W) : (c.support ∩ W).Finite := by
  exact (c.finite_on_compacts (closure W) hb.isCompact_closure).subset
    (fun _ hx => ⟨hx.1, subset_closure hx.2⟩)

/-- A samplewise finite set. No measurable enumeration is required. -/
def windowPointFinset {d : ℕ} (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (hb : Bornology.IsBounded W) : Finset (Ambient d) :=
  (finite_window_points c hb).toFinset

@[simp] theorem mem_windowPointFinset {d : ℕ} (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (hb : Bornology.IsBounded W) (x : Ambient d) :
    x ∈ windowPointFinset c W hb ↔ x ∈ c.support ∧ x ∈ W := by
  simp only [windowPointFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff]

theorem countingKernel_restrict_window {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hb : Bornology.IsBounded W) :
    (countingKernel d c).restrict W =
      Measure.count.restrict (windowPointFinset c W hb : Set (Ambient d)) := by
  change (Measure.count.restrict c.support).restrict W = _
  rw [Measure.restrict_restrict hW]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe, mem_windowPointFinset, and_comm]

theorem lintegral_countingKernel_indicator_eq_sum {d : ℕ}
    (c : Configuration (Ambient d)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hb : Bornology.IsBounded W) (f : Ambient d → ℝ≥0∞) :
    (∫⁻ x, W.indicator f x ∂countingKernel d c) = ∑ x ∈ windowPointFinset c W hb, f x := by
  rw [lintegral_indicator hW, countingKernel_restrict_window c hW hb]
  simpa only [Measure.count_singleton, mul_one] using
    (lintegral_finset (windowPointFinset c W hb) f (μ := Measure.count))

/-- Every function is integrable on a finite atomic counting restriction. -/
theorem integrable_count_restrict_finset {d : ℕ} (s : Finset (Ambient d))
    (f : Ambient d → ℝ) : Integrable f (Measure.count.restrict (s : Set (Ambient d))) := by
  have : IsFiniteMeasure (Measure.count.restrict (s : Set (Ambient d))) := by
    apply (isFiniteMeasure_iff _).mpr
    rw [Measure.restrict_apply_univ]
    exact (Measure.count_apply_lt_top.mpr s.finite_toSet)
  simpa only [IntegrableOn, Measure.restrict_restrict s.measurableSet, Set.inter_self] using
    (IntegrableOn.finset (μ := Measure.count.restrict (s : Set (Ambient d))) (s := s) (f := f))

theorem integrable_countingKernel_indicator {d : ℕ}
    (c : Configuration (Ambient d)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hb : Bornology.IsBounded W) (f : Ambient d → ℝ) :
    Integrable (W.indicator f) (countingKernel d c) := by
  rw [integrable_indicator_iff hW, IntegrableOn, countingKernel_restrict_window c hW hb]
  exact integrable_count_restrict_finset _ f

theorem integral_countingKernel_indicator_eq_sum {d : ℕ}
    (c : Configuration (Ambient d)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hb : Bornology.IsBounded W) (f : Ambient d → ℝ) :
    (∫ x, W.indicator f x ∂countingKernel d c) = ∑ x ∈ windowPointFinset c W hb, f x := by
  rw [integral_indicator hW, countingKernel_restrict_window c hW hb]
  have hf : IntegrableOn f (windowPointFinset c W hb : Set (Ambient d)) Measure.count :=
    integrable_count_restrict_finset _ f
  simpa only [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul] using
    (setIntegral_finset (windowPointFinset c W hb) hf)

theorem localizedPairIntegral_eq_sum {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    localizedPairIntegral V c W U =
      ∑ x ∈ windowPointFinset c W hbW, ∑ y ∈ windowPointFinset c U hbU, V x y := by
  change (∫⁻ x, W.indicator
    (fun x => ∫⁻ y, U.indicator (V x) y ∂countingKernel d c) x ∂countingKernel d c) = _
  rw [lintegral_countingKernel_indicator_eq_sum c hW hbW]
  apply Finset.sum_congr rfl
  intro x _
  exact lintegral_countingKernel_indicator_eq_sum c hU hbU (V x)

theorem signedLocalizedPairIntegral_eq_sum {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    signedLocalizedPairIntegral H c W U =
      ∑ x ∈ windowPointFinset c W hbW, ∑ y ∈ windowPointFinset c U hbU, H x y := by
  unfold signedLocalizedPairIntegral
  rw [localizedPairIntegral_eq_sum _ c hW hbW hU hbU,
    localizedPairIntegral_eq_sum _ c hW hbW hU hbU]
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)),
    ENNReal.toReal_sum (fun _ _ => ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))]
  simp only [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : 0 ≤ H x y
  · rw [ENNReal.toReal_ofReal h, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr h)]
    simp
  · have h' := (not_le.mp h).le
    rw [ENNReal.ofReal_eq_zero.mpr h', ENNReal.toReal_ofReal (neg_nonneg.mpr h')]
    simp

/-- The actual double Bochner integral; diagonal pairs are included. -/
def realLocalizedPairIntegral {d : ℕ} (H : Ambient d → Ambient d → ℝ)
    (c : Configuration (Ambient d)) (W U : Set (Ambient d)) : ℝ :=
  ∫ x, W.indicator (fun x => ∫ y, U.indicator (H x) y ∂countingKernel d c) x ∂countingKernel d c

theorem realLocalizedPairIntegral_eq_sum {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    realLocalizedPairIntegral H c W U =
      ∑ x ∈ windowPointFinset c W hbW, ∑ y ∈ windowPointFinset c U hbU, H x y := by
  unfold realLocalizedPairIntegral
  rw [integral_countingKernel_indicator_eq_sum c hW hbW]
  apply Finset.sum_congr rfl
  intro x _
  exact integral_countingKernel_indicator_eq_sum c hU hbU (H x)

theorem signedLocalizedPairIntegral_eq_real {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    signedLocalizedPairIntegral H c W U = realLocalizedPairIntegral H c W U := by
  rw [signedLocalizedPairIntegral_eq_sum H c hW hbW hU hbU,
    realLocalizedPairIntegral_eq_sum H c hW hbW hU hbU]

theorem measurable_realLocalizedPairIntegral {d : ℕ}
    {H : Ambient d → Ambient d → ℝ} (hH : Measurable (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    Measurable (fun c => realLocalizedPairIntegral H c W U) := by
  have he : (fun c => realLocalizedPairIntegral H c W U) =
      (fun c => signedLocalizedPairIntegral H c W U) := by
    funext c
    exact (signedLocalizedPairIntegral_eq_real H c hW hbW hU hbU).symm
  rw [he]
  exact measurable_signedLocalizedPairIntegral hH hW hU

theorem integrable_realLocalizedPairIntegral_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (H : Ambient d → Ambient d → ℝ)
    (hH : Measurable (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (M : ℝ) (hbound : ∀ x ∈ W, ∀ y ∈ U, |H x y| ≤ M) :
    Integrable (fun c => realLocalizedPairIntegral H c W U) μ := by
  have he : (fun c => realLocalizedPairIntegral H c W U) =
      (fun c => signedLocalizedPairIntegral H c W U) := by
    funext c
    exact (signedLocalizedPairIntegral_eq_real H c hW hbW hU hbU).symm
  rw [he]
  exact integrable_signedLocalizedPairIntegral_of_riesz hs μ hμ ρ hρ hρtop henergy
    H hH hW hbW hU hbU M hbound

/-- Real-valued kernels always give finite samplewise Jordan parts on bounded
windows. An expectation bound still requires the original moment control. -/
theorem localizedPairIntegral_ofReal_ne_top {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U ≠ ∞ := by
  rw [localizedPairIntegral_eq_sum _ c hW hbW hU hbU]
  exact ENNReal.sum_ne_top.mpr fun _ _ =>
    ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top

theorem count_eq_windowPointFinset_card {d : ℕ} (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (hb : Bornology.IsBounded W) :
    c.count W = (windowPointFinset c W hb).card := by
  exact Measure.count_apply_finite (c.support ∩ W) (finite_window_points c hb)

theorem realLocalizedPairIntegral_add {d : ℕ}
    (H G : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    realLocalizedPairIntegral (fun x y => H x y + G x y) c W U =
      realLocalizedPairIntegral H c W U + realLocalizedPairIntegral G c W U := by
  simp only [realLocalizedPairIntegral_eq_sum _ c hW hbW hU hbU,
    Finset.sum_add_distrib]

theorem realLocalizedPairIntegral_mul {d : ℕ}
    (a : ℝ) (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    realLocalizedPairIntegral (fun x y => a * H x y) c W U =
      a * realLocalizedPairIntegral H c W U := by
  simp only [realLocalizedPairIntegral_eq_sum _ c hW hbW hU hbU, Finset.mul_sum]

theorem realLocalizedPairIntegral_flip {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    realLocalizedPairIntegral (fun x y => H y x) c W U = realLocalizedPairIntegral H c U W := by
  rw [realLocalizedPairIntegral_eq_sum _ c hW hbW hU hbU,
    realLocalizedPairIntegral_eq_sum _ c hU hbU hW hbW]
  exact Finset.sum_comm

theorem realLocalizedPairIntegral_nonneg {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (hH : ∀ x ∈ W, ∀ y ∈ U, 0 ≤ H x y) :
    0 ≤ realLocalizedPairIntegral H c W U := by
  rw [realLocalizedPairIntegral_eq_sum _ c hW hbW hU hbU]
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro y hy
  exact hH x ((mem_windowPointFinset c W hbW x).mp hx).2
    y ((mem_windowPointFinset c U hbU y).mp hy).2

theorem realLocalizedPairIntegral_diagonal {d : ℕ}
    (h : Ambient d → ℝ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realLocalizedPairIntegral (fun x y => if y = x then h x else 0) c W W =
      ∑ x ∈ windowPointFinset c W hbW, h x := by
  rw [realLocalizedPairIntegral_eq_sum _ c hW hbW hW hbW]
  apply Finset.sum_congr rfl
  intro x hx
  simp [hx]

theorem realLocalizedPairIntegral_const_diagonal {d : ℕ}
    (a : ℝ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realLocalizedPairIntegral (fun x y => if y = x then a else 0) c W W =
      a * (c.count W).toReal := by
  rw [realLocalizedPairIntegral_diagonal _ c hW hbW, count_eq_windowPointFinset_card c W hbW]
  simp [nsmul_eq_mul, mul_comm]

/-- Exact diagonal removal before the energy LP step. -/
theorem realLocalizedPairIntegral_split_diagonal {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realLocalizedPairIntegral H c W W =
      realLocalizedPairIntegral (fun x y => if y = x then 0 else H x y) c W W +
        ∑ x ∈ windowPointFinset c W hbW, H x x := by
  have he : H = fun x y => (if y = x then 0 else H x y) +
      (if y = x then H x x else 0) := by
    funext x y
    by_cases hy : y = x <;> simp [hy]
  calc
    _ = realLocalizedPairIntegral (fun x y => (if y = x then 0 else H x y) +
        (if y = x then H x x else 0)) c W W := congrArg (fun F => realLocalizedPairIntegral F c W W) he
    _ = _ := by rw [realLocalizedPairIntegral_add _ _ c hW hbW hW hbW,
      realLocalizedPairIntegral_diagonal _ c hW hbW]

theorem measurable_finitePairSum {d : ℕ}
    {H : Ambient d → Ambient d → ℝ} (hH : Measurable (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    Measurable (fun c : Configuration (Ambient d) =>
      ∑ x ∈ windowPointFinset c W hbW, ∑ y ∈ windowPointFinset c U hbU, H x y) := by
  have he : (fun c : Configuration (Ambient d) =>
      ∑ x ∈ windowPointFinset c W hbW, ∑ y ∈ windowPointFinset c U hbU, H x y) =
      (fun c => realLocalizedPairIntegral H c W U) := by
    funext c
    exact (realLocalizedPairIntegral_eq_sum H c hW hbW hU hbU).symm
  rw [he]
  exact measurable_realLocalizedPairIntegral hH hW hbW hU hbU

theorem realLocalizedPairIntegral_difference_split {d : ℕ}
    (h : Ambient d → ℝ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realLocalizedPairIntegral (fun x y => h (x - y)) c W W =
      realLocalizedPairIntegral (fun x y => if y = x then 0 else h (x - y)) c W W +
        h 0 * (c.count W).toReal := by
  rw [realLocalizedPairIntegral_split_diagonal _ c hW hbW,
    count_eq_windowPointFinset_card c W hbW]
  simp [nsmul_eq_mul, mul_comm]

theorem integrable_realLocalizedPairIntegral_unit_diagonal {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (a : ℝ) :
    Integrable (fun c => realLocalizedPairIntegral (fun x y => if y = x then a else 0)
      c (unitWindow d) (unitWindow d)) μ := by
  have he : (fun c => realLocalizedPairIntegral (fun x y => if y = x then a else 0)
      c (unitWindow d) (unitWindow d)) = (fun c => a * (c.count (unitWindow d)).toReal) := by
    funext c
    exact realLocalizedPairIntegral_const_diagonal a c (measurable_unitWindow d) (isBounded_unitWindow d)
  rw [he]
  apply Integrable.const_mul
  apply integrable_toReal_of_lintegral_ne_top
    (Configuration.measurable_count (measurable_unitWindow d)).aemeasurable
  rwa [expected_count_unitWindow μ ρ hρ]

/-- The finite diagonal expectation of a translation-invariant auxiliary kernel is
its value at zero times intensity, here at the normalized unit window. -/
theorem integral_realLocalizedPairIntegral_unit_diagonal {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (a : ℝ) :
    (∫ c, realLocalizedPairIntegral (fun x y => if y = x then a else 0)
      c (unitWindow d) (unitWindow d) ∂μ) = a * ρ.toReal := by
  have he : (fun c => realLocalizedPairIntegral (fun x y => if y = x then a else 0)
      c (unitWindow d) (unitWindow d)) = (fun c => a * (c.count (unitWindow d)).toReal) := by
    funext c
    exact realLocalizedPairIntegral_const_diagonal a c (measurable_unitWindow d) (isBounded_unitWindow d)
  rw [he, integral_const_mul]
  have hc : Integrable (fun c : Configuration (Ambient d) => (c.count (unitWindow d)).toReal) μ := by
    apply integrable_toReal_of_lintegral_ne_top
      (Configuration.measurable_count (measurable_unitWindow d)).aemeasurable
    rwa [expected_count_unitWindow μ ρ hρ]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    hc.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_toReal (count_ne_top_of_bounded _ (isBounded_unitWindow d))]
  rw [expected_count_unitWindow μ ρ hρ]

theorem realLocalizedPairIntegral_abs_eq {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    realLocalizedPairIntegral (fun x y => |H x y|) c W U =
      (localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U).toReal := by
  rw [realLocalizedPairIntegral_eq_sum _ c hW hbW hU hbU,
    localizedPairIntegral_eq_sum _ c hW hbW hU hbU]
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))]
  simp only [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (abs_nonneg _)]

theorem abs_realLocalizedPairIntegral_le {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    |realLocalizedPairIntegral H c W U| ≤
      realLocalizedPairIntegral (fun x y => |H x y|) c W U := by
  rw [← signedLocalizedPairIntegral_eq_real H c hW hbW hU hbU,
    realLocalizedPairIntegral_abs_eq H c hW hbW hU hbU]
  exact abs_signedLocalizedPairIntegral_le H c
    (localizedPairIntegral_ofReal_ne_top (fun x y => |H x y|) c hW hbW hU hbU)

/-- Compact closures provide a law-independent local bound automatically.
This does not assert a summable all-space tail. -/
theorem exists_local_pair_bound_of_continuous {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Continuous (Function.uncurry H))
    {W U : Set (Ambient d)} (hbW : Bornology.IsBounded W) (hbU : Bornology.IsBounded U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ W, ∀ y ∈ U, |H x y| ≤ M := by
  have hK : IsCompact (closure W ×ˢ closure U) := hbW.isCompact_closure.prod hbU.isCompact_closure
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hb := hM (x, y) ⟨subset_closure hx, subset_closure hy⟩
  have hb' : |H x y| ≤ M := by
    simpa only [Function.uncurry, Real.norm_eq_abs] using hb
  exact hb'.trans (le_max_left M 0)

/-- Every continuous auxiliary kernel has an integrable local quadratic form
under the original finite-intensity / finite-Riesz-energy hypotheses. -/
theorem integrable_realLocalizedPairIntegral_of_continuous {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (H : Ambient d → Ambient d → ℝ)
    (hH : Continuous (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    Integrable (fun c => realLocalizedPairIntegral H c W U) μ := by
  obtain ⟨M, _, hM⟩ := exists_local_pair_bound_of_continuous H hH hbW hbU
  exact integrable_realLocalizedPairIntegral_of_riesz hs μ hμ ρ hρ hρtop henergy
    H hH.measurable hW hbW hU hbU M hM

end E8Leech
