import E8Leech.SpectralPairForms

/-!
# Real finite-window first moments from intensity alone

The counting integral is identified with a finite sum samplewise. Measurability
comes from its two nonnegative Jordan parts, including additional parameters.
Finite intensity and a bounded kernel give integrability and the exact mean
formula. Neither stationarity nor a second-moment hypothesis is used here.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def realWindowIntegral {d : ℕ} (f : Ambient d → ℝ)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) : ℝ :=
  ∫ x, W.indicator f x ∂countingKernel d c

theorem realWindowIntegral_eq_sum {d : ℕ} (f : Ambient d → ℝ)
    (c : Configuration (Ambient d)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realWindowIntegral f c W = ∑ x ∈ windowPointFinset c W hbW, f x :=
  integral_countingKernel_indicator_eq_sum c hW hbW f

theorem realWindowIntegral_eq_Jordan {d : ℕ} (f : Ambient d → ℝ)
    (c : Configuration (Ambient d)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realWindowIntegral f c W =
      (∫⁻ x, W.indicator (fun x => ENNReal.ofReal (f x)) x ∂countingKernel d c).toReal -
      (∫⁻ x, W.indicator (fun x => ENNReal.ofReal (-f x)) x ∂countingKernel d c).toReal := by
  unfold realWindowIntegral
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (integrable_countingKernel_indicator c hW hbW f)]
  congr 2 <;> congr 1 <;> funext x <;> by_cases hx : x ∈ W <;> simp [hx]

theorem measurable_realWindowIntegral_param {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : A → Configuration (Ambient d)) (hc : Measurable c)
    (f : A → Ambient d → ℝ) (hf : Measurable (Function.uncurry f))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Measurable (fun a => realWindowIntegral (f a) (c a) W) := by
  have hp : Measurable (fun a => ∫⁻ x,
      W.indicator (fun x => ENNReal.ofReal (f a x)) x ∂countingKernel d (c a)) :=
    measurable_countingKernel_lintegral_param c hc
      (Measurable.ite (hW.preimage measurable_snd) hf.ennreal_ofReal measurable_const)
  have hn : Measurable (fun a => ∫⁻ x,
      W.indicator (fun x => ENNReal.ofReal (-f a x)) x ∂countingKernel d (c a)) :=
    measurable_countingKernel_lintegral_param c hc
      (Measurable.ite (hW.preimage measurable_snd) hf.neg.ennreal_ofReal measurable_const)
  have he : (fun a => realWindowIntegral (f a) (c a) W) =
      (fun a => (∫⁻ x, W.indicator (fun x => ENNReal.ofReal (f a x)) x
        ∂countingKernel d (c a)).toReal -
        (∫⁻ x, W.indicator (fun x => ENNReal.ofReal (-f a x)) x
        ∂countingKernel d (c a)).toReal) := by
    funext a
    exact realWindowIntegral_eq_Jordan _ _ hW hbW
  rw [he]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

theorem measurable_realWindowIntegral {d : ℕ} (f : Ambient d → ℝ) (hf : Measurable f)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Measurable (fun c => realWindowIntegral f c W) :=
  measurable_realWindowIntegral_param id measurable_id (fun _ => f)
    (hf.comp measurable_snd) hW hbW

theorem window_lintegral_le_const {d : ℕ} (ν : Measure (Ambient d))
    (V : Ambient d → ℝ≥0∞) {W : Set (Ambient d)} (hW : MeasurableSet W)
    (M : ℝ≥0∞) (hV : ∀ x ∈ W, V x ≤ M) :
    (∫⁻ x, W.indicator V x ∂ν) ≤ M * ν W := by
  calc
    _ ≤ ∫⁻ x, W.indicator (fun _ => M) x ∂ν := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ W
      · simpa only [indicator_of_mem hx] using hV x hx
      · simp [hx]
    _ = _ := lintegral_indicator_const hW M

theorem expected_window_lintegral_ne_top_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (V : Ambient d → ℝ≥0∞) (hV : Measurable V)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hbound : ∀ x ∈ W, V x ≤ M) :
    (∫⁻ c, ∫⁻ x, W.indicator V x ∂countingKernel d c ∂μ) ≠ ∞ := by
  rw [expected_counting_integral μ ρ hρ (hV.indicator hW)]
  apply ENNReal.mul_ne_top hρtop
  exact ne_of_lt ((window_lintegral_le_const volume V hW M hbound).trans_lt
    (ENNReal.mul_ne_top hM hbW.measure_lt_top.ne).lt_top)

theorem integrable_realWindowIntegral_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (f : Ambient d → ℝ) (hf : Measurable f)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (M : ℝ) (hbound : ∀ x ∈ W, |f x| ≤ M) :
    Integrable (fun c => realWindowIntegral f c W) μ := by
  have hp := expected_window_lintegral_ne_top_of_intensity μ ρ hρ hρtop
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal hW hbW (ENNReal.ofReal M)
    ENNReal.ofReal_ne_top (fun x hx => ENNReal.ofReal_le_ofReal
      ((le_abs_self (f x)).trans (hbound x hx)))
  have hn := expected_window_lintegral_ne_top_of_intensity μ ρ hρ hρtop
    (fun x => ENNReal.ofReal (-f x)) hf.neg.ennreal_ofReal hW hbW (ENNReal.ofReal M)
    ENNReal.ofReal_ne_top (fun x hx => ENNReal.ofReal_le_ofReal
      ((neg_le_abs (f x)).trans (hbound x hx)))
  have hpm : Measurable (fun c => ∫⁻ x,
      W.indicator (fun x => ENNReal.ofReal (f x)) x ∂countingKernel d c) :=
    measurable_countingKernel_lintegral ((hf.ennreal_ofReal.indicator hW).comp measurable_snd)
  have hnm : Measurable (fun c => ∫⁻ x,
      W.indicator (fun x => ENNReal.ofReal (-f x)) x ∂countingKernel d c) :=
    measurable_countingKernel_lintegral ((hf.neg.ennreal_ofReal.indicator hW).comp measurable_snd)
  apply ((integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hp).sub
    (integrable_toReal_of_lintegral_ne_top hnm.aemeasurable hn)).congr
  filter_upwards with c
  exact (realWindowIntegral_eq_Jordan f c hW hbW).symm

theorem integrable_real_window_indicator_of_bound {d : ℕ} (f : Ambient d → ℝ)
    (hf : Measurable f) {W : Set (Ambient d)} (hW : MeasurableSet W)
    (hbW : Bornology.IsBounded W) (M : ℝ) (hbound : ∀ x ∈ W, |f x| ≤ M) :
    Integrable (W.indicator f) volume := by
  rw [integrable_indicator_iff hW]
  apply Measure.integrableOn_of_bounded hbW.measure_lt_top.ne hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hW] with x hx
  simpa only [Real.norm_eq_abs] using hbound x hx

theorem integral_realWindowIntegral_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (f : Ambient d → ℝ) (hf : Measurable f)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (M : ℝ) (hbound : ∀ x ∈ W, |f x| ≤ M) :
    (∫ c, realWindowIntegral f c W ∂μ) = ρ.toReal * ∫ x, W.indicator f x := by
  have hp := expected_window_lintegral_ne_top_of_intensity μ ρ hρ hρtop
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal hW hbW (ENNReal.ofReal M)
    ENNReal.ofReal_ne_top (fun x hx => ENNReal.ofReal_le_ofReal
      ((le_abs_self (f x)).trans (hbound x hx)))
  have hn := expected_window_lintegral_ne_top_of_intensity μ ρ hρ hρtop
    (fun x => ENNReal.ofReal (-f x)) hf.neg.ennreal_ofReal hW hbW (ENNReal.ofReal M)
    ENNReal.ofReal_ne_top (fun x hx => ENNReal.ofReal_le_ofReal
      ((neg_le_abs (f x)).trans (hbound x hx)))
  have hpm : Measurable (fun c => ∫⁻ x,
      W.indicator (fun x => ENNReal.ofReal (f x)) x ∂countingKernel d c) :=
    measurable_countingKernel_lintegral ((hf.ennreal_ofReal.indicator hW).comp measurable_snd)
  have hnm : Measurable (fun c => ∫⁻ x,
      W.indicator (fun x => ENNReal.ofReal (-f x)) x ∂countingKernel d c) :=
    measurable_countingKernel_lintegral ((hf.neg.ennreal_ofReal.indicator hW).comp measurable_snd)
  have he : (fun c => realWindowIntegral f c W) = (fun c =>
      (∫⁻ x, W.indicator (fun x => ENNReal.ofReal (f x)) x ∂countingKernel d c).toReal -
      (∫⁻ x, W.indicator (fun x => ENNReal.ofReal (-f x)) x ∂countingKernel d c).toReal) := by
    funext c
    exact realWindowIntegral_eq_Jordan f c hW hbW
  rw [he, integral_sub (integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hp)
    (integrable_toReal_of_lintegral_ne_top hnm.aemeasurable hn),
    integral_toReal hpm.aemeasurable (ae_lt_top hpm hp),
    integral_toReal hnm.aemeasurable (ae_lt_top hnm hn),
    expected_counting_integral μ ρ hρ (hf.ennreal_ofReal.indicator hW),
    expected_counting_integral μ ρ hρ
      (f := W.indicator (fun x => ENNReal.ofReal (-f x)))
      (hf.neg.ennreal_ofReal.indicator hW),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub]
  congr 1
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (integrable_real_window_indicator_of_bound f hf hW hbW M hbound)]
  congr 2 <;> congr 1 <;> funext x <;> by_cases hx : x ∈ W <;> simp [hx]

end E8Leech
