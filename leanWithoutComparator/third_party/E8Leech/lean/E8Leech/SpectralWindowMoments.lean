import E8Leech.WindowFirstMoments

/-!
# Spectral window sums: exact means and a lower bound for their squares

Intensity alone computes the mean character sum. Original finite Riesz energy
controls its second moment. Centering a complex random variable proves the
mean-square inequality directly, without a general Jensen or variance library.
No ergodicity, independence or extra process moment assumption is added.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory ComplexConjugate
open scoped ENNReal Classical

-- Keep character identities abstract during type comparison; do not expand
-- the Euclidean coordinate inner-product sum while matching measurability.
attribute [local irreducible] spectralPhase

@[irreducible] def spectralWindowSum {d : ℕ} (W : Set (Ambient d)) (hbW : Bornology.IsBounded W)
    (ξ : Ambient d) (c : Configuration (Ambient d)) : ℂ :=
  ∑ x ∈ windowPointFinset c W hbW, spectralPhase ξ x

theorem continuous_spectralPhase_joint {d : ℕ} :
    Continuous (Function.uncurry (@spectralPhase d)) := by
  unfold spectralPhase
  fun_prop

theorem spectralWindowSum_norm_le_count {d : ℕ} (W : Set (Ambient d))
    (hbW : Bornology.IsBounded W) (ξ : Ambient d) (c : Configuration (Ambient d)) :
    ‖spectralWindowSum W hbW ξ c‖ ≤ (c.count W).toReal := by
  unfold spectralWindowSum
  calc
    _ ≤ ∑ x ∈ windowPointFinset c W hbW, ‖spectralPhase ξ x‖ := norm_sum_le _ _
    _ = _ := by rw [count_eq_windowPointFinset_card c W hbW]; simp

theorem spectralWindowSum_normSq_le_count_sq {d : ℕ} (W : Set (Ambient d))
    (hbW : Bornology.IsBounded W) (ξ : Ambient d) (c : Configuration (Ambient d)) :
    Complex.normSq (spectralWindowSum W hbW ξ c) ≤ (c.count W).toReal ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (spectralWindowSum_norm_le_count W hbW ξ c) 2

theorem spectralWindowSum_re {d : ℕ} {W : Set (Ambient d)} (hW : MeasurableSet W)
    (hbW : Bornology.IsBounded W) (ξ : Ambient d) (c : Configuration (Ambient d)) :
    (spectralWindowSum W hbW ξ c).re = realWindowIntegral (fun x => (spectralPhase ξ x).re) c W := by
  rw [realWindowIntegral_eq_sum _ c hW hbW]
  unfold spectralWindowSum
  exact Complex.re_sum _ _

theorem spectralWindowSum_im {d : ℕ} {W : Set (Ambient d)} (hW : MeasurableSet W)
    (hbW : Bornology.IsBounded W) (ξ : Ambient d) (c : Configuration (Ambient d)) :
    (spectralWindowSum W hbW ξ c).im = realWindowIntegral (fun x => (spectralPhase ξ x).im) c W := by
  rw [realWindowIntegral_eq_sum _ c hW hbW]
  unfold spectralWindowSum
  exact Complex.im_sum _ _

theorem measurable_spectralWindowSum_joint {d : ℕ} {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Measurable (Function.uncurry (spectralWindowSum W hbW)) := by
  have hphase : Measurable (fun q : Ambient d × Ambient d => spectralPhase q.1 q.2) :=
    (continuous_spectralPhase_joint (d := d)).measurable
  have hproj : Measurable (fun p : (Ambient d × Configuration (Ambient d)) × Ambient d =>
      (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
  have hp : Measurable (fun p : (Ambient d × Configuration (Ambient d)) × Ambient d =>
      spectralPhase p.1.1 p.2) := hphase.comp hproj
  have hr := measurable_realWindowIntegral_param Prod.snd measurable_snd
    (fun p x => (spectralPhase p.1 x).re)
    (Complex.continuous_re.measurable.comp hp) hW hbW
  have hi := measurable_realWindowIntegral_param Prod.snd measurable_snd
    (fun p x => (spectralPhase p.1 x).im)
    (Complex.continuous_im.measurable.comp hp) hW hbW
  have he : Function.uncurry (spectralWindowSum W hbW) = (fun p =>
      (realWindowIntegral (fun x => (spectralPhase p.1 x).re) p.2 W : ℂ) +
      (realWindowIntegral (fun x => (spectralPhase p.1 x).im) p.2 W : ℂ) * Complex.I) := by
    funext p
    change spectralWindowSum W hbW p.1 p.2 = _
    rw [← spectralWindowSum_re hW hbW p.1 p.2, ← spectralWindowSum_im hW hbW p.1 p.2]
    exact (Complex.re_add_im _).symm
  rw [he]
  exact (Complex.continuous_ofReal.measurable.comp hr).add
    ((Complex.continuous_ofReal.measurable.comp hi).mul_const Complex.I)

theorem measurable_spectralWindowSum {d : ℕ} {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    Measurable (spectralWindowSum W hbW ξ) := by
  have hj : Measurable (fun p : Ambient d × Configuration (Ambient d) =>
      spectralWindowSum W hbW p.1 p.2) := measurable_spectralWindowSum_joint hW hbW
  have hi : Measurable (fun c : Configuration (Ambient d) => (ξ, c)) :=
    measurable_const.prodMk measurable_id
  exact hj.comp hi

theorem integrable_spectralPhase_window {d : ℕ} {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    Integrable (W.indicator (spectralPhase ξ)) volume := by
  rw [integrable_indicator_iff hW]
  apply Measure.integrableOn_of_bounded hbW.measure_lt_top.ne
    (continuous_spectralPhase_point ξ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (spectralPhase_norm ξ x).le

theorem integrable_spectralWindowSum_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (hρtop : ρ ≠ ∞) {W : Set (Ambient d)} (hW : MeasurableSet W)
    (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    Integrable (spectralWindowSum W hbW ξ) μ := by
  apply Integrable.re_im_iff.mp
  constructor
  · apply (integrable_realWindowIntegral_of_intensity μ ρ hρ hρtop
      (fun x => (spectralPhase ξ x).re)
      (Complex.continuous_re.comp (continuous_spectralPhase_point ξ)).measurable
      hW hbW 1 (fun x _ => (Complex.abs_re_le_norm _).trans_eq (spectralPhase_norm ξ x))).congr
    filter_upwards with c
    exact (spectralWindowSum_re hW hbW ξ c).symm
  · apply (integrable_realWindowIntegral_of_intensity μ ρ hρ hρtop
      (fun x => (spectralPhase ξ x).im)
      (Complex.continuous_im.comp (continuous_spectralPhase_point ξ)).measurable
      hW hbW 1 (fun x _ => (Complex.abs_im_le_norm _).trans_eq (spectralPhase_norm ξ x))).congr
    filter_upwards with c
    exact (spectralWindowSum_im hW hbW ξ c).symm

theorem integrable_spectralWindowSum_normSq_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    Integrable (fun c => Complex.normSq (spectralWindowSum W hbW ξ c)) μ := by
  have hc := integrable_square_of_memLp_two
    (memLp_bounded_window_count_two hs μ hμ ρ hρ hρtop henergy hW hbW)
  apply hc.mono' (Complex.continuous_normSq.measurable.comp
    (measurable_spectralWindowSum hW hbW ξ)).aestronglyMeasurable
  filter_upwards with c
  change ‖Complex.normSq (spectralWindowSum W hbW ξ c)‖ ≤ (c.count W).toReal ^ 2
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)] using
    spectralWindowSum_normSq_le_count_sq W hbW ξ c

theorem integral_spectralWindowSum_of_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (hρtop : ρ ≠ ∞) {W : Set (Ambient d)} (hW : MeasurableSet W)
    (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    (∫ c, spectralWindowSum W hbW ξ c ∂μ) =
      (ρ.toReal : ℂ) * ∫ x, W.indicator (spectralPhase ξ) x := by
  have hZ := integrable_spectralWindowSum_of_intensity μ ρ hρ hρtop hW hbW ξ
  have hP := integrable_spectralPhase_window hW hbW ξ
  have hZr : (∫ c, (spectralWindowSum W hbW ξ c).re ∂μ) =
      (∫ c, spectralWindowSum W hbW ξ c ∂μ).re := integral_re hZ
  have hZi : (∫ c, (spectralWindowSum W hbW ξ c).im ∂μ) =
      (∫ c, spectralWindowSum W hbW ξ c ∂μ).im := integral_im hZ
  have hPr : (∫ x, (W.indicator (spectralPhase ξ) x).re) =
      (∫ x, W.indicator (spectralPhase ξ) x).re := integral_re hP
  have hPi : (∫ x, (W.indicator (spectralPhase ξ) x).im) =
      (∫ x, W.indicator (spectralPhase ξ) x).im := integral_im hP
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hZr, ← hPr]
    simp_rw [spectralWindowSum_re hW hbW]
    rw [integral_realWindowIntegral_of_intensity μ ρ hρ hρtop (fun x => (spectralPhase ξ x).re)
      (Complex.continuous_re.comp (continuous_spectralPhase_point ξ)).measurable hW hbW 1
      (fun x _ => (Complex.abs_re_le_norm _).trans_eq (spectralPhase_norm ξ x))]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ W <;> simp [hx]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← hZi, ← hPi]
    simp_rw [spectralWindowSum_im hW hbW]
    rw [integral_realWindowIntegral_of_intensity μ ρ hρ hρtop (fun x => (spectralPhase ξ x).im)
      (Complex.continuous_im.comp (continuous_spectralPhase_point ξ)).measurable hW hbW 1
      (fun x _ => (Complex.abs_im_le_norm _).trans_eq (spectralPhase_norm ξ x))]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ W <;> simp [hx]

/-- Centering is a short proof of the complex square-mean inequality. -/
theorem complex_normSq_integral_le_integral_normSq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℂ) (hF : Integrable F μ)
    (hF2 : Integrable (fun a => Complex.normSq (F a)) μ) :
    Complex.normSq (∫ a, F a ∂μ) ≤ ∫ a, Complex.normSq (F a) ∂μ := by
  let m : ℂ := ∫ a, F a ∂μ
  have hconst : Integrable (fun _ : A => Complex.normSq m) μ := integrable_const _
  have hcross : Integrable (fun a => 2 * (F a * conj m).re) μ :=
    ((hF.mul_const (conj m)).re).const_mul 2
  have hsum : Integrable (fun a => Complex.normSq (F a) + Complex.normSq m) μ :=
    hF2.add hconst
  have hcrossre : (∫ a, (F a * conj m).re ∂μ) = (∫ a, F a * conj m ∂μ).re :=
    integral_re (hF.mul_const (conj m))
  have hn : (0 : ℝ) ≤ ∫ a, Complex.normSq (F a - m) ∂μ :=
    integral_nonneg (fun a => Complex.normSq_nonneg (F a - m))
  simp_rw [Complex.normSq_sub] at hn
  rw [integral_sub hsum hcross, integral_add hF2 hconst,
    integral_const, integral_const_mul, hcrossre,
    integral_mul_const] at hn
  change 0 ≤ (∫ a, Complex.normSq (F a) ∂μ) + μ.real univ * Complex.normSq m -
    2 * (m * conj m).re at hn
  rw [probReal_univ, one_mul, Complex.mul_conj, Complex.ofReal_re] at hn
  change Complex.normSq m ≤ _
  linarith

theorem spectralWindowSum_mean_square_lower {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    ρ.toReal ^ 2 * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ≤
      ∫ c, Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ := by
  have h := complex_normSq_integral_le_integral_normSq μ (spectralWindowSum W hbW ξ)
    (integrable_spectralWindowSum_of_intensity μ ρ hρ hρtop hW hbW ξ)
    (integrable_spectralWindowSum_normSq_of_riesz hs μ hμ ρ hρ hρtop henergy hW hbW ξ)
  rw [integral_spectralWindowSum_of_intensity μ ρ hρ hρtop hW hbW ξ,
    Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at h
  exact h

end E8Leech
