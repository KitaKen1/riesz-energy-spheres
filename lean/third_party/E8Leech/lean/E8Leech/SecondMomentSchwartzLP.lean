import E8Leech.PositiveMixtureMoments
import E8Leech.SchwartzPotentialGap

/-!
# Stationary Schwartz LP from a local second moment

The signed Fourier proof uses the unit-window second moment, not the singular
Riesz potential itself. Isolating this prerequisite permits laws having finite
positive Gaussian mixture energy. The moment is derived in the mixture adapter;
it is not an additional hypothesis of that adapter.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter
open scoped ENNReal Classical Topology SchwartzMap FourierTransform RealInnerProductSpace

theorem expected_translated_unit_count_sq_ne_top_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (_hρ : HasIntensity μ ρ) (_hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (a : Ambient d) :
    (∫⁻ c, c.count ((fun x => a + x) ⁻¹' unitWindow d) ^ 2 ∂μ) ≠ ∞ := by
  have heq := (hμ a).lintegral_comp ((Configuration.measurable_count (measurable_unitWindow d)).pow_const 2)
  simp only [count_translate] at heq
  rw [heq]
  exact hsecond

theorem memLp_translated_unit_count_two_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (a : Ambient d) :
    MemLp (fun c => (c.count ((fun x => a + x) ⁻¹' unitWindow d)).toReal) 2 μ := by
  have hW : MeasurableSet ((fun x => a + x) ⁻¹' unitWindow d) :=
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  exact memLp_two_toReal_of_second_moment (Configuration.measurable_count hW)
    (expected_translated_unit_count_sq_ne_top_of_second_moment μ hμ ρ hρ hρtop hsecond a)

theorem memLp_bounded_window_count_two_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hb : Bornology.IsBounded W) :
    MemLp (fun c => (c.count W).toReal) 2 μ := by
  obtain ⟨t, ht⟩ := exists_finite_unitWindow_cover hb
  let U := fun a : Ambient d => (fun x => a + x) ⁻¹' unitWindow d
  have hU : ∀ a, MeasurableSet (U a) := fun _ =>
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  have hsum : MemLp (fun c : Configuration (Ambient d) =>
      ∑ a ∈ t, (c.count (U a)).toReal) 2 μ :=
    memLp_finsetSum t (fun a _ => memLp_translated_unit_count_two_of_second_moment μ hμ ρ hρ hρtop hsecond a)
  apply hsum.mono' ((Configuration.measurable_count hW).ennreal_toReal).aestronglyMeasurable
  filter_upwards [] with c
  have hfinite : ∀ a, c.count (U a) ≠ ∞ := by
    intro a
    rw [← count_translate]
    exact count_ne_top_of_bounded (translate a c) (isBounded_unitWindow d)
  have hsumfinite : (∑ a ∈ t, c.count (U a)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun a _ => hfinite a)
  have hle := ENNReal.toReal_mono hsumfinite
    (count_le_finite_window_cover c t U (fun a _ => hU a) hW ht)
  rw [ENNReal.toReal_sum (fun a _ => hfinite a)] at hle
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hle

theorem expected_abs_difference_pair_unit_ne_top_of_second_moment {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |h (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞ := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_difference_cell_envelope_of_rapidDecay h hdecay 0
  have hfinite := ne_of_lt ((expected_pair_univ_le_cell_envelope μ hμ
    (fun x y => ENNReal.ofReal |h (x - y)|) (measurable_ofReal_abs_difference h hh) 0
    (fun z => ENNReal.ofReal (M z))
    (fun z x hx y hy => ENNReal.ofReal_le_ofReal (hbound z x hx y hy))).trans_lt
      (ENNReal.mul_ne_top hM (ENNReal.mul_ne_top (by simp) hsecond)).lt_top)
  have hw : ((fun x : Ambient d => (0 : Ambient d) + x) ⁻¹' unitWindow d) = unitWindow d := by
    ext x
    simp
  rw [hw] at hfinite
  exact hfinite

theorem integrable_spectralWindowSum_normSq_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    Integrable (fun c => Complex.normSq (spectralWindowSum W hbW ξ c)) μ := by
  have hc := integrable_square_of_memLp_two
    (memLp_bounded_window_count_two_of_second_moment μ hμ ρ hρ hρtop hsecond hW hbW)
  apply hc.mono' (Complex.continuous_normSq.measurable.comp
    (measurable_spectralWindowSum hW hbW ξ)).aestronglyMeasurable
  filter_upwards with c
  change ‖Complex.normSq (spectralWindowSum W hbW ξ c)‖ ≤ (c.count W).toReal ^ 2
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)] using
    spectralWindowSum_normSq_le_count_sq W hbW ξ c

theorem spectralWindowSum_mean_square_lower_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) (ξ : Ambient d) :
    ρ.toReal ^ 2 * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ≤
      ∫ c, Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ := by
  have h := complex_normSq_integral_le_integral_normSq μ (spectralWindowSum W hbW ξ)
    (integrable_spectralWindowSum_of_intensity μ ρ hρ hρtop hW hbW ξ)
    (integrable_spectralWindowSum_normSq_of_second_moment μ hμ ρ hρ hρtop hsecond hW hbW ξ)
  rw [integral_spectralWindowSum_of_intensity μ ρ hρ hρtop hW hbW ξ,
    Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at h
  exact h

theorem integrable_spectral_window_product_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun p : Ambient d × Configuration (Ambient d) =>
      g p.1 * Complex.normSq (spectralWindowSum W hbW p.1 p.2)) (ν.prod μ) := by
  have hc := integrable_square_of_memLp_two
    (memLp_bounded_window_count_two_of_second_moment μ hμ ρ hρ hρtop hsecond hW hbW)
  have hm : Measurable (fun p : Ambient d × Configuration (Ambient d) =>
      Complex.normSq (spectralWindowSum W hbW p.1 p.2)) :=
    Complex.continuous_normSq.measurable.comp (measurable_spectralWindowSum_joint hW hbW)
  apply (hg.norm.mul_prod hc).mono' (hg.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable)
  filter_upwards with p
  change ‖g p.1 * Complex.normSq (spectralWindowSum W hbW p.1 p.2)‖ ≤
    ‖g p.1‖ * (p.2.count W).toReal ^ 2
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (spectralWindowSum_normSq_le_count_sq W hbW p.1 p.2) (abs_nonneg _)

theorem integrable_expected_spectral_square_density_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun ξ => g ξ * ∫ c, Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ) ν := by
  have hi := (integrable_spectral_window_product_of_second_moment μ hμ ρ hρ hρtop
    hsecond ν g hg hW hbW).integral_prod_left
  simpa only [integral_const_mul] using hi

theorem integral_spectral_pair_eq_integral_expected_square_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ) =
      ∫ ξ, g ξ * ∫ c, Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ ∂ν := by
  have hprod := integrable_spectral_window_product_of_second_moment μ hμ ρ hρ hρtop
    hsecond ν g hg hW hbW
  calc
    _ = ∫ c, ∫ ξ, g ξ * Complex.normSq (spectralWindowSum W hbW ξ c) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      simpa only [spectralWindowSum] using
        realLocalized_spectral_pair_eq_integral_square ν g hg c hW hbW
    _ = ∫ ξ, ∫ c, g ξ * Complex.normSq (spectralWindowSum W hbW ξ c) ∂μ ∂ν :=
      (integral_integral_swap hprod).symm
    _ = _ := by simp only [integral_const_mul]

theorem integral_spectral_pair_window_lower_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    ρ.toReal ^ 2 * (∫ ξ, g ξ * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ∂ν) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ := by
  rw [integral_spectral_pair_eq_integral_expected_square_of_second_moment μ hμ ρ hρ hρtop hsecond ν g hg hW hbW]
  have hleft : (ρ.toReal ^ 2 * ∫ ξ,
      g ξ * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x) ∂ν) =
      ∫ ξ, g ξ * (ρ.toReal ^ 2 * Complex.normSq (∫ x, W.indicator (spectralPhase ξ) x)) ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    ring
  rw [hleft]
  apply integral_mono_ae (integrable_spectral_window_mean_density ν g hg ρ hW hbW)
    (integrable_expected_spectral_square_density_of_second_moment μ hμ ρ hρ hρtop hsecond ν g hg hW hbW)
  filter_upwards [hgnonneg] with ξ hξ
  exact mul_le_mul_of_nonneg_left
    (spectralWindowSum_mean_square_lower_of_second_moment μ hμ ρ hρ hρtop hsecond hW hbW ξ) hξ

theorem integral_spectral_pair_window_lower_real_volume_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    ρ.toReal ^ 2 * (∫ x in W, ∫ y in W, realSpectralKernel ν g (x - y)) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ := by
  rw [← spectral_window_square_eq_real_volume_pair ν g hg hW hbW]
  exact integral_spectral_pair_window_lower_of_second_moment μ hμ ρ hρ hρtop hsecond ν g hg hgnonneg hW hbW

theorem stationary_spectral_pair_anchor_lower_of_abs_unit_of_second_moment
    {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (ν : Measure (Ambient d)) [SFinite ν]
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ)
    (hvolume : Integrable (realSpectralKernel ν g) volume)
    (hunit : (∫⁻ c, localizedPairIntegral
      (fun x y => ENNReal.ofReal |realSpectralKernel ν g (x - y)|) c
        (unitWindow d) univ ∂μ) ≠ ∞) :
    ρ.toReal ^ 2 * (∫ v, realSpectralKernel ν g v) ≤
      ∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
        (unitWindow d) univ ∂μ := by
  have href := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ.toReal ^ 2)
      atTop (𝓝 (ρ.toReal ^ 2))).mul
    (tendsto_normalized_box_pair_integral (realSpectralKernel ν g) hvolume)
  have hpair := tendsto_normalized_expected_real_difference_pair_box_of_abs_unit μ hμ
    (realSpectralKernel ν g) (continuous_realSpectralKernel ν g hg).measurable hunit
  apply le_of_tendsto_of_tendsto' href hpair
  intro n
  have hv : 0 < (volume (periodCell d ((n : ℝ) + 1))).toReal := by
    rw [volume_periodCell, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (show 0 ≤ (n : ℝ) + 1 by positivity)]
    positivity
  have h := integral_spectral_pair_window_lower_real_volume_of_second_moment μ hμ ρ hρ hρtop hsecond
    ν g hg hgnonneg (measurable_periodCell d ((n : ℝ) + 1))
      (isBounded_periodCell d ((n : ℝ) + 1))
  have hd := div_le_div_of_nonneg_right
    (c := (volume (periodCell d ((n : ℝ) + 1))).toReal) h hv.le
  simpa only [mul_div_assoc] using hd

theorem integral_spectral_window_diagonal_split_of_abs_unit {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hunit : (∫⁻ c, localizedPairIntegral
      (fun x y => ENNReal.ofReal |realSpectralKernel ν g (x - y)|) c
      (unitWindow d) univ ∂μ) ≠ ∞)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W ∂μ) =
      (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W ∂μ) +
      (∫ ξ, g ξ ∂ν) * ρ.toReal * (volume W).toReal := by
  have hh := (continuous_realSpectralKernel ν g hg).measurable
  have hH := hh.comp (measurable_fst.sub measurable_snd)
  have hf := expected_pair_right_ne_top_of_full μ _ W W
    (expected_difference_pair_bounded_ne_top_of_unit μ hμ _ hh.norm.ennreal_ofReal hunit hW hbW)
  have hofffinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal
      |if y = x then 0 else realSpectralKernel ν g (x - y)|) c W W ∂μ) ≠ ∞ := by
    apply ne_of_lt ((lintegral_mono fun c => localizedPairIntegral_mono c W W ?_).trans_lt hf.lt_top)
    intro x _ y _
    by_cases hxy : y = x <;> simp [hxy]
  have hhoff : Measurable (Function.uncurry (fun x y : Ambient d =>
      if y = x then 0 else realSpectralKernel ν g (x - y))) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd measurable_fst) measurable_const hH
  have hoff := integrable_real_pair_of_expected_abs μ _ hhoff hW hbW hW hofffinite
  have hdiag := integrable_real_pair_window_diagonal_of_intensity μ ρ hρ hρtop
    (∫ ξ, g ξ ∂ν) hW hbW
  calc
    _ = ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W +
      realLocalizedPairIntegral (fun x y => if y = x then (∫ ξ, g ξ ∂ν) else 0) c W W ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      rw [realLocalizedPairIntegral_difference_split _ c hW hbW, realSpectralKernel_zero,
        realLocalizedPairIntegral_const_diagonal _ c hW hbW]
    _ = _ := by rw [integral_add hoff hdiag,
      integral_real_pair_window_diagonal_of_intensity μ ρ hρ hρtop _ hW hbW]

theorem integral_spectral_pair_anchor_diagonal_split_of_abs_unit_without_riesz
    {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hunit : (∫⁻ c, localizedPairIntegral
      (fun x y => ENNReal.ofReal |realSpectralKernel ν g (x - y)|) c
        (unitWindow d) univ ∂μ) ≠ ∞) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
      (unitWindow d) univ ∂μ) =
      (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c (unitWindow d) univ ∂μ) +
      (∫ ξ, g ξ ∂ν) * ρ.toReal := by
  have hm := (continuous_realSpectralKernel ν g hg).measurable
  have hfull := tendsto_normalized_expected_real_difference_pair_box_of_abs_unit μ hμ
    (realSpectralKernel ν g) hm hunit
  have hoff := (tendsto_normalized_expected_real_offDiagonal_box_of_abs_unit μ hμ
    (realSpectralKernel ν g) hm hunit).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (∫ ξ, g ξ ∂ν) * ρ.toReal)
      atTop (𝓝 ((∫ ξ, g ξ ∂ν) * ρ.toReal)))
  have he (n : ℕ) :
      (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
        (volume (periodCell d ((n : ℝ) + 1))).toReal =
      (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c
        (periodCell d ((n : ℝ) + 1)) (periodCell d ((n : ℝ) + 1)) ∂μ) /
        (volume (periodCell d ((n : ℝ) + 1))).toReal + (∫ ξ, g ξ ∂ν) * ρ.toReal := by
    have hden : (volume (periodCell d ((n : ℝ) + 1))).toReal ≠ 0 := by
      rw [volume_periodCell, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (show 0 ≤ (n : ℝ) + 1 by positivity)]
      positivity
    rw [integral_spectral_window_diagonal_split_of_abs_unit μ hμ ρ hρ hρtop ν g hg hunit
      (measurable_periodCell d ((n : ℝ) + 1)) (isBounded_periodCell d ((n : ℝ) + 1)),
      add_div, mul_div_assoc, div_self hden, mul_one]
  have hsame := hfull
  simp only [he] at hsame
  exact tendsto_nhds_unique hsame hoff

theorem stationary_schwartzMap_offDiagonal_lower_of_second_moment {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re) :
    ρ.toReal ^ 2 * (𝓕 f (0 : Ambient d)).re - (f 0).re * ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0 else (f (x - y)).re) c
        (unitWindow d) univ ∂μ := by
  have hk := realSpectralKernel_fourier_schwartzMap_re f him
  have hg := integrable_fourier_schwartzMap_re f
  have hd : HasRapidDecay (realSpectralKernel volume (fun ξ => (𝓕 f ξ).re)) := by
    rw [hk]
    exact hasRapidDecay_schwartzMap_re f
  have hh := (continuous_realSpectralKernel volume (fun ξ => (𝓕 f ξ).re) hg).measurable
  have hunit := expected_abs_difference_pair_unit_ne_top_of_second_moment μ hμ hsecond _ hh hd
  have hp := stationary_spectral_pair_anchor_lower_of_abs_unit_of_second_moment μ hμ ρ
    hρ hρtop hsecond volume (fun ξ => (𝓕 f ξ).re) hg hnonneg
    (by rw [hk]; exact integrable_schwartzMap_re f) hunit
  rw [integral_spectral_pair_anchor_diagonal_split_of_abs_unit_without_riesz μ hμ ρ
    hρ hρtop volume (fun ξ => (𝓕 f ξ).re) hg hunit, hk] at hp
  have hzero : (∫ ξ, (𝓕 f ξ).re) = (f 0).re := by
    rw [← realSpectralKernel_zero volume (fun ξ => (𝓕 f ξ).re), hk]
  rw [hzero, ← fourier_schwartzMap_zero_re f] at hp
  linarith

theorem expected_potential_gap_of_schwartzMap_minorant_of_second_moment {d : ℕ} 
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞)
    (P V : Ambient d → Ambient d → ℝ≥0∞)
    (hP : Measurable (Function.uncurry P)) (hV : Measurable (Function.uncurry V))
    (L : ℝ≥0∞) (hL : L ≠ ∞) (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re)
    (hminor : ∀ x y, x ≠ y → P x y + ENNReal.ofReal (-(f (x - y)).re) =
      V x y + ENNReal.ofReal (f (x - y)).re)
    (hcalib : L.toReal = (𝓕 f (0 : Ambient d)).re - (f 0).re) :
    L + (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy P c (unitWindow d) ∂μ := by
  let E := ∫⁻ c, orderedWindowEnergy P c (unitWindow d) ∂μ
  by_cases hE : E = ∞
  · change L + _ ≤ E
    rw [hE]
    exact le_top
  let H : Ambient d → Ambient d → ℝ := fun x y => if y = x then 0 else (f (x - y)).re
  have hH : Measurable (Function.uncurry H) := by
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_fst) measurable_const
      ((Complex.continuous_re.comp f.continuous).measurable.comp
        (measurable_fst.sub measurable_snd))
  have hunit := expected_abs_difference_pair_unit_ne_top_of_second_moment μ hμ hsecond
    (fun v => (f v).re) (Complex.continuous_re.comp f.continuous).measurable
    (hasRapidDecay_schwartzMap_re f)
  have hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c
      (unitWindow d) univ ∂μ) ≠ ∞ := by
    simpa only [differenceOffDiagonal_sub] using
      expected_abs_differenceOffDiagonal_unit_ne_top μ (fun v => (f v).re) hunit
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ H (unitWindow d) univ hfinite
  let A := ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c
    (unitWindow d) univ ∂μ
  let B := ∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c
    (unitWindow d) univ ∂μ
  let S := ∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ
  have hbal : E + B = S + A := expected_signed_minorant_balance μ P V hP hV
    (fun v => (f v).re) hminor (measurable_unitWindow d)
  have hS : S ≠ ∞ :=
    (ENNReal.add_ne_top.mp (hbal ▸ (ENNReal.add_ne_top.mpr ⟨hE, hn⟩))).1
  have hreal := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add hE hn, ENNReal.toReal_add hS hp] at hreal
  have hlower := stationary_schwartzMap_offDiagonal_lower_of_second_moment μ hμ 1 hρ
    (by simp) hsecond f him hnonneg
  simp only [ENNReal.toReal_one, one_pow, one_mul, mul_one] at hlower
  rw [← hcalib, integral_real_pair_eq_pos_sub_neg_of_expected_abs μ H hH
    (measurable_unitWindow d) (isBounded_unitWindow d) MeasurableSet.univ hfinite] at hlower
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hL, hS⟩) hE).mp
  rw [ENNReal.toReal_add hL hS]
  change L.toReal ≤ A.toReal - B.toReal at hlower
  linarith

end E8Leech
