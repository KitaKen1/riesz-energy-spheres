import E8Leech.GaussianPairIntegrals

/-!
# Genuine real pair integrals with an unbounded second window

The first window contains finitely many support points. An absolute pair
integral below infinity therefore makes every relevant inner integral
integrable. Finite first-endpoint sums then identify the actual double Bochner
integral with the Jordan form. No product-measure Fubini or measurable point
enumeration is used. Expected finiteness still comes from the original energy.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

/-- Only the first endpoint is truncated to a bounded window. -/
theorem localizedPairIntegral_eq_outer_sum {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (U : Set (Ambient d)) :
    localizedPairIntegral V c W U = ∑ x ∈ windowPointFinset c W hbW,
      ∫⁻ y, U.indicator (V x) y ∂countingKernel d c := by
  change (∫⁻ x, W.indicator
    (fun x => ∫⁻ y, U.indicator (V x) y ∂countingKernel d c) x ∂countingKernel d c) = _
  exact lintegral_countingKernel_indicator_eq_sum c hW hbW _

/-- This monotonicity does not require a measurable second window. -/
theorem localizedPairIntegral_right_le_univ {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) :
    localizedPairIntegral V c W U ≤ localizedPairIntegral V c W univ := by
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ W
  · simp only [if_pos hx, mem_univ, if_true]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ U <;> simp [hy]
  · simp only [if_neg hx, le_refl]

theorem inner_abs_pair_ne_top_of_finite_abs {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (U : Set (Ambient d))
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ≠ ∞)
    {x : Ambient d} (hx : x ∈ windowPointFinset c W hbW) :
    (∫⁻ y, U.indicator (fun y => ENNReal.ofReal |H x y|) y ∂countingKernel d c) ≠ ∞ := by
  rw [localizedPairIntegral_eq_outer_sum _ c hW hbW U] at hfinite
  exact (ENNReal.sum_ne_top.mp hfinite) x hx

theorem integrable_inner_pair_of_finite_abs {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ≠ ∞)
    {x : Ambient d} (hx : x ∈ windowPointFinset c W hbW) :
    Integrable (U.indicator (H x)) (countingKernel d c) := by
  have hm : Measurable (H x) := hH.comp (measurable_const.prodMk measurable_id)
  refine ⟨(hm.indicator hU).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hf := inner_abs_pair_ne_top_of_finite_abs H c hW hbW U hfinite hx
  apply lt_top_iff_ne_top.mpr
  convert hf using 1
  congr 1
  funext y
  by_cases hy : y ∈ U <;> simp [hy, Real.norm_eq_abs]

theorem integral_inner_pair_eq_Jordan {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    (U : Set (Ambient d)) (x : Ambient d)
    (hint : Integrable (U.indicator (H x)) (countingKernel d c)) :
    (∫ y, U.indicator (H x) y ∂countingKernel d c) =
      (∫⁻ y, U.indicator (fun y => ENNReal.ofReal (H x y)) y ∂countingKernel d c).toReal -
      (∫⁻ y, U.indicator (fun y => ENNReal.ofReal (-H x y)) y ∂countingKernel d c).toReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  congr 2 <;> congr 1 <;> funext y <;> by_cases hy : y ∈ U <;> simp [hy]

/-- Absolute convergence is checked before the Jordan parts are subtracted. -/
theorem signedLocalizedPairIntegral_eq_real_of_finite_abs {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ≠ ∞) :
    signedLocalizedPairIntegral H c W U = realLocalizedPairIntegral H c W U := by
  have hpn := ENNReal.add_ne_top.mp
    ((localizedPairIntegral_pos_add_neg H c W U).symm ▸ hfinite)
  unfold signedLocalizedPairIntegral realLocalizedPairIntegral
  rw [localizedPairIntegral_eq_outer_sum _ c hW hbW U,
    localizedPairIntegral_eq_outer_sum _ c hW hbW U] at hpn ⊢
  rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hpn.1),
    ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hpn.2), ← Finset.sum_sub_distrib,
    integral_countingKernel_indicator_eq_sum c hW hbW]
  apply Finset.sum_congr rfl
  intro x hx
  exact (integral_inner_pair_eq_Jordan H c U x
    (integrable_inner_pair_of_finite_abs H hH c hW hbW hU hfinite hx)).symm

theorem abs_realLocalizedPairIntegral_le_of_finite_abs {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ≠ ∞) :
    |realLocalizedPairIntegral H c W U| ≤
      (localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U).toReal := by
  rw [← signedLocalizedPairIntegral_eq_real_of_finite_abs H hH c hW hbW hU hfinite]
  exact abs_signedLocalizedPairIntegral_le H c hfinite

theorem measurable_ofReal_abs_pair_kernel {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (fun x y => ENNReal.ofReal |H x y|)) := by
  change Measurable (fun q : Ambient d × Ambient d => ENNReal.ofReal |H q.1 q.2|)
  have hp : Measurable (fun q : Ambient d × Ambient d => H q.1 q.2) := hH
  simpa only [Real.norm_eq_abs] using hp.norm.ennreal_ofReal

/-- Neither part is converted to a real expectation before its finiteness is checked. -/
theorem expected_pair_Jordan_parts_ne_top_of_abs {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (H : Ambient d → Ambient d → ℝ)
    (W U : Set (Ambient d))
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ∂μ) ≠ ∞) :
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U ∂μ) ≠ ∞ ∧
    (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U ∂μ) ≠ ∞ := by
  constructor
  · exact ne_of_lt ((lintegral_mono fun c => localizedPairIntegral_mono c W U
      (fun x _ y _ => ENNReal.ofReal_le_ofReal (le_abs_self (H x y)))).trans_lt hfinite.lt_top)
  · exact ne_of_lt ((lintegral_mono fun c => localizedPairIntegral_mono c W U
      (fun x _ y _ => ENNReal.ofReal_le_ofReal (neg_le_abs (H x y)))).trans_lt hfinite.lt_top)

theorem ae_signed_pair_eq_real_of_expected_abs {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ∂μ) ≠ ∞) :
    ∀ᵐ c ∂μ, signedLocalizedPairIntegral H c W U = realLocalizedPairIntegral H c W U := by
  filter_upwards [ae_lt_top (measurable_localizedPairIntegral
    (measurable_ofReal_abs_pair_kernel H hH) hW hU) hfinite] with c hc
  exact signedLocalizedPairIntegral_eq_real_of_finite_abs H hH c hW hbW hU hc.ne

theorem ae_inner_pair_integrable_of_expected_abs {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ∂μ) ≠ ∞) :
    ∀ᵐ c ∂μ, ∀ x ∈ c.support ∩ W, Integrable (U.indicator (H x)) (countingKernel d c) := by
  filter_upwards [ae_lt_top (measurable_localizedPairIntegral
    (measurable_ofReal_abs_pair_kernel H hH) hW hU) hfinite] with c hc
  intro x hx
  exact integrable_inner_pair_of_finite_abs H hH c hW hbW hU hc.ne
    ((mem_windowPointFinset c W hbW x).mpr hx)

theorem integrable_real_pair_of_expected_abs {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ∂μ) ≠ ∞) :
    Integrable (fun c => realLocalizedPairIntegral H c W U) μ := by
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ H W U hfinite
  have hi : Integrable (fun c => signedLocalizedPairIntegral H c W U) μ :=
    (integrable_toReal_of_lintegral_ne_top
      (measurable_localizedPairIntegral hH.ennreal_ofReal hW hU).aemeasurable hp).sub
    (integrable_toReal_of_lintegral_ne_top
      (measurable_localizedPairIntegral hH.neg.ennreal_ofReal hW hU).aemeasurable hn)
  exact hi.congr (ae_signed_pair_eq_real_of_expected_abs μ H hH hW hbW hU hfinite)

theorem integral_real_pair_eq_pos_sub_neg_of_expected_abs {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    {U : Set (Ambient d)} (hU : MeasurableSet U)
    (hfinite : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ∂μ) ≠ ∞) :
    (∫ c, realLocalizedPairIntegral H c W U ∂μ) =
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U ∂μ).toReal -
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U ∂μ).toReal := by
  obtain ⟨hp, hn⟩ := expected_pair_Jordan_parts_ne_top_of_abs μ H W U hfinite
  have he : (fun c => signedLocalizedPairIntegral H c W U) =ᵐ[μ]
      (fun c => realLocalizedPairIntegral H c W U) :=
    ae_signed_pair_eq_real_of_expected_abs μ H hH hW hbW hU hfinite
  rw [integral_congr_ae he.symm]
  exact integral_signedLocalizedPairIntegral_eq μ H hH hW hU hp hn

theorem isBounded_translated_unitWindow {d : ℕ} (a : Ambient d) :
    Bornology.IsBounded ((fun x => a + x) ⁻¹' unitWindow d) :=
  (isometry_add_left a).antilipschitz.isBounded_preimage (isBounded_unitWindow d)

/-- The measurable-kernel hypotheses stay separate from absolute convergence. -/
theorem ae_signed_difference_pair_univ_eq_real_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    ∀ᵐ c ∂μ, signedLocalizedPairIntegral (fun x y => h (x - y)) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ =
      realLocalizedPairIntegral (fun x y => h (x - y)) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ :=
  ae_signed_pair_eq_real_of_expected_abs μ (fun x y => h (x - y))
    (hh.comp (measurable_fst.sub measurable_snd))
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    (isBounded_translated_unitWindow a) MeasurableSet.univ
    (expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay a)

theorem integrable_real_difference_pair_univ_of_rapidDecay
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (h : Ambient d → ℝ) (hh : Measurable h) (hdecay : HasRapidDecay h) (a : Ambient d) :
    Integrable (fun c => realLocalizedPairIntegral (fun x y => h (x - y)) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ) μ :=
  integrable_real_pair_of_expected_abs μ (fun x y => h (x - y))
    (hh.comp (measurable_fst.sub measurable_snd))
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    (isBounded_translated_unitWindow a) MeasurableSet.univ
    (expected_abs_difference_pair_univ_ne_top_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
      h hh hdecay a)

theorem integrable_real_gaussian_pair_univ_of_riesz
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {α : ℝ} (hα : 0 < α) (a : Ambient d) :
    Integrable (fun c => realLocalizedPairIntegral (fun x y => gaussianKernel α (x - y)) c
      ((fun x => a + x) ⁻¹' unitWindow d) univ) μ :=
  integrable_real_difference_pair_univ_of_rapidDecay hs μ hμ ρ hρ hρtop henergy
    (gaussianKernel α) (continuous_gaussianKernel α).measurable (hasRapidDecay_gaussianKernel hα) a

end E8Leech
