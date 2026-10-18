import E8Leech.LocalSecondMoments

/-!
# Localized two-point integrals

Both endpoints are restricted to bounded windows. The diagonal is included:
these are the finite quadratic forms needed for signed auxiliary functions,
not the diagonal-excluded Riesz energy. Finite original energy supplies their
integrability without a new moment or hard-core assumption.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

/-- A nonnegative local quadratic form, including the diagonal. -/
def localizedPairIntegral {d : ℕ} (V : Ambient d → Ambient d → ℝ≥0∞)
    (c : Configuration (Ambient d)) (W U : Set (Ambient d)) : ℝ≥0∞ :=
  ∫⁻ x, if x ∈ W then
    ∫⁻ y, if y ∈ U then V x y else 0 ∂countingKernel d c
  else 0 ∂countingKernel d c

theorem localizedPairIntegral_eq_tsum {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) :
    localizedPairIntegral V c W U = ∑' x : c.support,
      if (x : Ambient d) ∈ W then ∑' y : c.support,
        if (y : Ambient d) ∈ U then V x y else 0 else 0 := by
  unfold localizedPairIntegral
  rw [countingKernel_lintegral_eq_tsum]
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx, countingKernel_lintegral_eq_tsum]
  · simp only [if_neg hx]

theorem measurable_localizedPairIntegral {d : ℕ}
    {V : Ambient d → Ambient d → ℝ≥0∞} (hV : Measurable (Function.uncurry V))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hU : MeasurableSet U) :
    Measurable (fun c => localizedPairIntegral V c W U) := by
  have hi : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      ∫⁻ y, if y ∈ U then V p.2 y else 0 ∂countingKernel d p.1) := by
    apply measurable_countingKernel_lintegral_param (d := d)
      (f := fun p : (Configuration (Ambient d) × Ambient d) × Ambient d =>
        if p.2 ∈ U then V p.1.2 p.2 else 0)
      (fun p : Configuration (Ambient d) × Ambient d => p.1) measurable_fst
    exact Measurable.ite (hU.preimage measurable_snd)
      (hV.comp (measurable_fst.snd.prodMk measurable_snd)) measurable_const
  exact measurable_countingKernel_lintegral
    (Measurable.ite (hW.preimage measurable_snd) hi measurable_const)

theorem localizedPairIntegral_mono {d : ℕ}
    {V Z : Ambient d → Ambient d → ℝ≥0∞} (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) (h : ∀ x ∈ W, ∀ y ∈ U, V x y ≤ Z x y) :
    localizedPairIntegral V c W U ≤ localizedPairIntegral Z c W U := by
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ W
  · simp only [if_pos hx]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ U
    · simpa only [if_pos hy] using h x hx y hy
    · simp only [if_neg hy, le_refl]
  · simp only [if_neg hx, le_refl]

theorem localizedPairIntegral_const {d : ℕ} (M : ℝ≥0∞)
    (c : Configuration (Ambient d)) {W U : Set (Ambient d)}
    (hW : MeasurableSet W) (hU : MeasurableSet U) :
    localizedPairIntegral (fun _ _ => M) c W U = M * c.count W * c.count U := by
  unfold localizedPairIntegral
  have hi : (∫⁻ y, if y ∈ U then M else 0 ∂countingKernel d c) = M * c.count U := by
    change (∫⁻ y, U.indicator (fun _ => M) y ∂countingKernel d c) = _
    rw [lintegral_indicator_const hU, countingKernel_apply c hU]
  simp only [hi]
  change (∫⁻ x, W.indicator (fun _ => M * c.count U) x ∂countingKernel d c) = _
  rw [lintegral_indicator_const hW, countingKernel_apply c hW]
  ring

theorem localizedPairIntegral_le_count_product {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hU : MeasurableSet U)
    (M : ℝ≥0∞) (hV : ∀ x ∈ W, ∀ y ∈ U, V x y ≤ M) :
    localizedPairIntegral V c W U ≤ M * c.count W * c.count U := by
  exact (localizedPairIntegral_mono c W U hV).trans_eq
    (localizedPairIntegral_const M c hW hU)

theorem localizedPairIntegral_ne_top {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hV : ∀ x ∈ W, ∀ y ∈ U, V x y ≤ M) :
    localizedPairIntegral V c W U ≠ ∞ := by
  exact ne_of_lt ((localizedPairIntegral_le_count_product V c hW hU M hV).trans_lt
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hM (count_ne_top_of_bounded c hbW))
      (count_ne_top_of_bounded c hbU)).lt_top)

theorem expected_localizedPairIntegral_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (V : Ambient d → Ambient d → ℝ≥0∞)
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hU : MeasurableSet U)
    (M : ℝ≥0∞) (hV : ∀ x ∈ W, ∀ y ∈ U, V x y ≤ M) :
    (∫⁻ c, localizedPairIntegral V c W U ∂μ) ≤
      M * ∫⁻ c, c.count W * c.count U ∂μ := by
  have hm : Measurable (fun c : Configuration (Ambient d) => c.count W * c.count U) := by
    exact Measurable.mul (Configuration.measurable_count hW) (Configuration.measurable_count hU)
  rw [← lintegral_const_mul M hm]
  apply lintegral_mono
  intro c
  simpa only [mul_assoc] using localizedPairIntegral_le_count_product V c hW hU M hV

/-- The local pair moment is derived from the original Riesz hypothesis. -/
theorem expected_localizedPairIntegral_ne_top_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (V : Ambient d → Ambient d → ℝ≥0∞)
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hV : ∀ x ∈ W, ∀ y ∈ U, V x y ≤ M) :
    (∫⁻ c, localizedPairIntegral V c W U ∂μ) ≠ ∞ := by
  exact ne_of_lt ((expected_localizedPairIntegral_le μ V hW hU M hV).trans_lt
    (ENNReal.mul_ne_top hM (expected_bounded_window_count_product_ne_top
      hs μ hμ ρ hρ hρtop henergy hW hbW hU hbU)).lt_top)

theorem localizedPairIntegral_add {d : ℕ}
    (V Z : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) :
    localizedPairIntegral (fun x y => V x y + Z x y) c W U =
      localizedPairIntegral V c W U + localizedPairIntegral Z c W U := by
  simp only [localizedPairIntegral_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx]
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) ∈ U <;> simp [hy]
  · simp [hx]

/-- Jordan decomposition of a signed local pair form. Finiteness is proved
below before this form is used in real expectations. -/
def signedLocalizedPairIntegral {d : ℕ} (H : Ambient d → Ambient d → ℝ)
    (c : Configuration (Ambient d)) (W U : Set (Ambient d)) : ℝ :=
  (localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U).toReal -
    (localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U).toReal

theorem measurable_signedLocalizedPairIntegral {d : ℕ}
    {H : Ambient d → Ambient d → ℝ} (hH : Measurable (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hU : MeasurableSet U) :
    Measurable (fun c => signedLocalizedPairIntegral H c W U) := by
  exact (measurable_localizedPairIntegral hH.ennreal_ofReal hW hU).ennreal_toReal.sub
    (measurable_localizedPairIntegral hH.neg.ennreal_ofReal hW hU).ennreal_toReal

theorem ofReal_pos_add_neg_eq_abs (r : ℝ) :
    ENNReal.ofReal r + ENNReal.ofReal (-r) = ENNReal.ofReal |r| := by
  by_cases hr : 0 ≤ r
  · simp [abs_of_nonneg hr, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hr)]
  · have hr' := (not_le.mp hr).le
    simp [abs_of_nonpos hr', ENNReal.ofReal_eq_zero.mpr hr']

theorem localizedPairIntegral_pos_add_neg {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) :
    localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U +
      localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U =
        localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U := by
  rw [← localizedPairIntegral_add]
  simp only [ofReal_pos_add_neg_eq_abs]

/-- An absolute local envelope controls the signed form, including diagonal. -/
theorem abs_signedLocalizedPairIntegral_le {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)}
    (hfinite : localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U ≠ ∞) :
    |signedLocalizedPairIntegral H c W U| ≤
      (localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U).toReal := by
  let P := localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U
  let N := localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U
  have hsum : P + N = localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U :=
    localizedPairIntegral_pos_add_neg H c W U
  have hpn : P ≠ ∞ ∧ N ≠ ∞ := ENNReal.add_ne_top.mp (hsum ▸ hfinite)
  change |P.toReal - N.toReal| ≤ _
  rw [← hsum, ENNReal.toReal_add hpn.1 hpn.2]
  exact abs_sub_le_iff.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := N)],
    by linarith [ENNReal.toReal_nonneg (a := P)]⟩

/-- Both Jordan parts are integrable; no extra second-moment hypothesis. -/
theorem integrable_signedLocalizedPairIntegral_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (H : Ambient d → Ambient d → ℝ)
    (hH : Measurable (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (M : ℝ) (hbound : ∀ x ∈ W, ∀ y ∈ U, |H x y| ≤ M) :
    Integrable (fun c => signedLocalizedPairIntegral H c W U) μ := by
  have hp : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U ∂μ) ≠ ∞ := by
    apply expected_localizedPairIntegral_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy
      _ hW hbW hU hbU (ENNReal.ofReal M) ENNReal.ofReal_ne_top
    intro x hx y hy
    exact ENNReal.ofReal_le_ofReal ((le_abs_self (H x y)).trans (hbound x hx y hy))
  have hn : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U ∂μ) ≠ ∞ := by
    apply expected_localizedPairIntegral_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy
      _ hW hbW hU hbU (ENNReal.ofReal M) ENNReal.ofReal_ne_top
    intro x hx y hy
    exact ENNReal.ofReal_le_ofReal ((neg_le_abs (H x y)).trans (hbound x hx y hy))
  exact (integrable_toReal_of_lintegral_ne_top
    (measurable_localizedPairIntegral hH.ennreal_ofReal hW hU).aemeasurable hp).sub
    (integrable_toReal_of_lintegral_ne_top
      (measurable_localizedPairIntegral hH.neg.ennreal_ofReal hW hU).aemeasurable hn)

theorem abs_signedLocalizedPairIntegral_le_count_product {d : ℕ}
    (H : Ambient d → Ambient d → ℝ) (c : Configuration (Ambient d))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x ∈ W, ∀ y ∈ U, |H x y| ≤ M) :
    |signedLocalizedPairIntegral H c W U| ≤ M * (c.count W).toReal * (c.count U).toReal := by
  have hb : ∀ x ∈ W, ∀ y ∈ U, ENNReal.ofReal |H x y| ≤ ENNReal.ofReal M :=
    fun x hx y hy => ENNReal.ofReal_le_ofReal (hbound x hx y hy)
  have hf := localizedPairIntegral_ne_top (fun x y => ENNReal.ofReal |H x y|)
    c hW hbW hU hbU (ENNReal.ofReal M) ENNReal.ofReal_ne_top hb
  have hprod : ENNReal.ofReal M * c.count W * c.count U ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (count_ne_top_of_bounded c hbW)) (count_ne_top_of_bounded c hbU)
  calc
    _ ≤ (localizedPairIntegral (fun x y => ENNReal.ofReal |H x y|) c W U).toReal :=
      abs_signedLocalizedPairIntegral_le H c hf
    _ ≤ (ENNReal.ofReal M * c.count W * c.count U).toReal :=
      ENNReal.toReal_mono hprod (localizedPairIntegral_le_count_product
        (fun x y => ENNReal.ofReal |H x y|) c hW hU (ENNReal.ofReal M) hb)
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-- Finite Jordan expectations justify subtraction before any LP identity. -/
theorem integral_signedLocalizedPairIntegral_eq {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    {W U : Set (Ambient d)} (hW : MeasurableSet W) (hU : MeasurableSet U)
    (hp : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U ∂μ) ≠ ∞)
    (hn : (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U ∂μ) ≠ ∞) :
    (∫ c, signedLocalizedPairIntegral H c W U ∂μ) =
      (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (H x y)) c W U ∂μ).toReal -
        (∫⁻ c, localizedPairIntegral (fun x y => ENNReal.ofReal (-H x y)) c W U ∂μ).toReal := by
  have hpm := measurable_localizedPairIntegral
    (V := fun x y => ENNReal.ofReal (H x y)) hH.ennreal_ofReal hW hU
  have hnm := measurable_localizedPairIntegral
    (V := fun x y => ENNReal.ofReal (-H x y)) hH.neg.ennreal_ofReal hW hU
  unfold signedLocalizedPairIntegral
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hp)
    (integrable_toReal_of_lintegral_ne_top hnm.aemeasurable hn),
    integral_toReal hpm.aemeasurable (ae_lt_top hpm hp),
    integral_toReal hnm.aemeasurable (ae_lt_top hnm hn)]

theorem expected_localizedPairIntegral_unit_cells_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → Ambient d → ℝ≥0∞) (a b : Ambient d)
    (M : ℝ≥0∞)
    (hV : ∀ x ∈ (fun z => a + z) ⁻¹' unitWindow d,
      ∀ y ∈ (fun z => b + z) ⁻¹' unitWindow d, V x y ≤ M) :
    (∫⁻ c, localizedPairIntegral V c
      ((fun z => a + z) ⁻¹' unitWindow d) ((fun z => b + z) ⁻¹' unitWindow d) ∂μ) ≤
      M * (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) := by
  have hm (v : Ambient d) : MeasurableSet ((fun z => v + z) ⁻¹' unitWindow d) :=
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  exact (expected_localizedPairIntegral_le μ V (hm a) (hm b) M hV).trans
    (mul_le_mul_of_nonneg_left (expected_unit_cell_count_product_le μ hμ a b) zero_le)

/-- A summable cell envelope controls a countable collection of local pairs.
This is the analytic-tail interface; constructing a covering and a Schwartz
envelope for the actual auxiliary function is a separate proof obligation. -/
theorem expected_localizedPairIntegral_cell_series_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : ℕ → Ambient d → Ambient d → ℝ≥0∞)
    (hVmeas : ∀ n, Measurable (Function.uncurry (V n)))
    (a b : ℕ → Ambient d) (M : ℕ → ℝ≥0∞)
    (hV : ∀ n, ∀ x ∈ (fun z => a n + z) ⁻¹' unitWindow d,
      ∀ y ∈ (fun z => b n + z) ⁻¹' unitWindow d, V n x y ≤ M n) :
    (∫⁻ c, ∑' n, localizedPairIntegral (V n) c
      ((fun z => a n + z) ⁻¹' unitWindow d)
      ((fun z => b n + z) ⁻¹' unitWindow d) ∂μ) ≤
      (∑' n, M n) * (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) := by
  have hm (v : Ambient d) : MeasurableSet ((fun z => v + z) ⁻¹' unitWindow d) :=
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  rw [lintegral_tsum (fun n =>
    (measurable_localizedPairIntegral (hVmeas n) (hm (a n)) (hm (b n))).aemeasurable)]
  calc
    _ ≤ ∑' n, M n * (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) :=
      ENNReal.tsum_le_tsum fun n =>
        expected_localizedPairIntegral_unit_cells_le μ hμ (V n) (a n) (b n) (M n) (hV n)
    _ = _ := ENNReal.tsum_mul_right

theorem expected_localizedPairIntegral_cell_series_ne_top_of_riesz
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (V : ℕ → Ambient d → Ambient d → ℝ≥0∞)
    (hVmeas : ∀ n, Measurable (Function.uncurry (V n)))
    (a b : ℕ → Ambient d) (M : ℕ → ℝ≥0∞) (hM : (∑' n, M n) ≠ ∞)
    (hV : ∀ n, ∀ x ∈ (fun z => a n + z) ⁻¹' unitWindow d,
      ∀ y ∈ (fun z => b n + z) ⁻¹' unitWindow d, V n x y ≤ M n) :
    (∫⁻ c, ∑' n, localizedPairIntegral (V n) c
      ((fun z => a n + z) ⁻¹' unitWindow d)
      ((fun z => b n + z) ⁻¹' unitWindow d) ∂μ) ≠ ∞ := by
  exact ne_of_lt ((expected_localizedPairIntegral_cell_series_le μ hμ V hVmeas a b M hV).trans_lt
    (ENNReal.mul_ne_top hM (ENNReal.mul_ne_top (by simp)
      (expected_unit_count_sq_ne_top_of_riesz hs μ ρ hρ hρtop henergy))).lt_top)

end E8Leech
