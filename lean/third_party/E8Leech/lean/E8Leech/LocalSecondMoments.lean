import E8Leech.QuadraticSlack
import E8Leech.WindowNormalization

/-!
# Local second moments from finite Riesz energy

Finite energy, rather than an additional hard-core or bounded-count assumption,
controls the square of the number of points in the unit window. The diagonal is
charged to the first moment; every off-diagonal pair is charged to energy.
This supplies a prerequisite for signed stationary LP / Fourier estimates.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

/-- Count every window point, separating the distinguished diagonal point.
The second endpoint need not be truncated in the energy. -/
theorem window_count_cost_le_at_point {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (κ : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → κ ≤ V x y)
    (x : c.support) (hx : (x : Ambient d) ∈ W) :
    κ * c.count W ≤ κ + ∑' y : c.support,
      if (y : Ambient d) = (x : Ambient d) then 0 else V x y := by
  rw [← countingKernel_apply c hW, ← lintegral_indicator_const hW κ,
    countingKernel_lintegral_eq_tsum]
  calc
    (∑' y : c.support, W.indicator (fun _ => κ) y) ≤
        ∑' y : c.support, ((if y = x then κ else 0) +
          (if (y : Ambient d) = (x : Ambient d) then 0 else V x y)) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : y = x
      · subst y
        simp [hx]
      · have hne : (x : Ambient d) ≠ (y : Ambient d) := by
          intro h
          exact hy (Subtype.ext h.symm)
        by_cases hyW : (y : Ambient d) ∈ W
        · simpa [hy, hne.symm, hyW] using hV x hx y hyW hne
        · simp [hyW]
    _ = κ + ∑' y : c.support,
        if (y : Ambient d) = (x : Ambient d) then 0 else V x y := by
      rw [ENNReal.tsum_add]
      simp only [tsum_ite_eq]

/-- Diagonal completion gives a second-moment bound with no point enumeration. -/
theorem window_count_sq_cost_le {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (κ : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → κ ≤ V x y) :
    κ * c.count W ^ 2 ≤ κ * c.count W + orderedWindowEnergy V c W := by
  have hleft : κ * c.count W ^ 2 = ∑' x : c.support,
      W.indicator (fun _ => κ * c.count W) x := by
    rw [← countingKernel_lintegral_eq_tsum, lintegral_indicator_const hW,
      countingKernel_apply c hW]
    ring
  rw [hleft]
  calc
    (∑' x : c.support, W.indicator (fun _ => κ * c.count W) x) ≤
        ∑' x : c.support, if (x : Ambient d) ∈ W then
          κ + ∑' y : c.support, if (y : Ambient d) = (x : Ambient d) then 0 else V x y
        else 0 := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : (x : Ambient d) ∈ W
      · simpa [hx] using window_count_cost_le_at_point c hW κ V hV x hx
      · simp [hx]
    _ = κ * c.count W + orderedWindowEnergy V c W := by
      have hsplit : (fun x : c.support => if (x : Ambient d) ∈ W then
          κ + ∑' y : c.support, if (y : Ambient d) = (x : Ambient d) then 0 else V x y
        else 0) = (fun x : c.support => W.indicator (fun _ => κ) x) +
          (fun x : c.support => if (x : Ambient d) ∈ W then
            ∑' y : c.support, if (y : Ambient d) = (x : Ambient d) then 0 else V x y
          else 0) := by
        funext x
        by_cases hx : (x : Ambient d) ∈ W <;> simp [hx]
      rw [hsplit]
      change (∑' x : c.support, (W.indicator (fun _ => κ) x +
        (if (x : Ambient d) ∈ W then
          ∑' y : c.support, if (y : Ambient d) = (x : Ambient d) then 0 else V x y
        else 0))) = _
      rw [ENNReal.tsum_add, ← countingKernel_lintegral_eq_tsum,
        lintegral_indicator_const hW, countingKernel_apply c hW]
      simp only [orderedWindowEnergy]
      apply congrArg (fun e : ℝ≥0∞ => κ * c.count W + e)
      apply tsum_congr
      intro x
      by_cases hx : (x : Ambient d) ∈ W
      · simp only [if_pos hx]
        apply tsum_congr
        intro y
        by_cases hy : (y : Ambient d) = (x : Ambient d)
        · simp only [if_pos hy]
        · simp only [if_neg hy]
      · simp only [if_neg hx]

theorem expected_window_count_sq_cost_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (κ : ℝ≥0∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → κ ≤ V x y) :
    κ * (∫⁻ c, c.count W ^ 2 ∂μ) ≤
      κ * (∫⁻ c, c.count W ∂μ) + ∫⁻ c, orderedWindowEnergy V c W ∂μ := by
  rw [← lintegral_const_mul κ ((Configuration.measurable_count hW).pow_const 2)]
  calc
    (∫⁻ c, κ * c.count W ^ 2 ∂μ) ≤
        ∫⁻ c, κ * c.count W + orderedWindowEnergy V c W ∂μ :=
      lintegral_mono fun c => window_count_sq_cost_le c hW κ V hV
    _ = _ := by
      rw [lintegral_add_left ((Configuration.measurable_count hW).const_mul κ),
        lintegral_const_mul κ (Configuration.measurable_count hW)]

theorem expected_window_count_sq_ne_top_of_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (κ : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → κ ≤ V x y)
    (hcount : (∫⁻ c, c.count W ∂μ) ≠ ∞)
    (henergy : (∫⁻ c, orderedWindowEnergy V c W ∂μ) ≠ ∞) :
    (∫⁻ c, c.count W ^ 2 ∂μ) ≠ ∞ := by
  apply (ENNReal.lt_top_of_mul_ne_top_right (b := ∫⁻ c, c.count W ^ 2 ∂μ) ?_ hκ0).ne
  exact ne_of_lt ((expected_window_count_sq_cost_le μ hW κ V hV).trans_lt
    (ENNReal.add_lt_top.mpr ⟨(ENNReal.mul_ne_top hκtop hcount).lt_top, henergy.lt_top⟩))

/-- Bounded windows give an actual positive Riesz pair-cost lower bound. -/
theorem riesz_pair_cost_lower {d : ℕ} {s D : ℝ} (hs : 0 ≤ s) (_hD : 0 < D)
    (x y : Ambient d) (hne : x ≠ y) (hxy : dist x y ≤ D) :
    ENNReal.ofReal (D ^ (-s)) ≤ rieszPotential s x y := by
  rw [rieszPotential, ENNReal.ofReal_rpow_of_pos (dist_pos.mpr hne)]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_nonpos (dist_pos.mpr hne) hxy (neg_nonpos.mpr hs))

theorem isBounded_unitWindow (d : ℕ) : Bornology.IsBounded (unitWindow d) := by
  let Q : Set (Fin d → ℝ) := Set.pi univ (fun _ => Icc (0 : ℝ) 1)
  let K : Set (Ambient d) := (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Q
  have hQ : IsCompact Q := by
    have he : Q = {x : Fin d → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
      ext x
      simp only [Q, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq]
    rw [he]
    exact isCompact_pi_infinite (fun _ : Fin d => isCompact_Icc)
  have hK : IsCompact K := (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr hQ
  apply hK.isBounded.subset
  intro x hx
  exact Set.mem_pi.mpr (fun i _ => ⟨(hx i).1, (hx i).2.le⟩)

/-- Finite original energy supplies the local second moment needed by stationary
LP. No stationarity, probability, hard core, or second-moment hypothesis is added. -/
theorem expected_unit_count_sq_ne_top_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (henergy : rieszEnergy s μ ≠ ∞) :
    (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞ := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp (isBounded_unitWindow d)
  let D := max R 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  let κ := ENNReal.ofReal (D ^ (-s))
  have hκ0 : κ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hD _)
  apply expected_window_count_sq_ne_top_of_cost μ (measurable_unitWindow d)
    κ hκ0 ENNReal.ofReal_ne_top (rieszPotential s)
  · intro x hx y hy hne
    exact riesz_pair_cost_lower hs hD x y hne ((hR hx hy).trans (le_max_left R 1))
  · rwa [expected_count_unitWindow μ ρ hρ]
  · exact henergy

theorem expected_unit_count_sq_ne_top_of_excess {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hρ : HasIntensity μ 1)
    {L δ : ℝ≥0∞} (hexcess : HasRieszExcessAtMost s μ L δ) (hδtop : δ ≠ ∞) :
    (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞ := by
  apply expected_unit_count_sq_ne_top_of_riesz hs μ 1 hρ (by simp)
  exact ne_of_lt (hexcess.2.trans_lt (ENNReal.add_lt_top.mpr ⟨hexcess.1.lt_top, hδtop.lt_top⟩))

/-- Stationarity propagates this local square moment to every translated cell. -/
theorem expected_translated_unit_count_sq_ne_top {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (a : Ambient d) :
    (∫⁻ c, c.count ((fun x => a + x) ⁻¹' unitWindow d) ^ 2 ∂μ) ≠ ∞ := by
  have heq := (hμ a).lintegral_comp ((Configuration.measurable_count (measurable_unitWindow d)).pow_const 2)
  simp only [count_translate] at heq
  rw [heq]
  exact expected_unit_count_sq_ne_top_of_riesz hs μ ρ hρ hρtop henergy

theorem count_ne_top_of_bounded {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : Bornology.IsBounded W) : c.count W ≠ ∞ := by
  change Measure.count (c.support ∩ W) ≠ ∞
  apply ne_of_lt
  apply Measure.count_apply_lt_top.mpr
  exact (c.finite_on_compacts (closure W) hW.isCompact_closure).subset
    (fun _ hx => ⟨hx.1, subset_closure hx.2⟩)

/-- A finite nonnegative second moment controls the real L2 seminorm directly. -/
theorem memLp_two_toReal_of_second_moment {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f)
    (hsecond : (∫⁻ x, f x ^ 2 ∂μ) ≠ ∞) : MemLp (fun x => (f x).toReal) 2 μ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hf.ennreal_toReal.aestronglyMeasurable]
  apply lt_of_le_of_lt (lintegral_mono ?_) hsecond.lt_top
  intro x
  simp only [ENNReal.toReal_ofNat]
  rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  change ENNReal.ofReal (f x).toReal ^ ((2 : ℕ) : ℝ) ≤ f x ^ 2
  rw [ENNReal.rpow_natCast]
  exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2

theorem integrable_square_of_memLp_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => f x ^ 2) μ := by
  simpa [← memLp_one_iff_integrable] using hf.norm_rpow two_ne_zero ENNReal.ofNat_ne_top

theorem integrable_unit_count_sq_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞)
    (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞) (henergy : rieszEnergy s μ ≠ ∞) :
    Integrable (fun c => (c.count (unitWindow d)).toReal ^ 2) μ := by
  simpa only [ENNReal.toReal_pow] using integrable_toReal_of_lintegral_ne_top
    ((Configuration.measurable_count (measurable_unitWindow d)).pow_const 2).aemeasurable
    (expected_unit_count_sq_ne_top_of_riesz hs μ ρ hρ hρtop henergy)

theorem memLp_translated_unit_count_two {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (a : Ambient d) :
    MemLp (fun c => (c.count ((fun x => a + x) ⁻¹' unitWindow d)).toReal) 2 μ := by
  have hW : MeasurableSet ((fun x => a + x) ⁻¹' unitWindow d) :=
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  exact memLp_two_toReal_of_second_moment (Configuration.measurable_count hW)
    (expected_translated_unit_count_sq_ne_top hs μ hμ ρ hρ hρtop henergy a)

/-- Open translated interiors cover a compact closure. This avoids integer-grid
enumeration while still yielding a deterministic finite cover for each window. -/
theorem exists_finite_unitWindow_cover {d : ℕ} {W : Set (Ambient d)}
    (hW : Bornology.IsBounded W) :
    ∃ t : Finset (Ambient d), W ⊆ ⋃ a ∈ t, (fun x => a + x) ⁻¹' unitWindow d := by
  let I : Set (Ambient d) := {x | ∀ i, x i ∈ Ioo (0 : ℝ) 1}
  have hI : IsOpen I := by
    have he : I = ⋂ i : Fin d, (fun x : Ambient d => x i) ⁻¹' Ioo (0 : ℝ) 1 := by
      ext x
      simp [I]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)
  let p : Ambient d := WithLp.toLp 2 (fun _ : Fin d => (1 / 2 : ℝ))
  have hcover : closure W ⊆ ⋃ a : Ambient d, (fun x => a + x) ⁻¹' I := by
    intro x _
    refine mem_iUnion.mpr ⟨p - x, ?_⟩
    change p - x + x ∈ I
    rw [sub_add_cancel]
    change ∀ i : Fin d, (0 : ℝ) < 1 / 2 ∧ 1 / 2 < 1
    norm_num
  obtain ⟨t, ht⟩ := hW.isCompact_closure.elim_finite_subcover
    (fun a : Ambient d => (fun x => a + x) ⁻¹' I)
    (fun _ => hI.preimage (continuous_const.add continuous_id)) hcover
  refine ⟨t, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp (ht (subset_closure hx))
  obtain ⟨ha, hax⟩ := mem_iUnion.mp ha
  refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, ?_⟩⟩
  exact fun i => ⟨(hax i).1.le, (hax i).2⟩

theorem count_le_finite_window_cover {d : ℕ} (c : Configuration (Ambient d))
    {ι : Type*} (t : Finset ι) (U : ι → Set (Ambient d))
    (hU : ∀ i ∈ t, MeasurableSet (U i)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hcover : W ⊆ ⋃ i ∈ t, U i) :
    c.count W ≤ ∑ i ∈ t, c.count (U i) := by
  calc
    c.count W = countingKernel d c W := (countingKernel_apply c hW).symm
    _ ≤ countingKernel d c (⋃ i ∈ t, U i) := measure_mono hcover
    _ ≤ ∑ i ∈ t, countingKernel d c (U i) := measure_biUnion_finset_le t U
    _ = _ := Finset.sum_congr rfl fun i hi => countingKernel_apply c (hU i hi)

/-- Original finite Riesz energy and stationarity give L2 counts in every
bounded Borel window, without any additional moment assumption. -/
theorem memLp_bounded_window_count_two {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hb : Bornology.IsBounded W) :
    MemLp (fun c => (c.count W).toReal) 2 μ := by
  obtain ⟨t, ht⟩ := exists_finite_unitWindow_cover hb
  let U := fun a : Ambient d => (fun x => a + x) ⁻¹' unitWindow d
  have hU : ∀ a, MeasurableSet (U a) := fun _ =>
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  have hsum : MemLp (fun c : Configuration (Ambient d) =>
      ∑ a ∈ t, (c.count (U a)).toReal) 2 μ :=
    memLp_finsetSum t (fun a _ => memLp_translated_unit_count_two hs μ hμ ρ hρ hρtop henergy a)
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

theorem expected_bounded_window_count_sq_ne_top {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hb : Bornology.IsBounded W) :
    (∫⁻ c, c.count W ^ 2 ∂μ) ≠ ∞ := by
  apply (integrable_toReal_iff ((Configuration.measurable_count hW).pow_const 2).aemeasurable
    (ae_of_all _ (fun c => ENNReal.pow_ne_top (count_ne_top_of_bounded c hb)))).mp
  simpa only [ENNReal.toReal_pow] using
    integrable_square_of_memLp_two
      (memLp_bounded_window_count_two hs μ hμ ρ hρ hρtop henergy hW hb)

/-- A loose factor avoids square roots and holds even for infinite values. -/
theorem ennreal_mul_le_sum_squares (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  by_cases hab : a ≤ b
  · calc
      a * b ≤ b * b := mul_le_mul_of_nonneg_right hab zero_le
      _ = b ^ 2 := (pow_two b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_of_nonneg_left zero_le
  · calc
      a * b ≤ a * a := mul_le_mul_of_nonneg_left (not_le.mp hab).le zero_le
      _ = a ^ 2 := (pow_two a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_of_nonneg_right zero_le

/-- Uniform cell-correlation control for stationary laws, with no independence
assumption. Finite energy makes the right side finite by the preceding result. -/
theorem expected_unit_cell_count_product_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) (a b : Ambient d) :
    (∫⁻ c, c.count ((fun x => a + x) ⁻¹' unitWindow d) *
      c.count ((fun x => b + x) ⁻¹' unitWindow d) ∂μ) ≤
      2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ := by
  have hm (v : Ambient d) : MeasurableSet ((fun x => v + x) ⁻¹' unitWindow d) :=
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  have heq (v : Ambient d) :
      (∫⁻ c, c.count ((fun x => v + x) ⁻¹' unitWindow d) ^ 2 ∂μ) =
        ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ := by
    simpa only [count_translate] using (hμ v).lintegral_comp
      ((Configuration.measurable_count (measurable_unitWindow d)).pow_const 2)
  calc
    (∫⁻ c, c.count ((fun x => a + x) ⁻¹' unitWindow d) *
        c.count ((fun x => b + x) ⁻¹' unitWindow d) ∂μ) ≤
        ∫⁻ c, c.count ((fun x => a + x) ⁻¹' unitWindow d) ^ 2 +
          c.count ((fun x => b + x) ⁻¹' unitWindow d) ^ 2 ∂μ :=
      lintegral_mono fun c => ennreal_mul_le_sum_squares _ _
    _ = _ := by
      rw [lintegral_add_left ((Configuration.measurable_count (hm a)).pow_const 2), heq a, heq b]
      ring

theorem expected_bounded_window_count_product_ne_top {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {W U : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    (∫⁻ c, c.count W * c.count U ∂μ) ≠ ∞ := by
  apply ne_of_lt
  calc
    (∫⁻ c, c.count W * c.count U ∂μ) ≤ ∫⁻ c, c.count W ^ 2 + c.count U ^ 2 ∂μ :=
      lintegral_mono fun _ => ennreal_mul_le_sum_squares _ _
    _ = (∫⁻ c, c.count W ^ 2 ∂μ) + ∫⁻ c, c.count U ^ 2 ∂μ :=
      lintegral_add_left ((Configuration.measurable_count hW).pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.mpr
      ⟨(expected_bounded_window_count_sq_ne_top hs μ hμ ρ hρ hρtop henergy hW hbW).lt_top,
       (expected_bounded_window_count_sq_ne_top hs μ hμ ρ hρ hρtop henergy hU hbU).lt_top⟩

theorem integrable_bounded_window_count_product {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) {W U : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W)
    (hU : MeasurableSet U) (hbU : Bornology.IsBounded U) :
    Integrable (fun c => (c.count W).toReal * (c.count U).toReal) μ := by
  simpa only [Pi.mul_apply, ENNReal.toReal_mul] using integrable_toReal_of_lintegral_ne_top
    ((Configuration.measurable_count hW).mul (Configuration.measurable_count hU)).aemeasurable
    (expected_bounded_window_count_product_ne_top hs μ hμ ρ hρ hρtop henergy hW hbW hU hbU)

theorem expected_window_count_sq_le_of_pair_cost {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (κ : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → κ ≤ V x y) :
    (∫⁻ c, c.count W ^ 2 ∂μ) ≤ (∫⁻ c, c.count W ∂μ) +
      (∫⁻ c, orderedWindowEnergy V c W ∂μ) / κ := by
  have hdiv : (∫⁻ c, c.count W ^ 2 ∂μ) ≤
      (κ * (∫⁻ c, c.count W ∂μ) + ∫⁻ c, orderedWindowEnergy V c W ∂μ) / κ := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hκ0) (Or.inl hκtop)).mpr
    simpa only [mul_comm] using expected_window_count_sq_cost_le μ hW κ V hV
  simpa only [ENNReal.add_div, mul_comm κ, ENNReal.mul_div_cancel_right hκ0 hκtop] using hdiv

/-- An excess cap gives a second-moment constant chosen before the original
law or excess parameter. This is a proved bound, not another moment input. -/
theorem exists_uniform_unit_second_moment_bound {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (L Δ : ℝ≥0∞) (hLtop : L ≠ ∞) (hΔtop : Δ ≠ ∞) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      ∀ μ : Measure (Configuration (Ambient d)), HasIntensity μ 1 →
      ∀ δ : ℝ≥0∞, δ ≤ Δ → HasRieszExcessAtMost s μ L δ →
      (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≤ M := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp (isBounded_unitWindow d)
  let D := max R 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  let κ := ENNReal.ofReal (D ^ (-s))
  have hκ0 : κ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hD _)
  have hκtop : κ ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨1 + (L + Δ) / κ, ENNReal.add_ne_top.mpr
    ⟨by simp, ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨hLtop, hΔtop⟩) hκ0⟩, ?_⟩
  intro μ hρ δ hδ hexcess
  have hbase := expected_window_count_sq_le_of_pair_cost μ (measurable_unitWindow d)
    κ hκ0 hκtop (rieszPotential s)
    (fun x hx y hy hne => riesz_pair_cost_lower hs hD x y hne
      ((hR hx hy).trans (le_max_left R 1)))
  rw [expected_count_unitWindow μ 1 hρ] at hbase
  apply hbase.trans
  apply add_le_add le_rfl
  exact ENNReal.div_le_div_right (hexcess.2.trans (add_le_add le_rfl hδ)) κ

end E8Leech
