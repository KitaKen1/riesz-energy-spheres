import E8Leech.Dilation
import E8Leech.E8Geometry
import E8Leech.WindowNormalization

/-!
# Guarded periodization of one separated configuration

Repeat the points in [r/2, L-r/2)^d with periods L times integer vectors.
A different integer coordinate supplies the separation between different copies.
Local finiteness follows from separation. The separated configuration is an
intermediate object supplied by deletion and expansion, not an extra hypothesis
on the original process.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def coordinateBox (d : ℕ) (lo hi : ℝ) : Set (Ambient d) :=
  {x | ∀ i, x i ∈ Ico lo hi}

def guardInnerBox (d : ℕ) (L r : ℝ) : Set (Ambient d) :=
  coordinateBox d (r / 2) (L - r / 2)

def periodCell (d : ℕ) (L : ℝ) : Set (Ambient d) := coordinateBox d 0 L

theorem measurable_coordinateBox (d : ℕ) (lo hi : ℝ) :
    MeasurableSet (coordinateBox d lo hi) := by
  have he : coordinateBox d lo hi = ⋂ i : Fin d,
      (fun x : Ambient d => x i) ⁻¹' Ico lo hi := by
    ext x
    simp [coordinateBox]
  rw [he]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ico.preimage (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable

theorem measurable_guardInnerBox (d : ℕ) (L r : ℝ) :
    MeasurableSet (guardInnerBox d L r) := measurable_coordinateBox d _ _

theorem measurable_periodCell (d : ℕ) (L : ℝ) :
    MeasurableSet (periodCell d L) := measurable_coordinateBox d _ _

theorem volume_coordinateBox (d : ℕ) (lo hi : ℝ) :
    volume (coordinateBox d lo hi) = ENNReal.ofReal (hi - lo) ^ d := by
  let Q : Set (Fin d → ℝ) := Set.pi univ (fun _ => Ico lo hi)
  have hQ : MeasurableSet Q := MeasurableSet.pi (Set.to_countable univ)
    (fun _ _ => measurableSet_Ico)
  have he : coordinateBox d lo hi = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' Q := by
    ext x
    simp [coordinateBox, Q, Set.mem_pi]
  rw [he, (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hQ.nullMeasurableSet]
  simp [Q, Real.volume_pi_Ico]

theorem volume_guardInnerBox (d : ℕ) (L r : ℝ) :
    volume (guardInnerBox d L r) = ENNReal.ofReal (L - r) ^ d := by
  rw [guardInnerBox, volume_coordinateBox]
  congr 2
  ring

theorem volume_periodCell (d : ℕ) (L : ℝ) :
    volume (periodCell d L) = ENNReal.ofReal L ^ d := by
  simp only [periodCell, volume_coordinateBox, sub_zero]

def periodShift {d : ℕ} (L : ℝ) (m : Fin d → ℤ) : Ambient d :=
  WithLp.toLp 2 (fun i => L * (m i : ℝ))

@[simp] theorem periodShift_apply {d : ℕ} (L : ℝ) (m : Fin d → ℤ) (i : Fin d) :
    periodShift L m i = L * (m i : ℝ) := rfl

@[simp] theorem periodShift_zero {d : ℕ} (L : ℝ) :
    periodShift (d := d) L 0 = 0 := by
  ext i
  simp [periodShift]

theorem periodShift_add {d : ℕ} (L : ℝ) (m n : Fin d → ℤ) :
    periodShift L (m + n) = periodShift L m + periodShift L n := by
  ext i
  simp [periodShift, mul_add]

theorem guard_copies_distance {d : ℕ} {L r : ℝ} (hL : 0 ≤ L)
    {m n : Fin d → ℤ} (hmn : m ≠ n) {x y : Ambient d}
    (hx : x ∈ guardInnerBox d L r) (hy : y ∈ guardInnerBox d L r) :
    r ≤ dist (periodShift L m + x) (periodShift L n + y) := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ n i := by
    by_contra h
    apply hmn
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hx' : r / 2 ≤ x i ∧ x i < L - r / 2 := hx i
  have hy' : r / 2 ≤ y i ∧ y i < L - r / 2 := hy i
  have hcoord : r ≤ |(periodShift L m + x) i - (periodShift L n + y) i| := by
    by_cases hmn' : m i < n i
    · have hcast : (m i : ℝ) + 1 ≤ (n i : ℝ) := by
        exact_mod_cast (show m i + 1 ≤ n i from by omega)
      have hmul := mul_le_mul_of_nonneg_left hcast hL
      ring_nf at hmul
      have hl : r ≤ (periodShift L n + y) i - (periodShift L m + x) i := by
        change r ≤ L * (n i : ℝ) + y i - (L * (m i : ℝ) + x i)
        linarith
      exact hl.trans (by simpa only [neg_sub] using (neg_le_abs
        ((periodShift L m + x) i - (periodShift L n + y) i)))
    · have hcast : (n i : ℝ) + 1 ≤ (m i : ℝ) := by
        exact_mod_cast (show n i + 1 ≤ m i from by omega)
      have hmul := mul_le_mul_of_nonneg_left hcast hL
      ring_nf at hmul
      have hl : r ≤ (periodShift L m + x) i - (periodShift L n + y) i := by
        change r ≤ L * (m i : ℝ) + x i - (L * (n i : ℝ) + y i)
        linarith
      exact hl.trans (le_abs_self _)
  exact hcoord.trans (by simpa only [Real.dist_eq] using
    (PiLp.dist_apply_le (periodShift L m + x) (periodShift L n + y) i))

def guardedPeriodizationSupport {d : ℕ} (c : Configuration (Ambient d)) (L r : ℝ) :
    Set (Ambient d) :=
  ⋃ m : Fin d → ℤ, (fun x => periodShift L m + x) '' (c.support ∩ guardInnerBox d L r)

theorem guard_copies_disjoint {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : 0 ≤ L) :
    Pairwise (fun m n : Fin d → ℤ => Disjoint
      ((fun x => periodShift L m + x) '' (c.support ∩ guardInnerBox d L r))
      ((fun x => periodShift L n + x) '' (c.support ∩ guardInnerBox d L r))) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  change periodShift L m + x = z at hxz
  change periodShift L n + y = z at hyz
  have hd := guard_copies_distance hL hmn hx.2 hy.2
  rw [hxz, hyz, dist_self] at hd
  exact (not_le_of_gt hr) hd

theorem guard_shift_in_cell_iff {d : ℕ} (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (m : Fin d → ℤ) {x : Ambient d} (hx : x ∈ guardInnerBox d L r) :
    periodShift L m + x ∈ periodCell d L ↔ m = 0 := by
  have hLp : 0 < L := hr.trans hL
  constructor
  · intro hz
    funext i
    have hx' : r / 2 ≤ x i ∧ x i < L - r / 2 := hx i
    have hz' : 0 ≤ L * (m i : ℝ) + x i ∧ L * (m i : ℝ) + x i < L := hz i
    change m i = 0
    by_contra hm
    by_cases hmneg : m i < 0
    · have hc : (m i : ℝ) ≤ -1 := by
        exact_mod_cast (show m i ≤ -1 from by omega)
      have hh := mul_le_mul_of_nonneg_left hc hLp.le
      linarith
    · have hc : (1 : ℝ) ≤ (m i : ℝ) := by
        exact_mod_cast (show (1 : ℤ) ≤ m i from by omega)
      have hh := mul_le_mul_of_nonneg_left hc hLp.le
      linarith
  · rintro rfl
    simp only [periodShift_zero, zero_add]
    intro i
    have hx' : r / 2 ≤ x i ∧ x i < L - r / 2 := hx i
    constructor <;> linarith

theorem guardedPeriodizationSupport_inter_cell {d : ℕ}
    (c : Configuration (Ambient d)) (L r : ℝ) (hr : 0 < r) (hL : r < L) :
    guardedPeriodizationSupport c L r ∩ periodCell d L =
      c.support ∩ guardInnerBox d L r := by
  ext z
  constructor
  · rintro ⟨hz, hzQ⟩
    obtain ⟨m, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    have hm := (guard_shift_in_cell_iff L r hr hL m hx.2).mp hzQ
    subst m
    simpa only [periodShift_zero, zero_add] using hx
  · intro hz
    constructor
    · apply Set.mem_iUnion.mpr
      exact ⟨0, z, hz, by simp⟩
    · have hh := (guard_shift_in_cell_iff L r hr hL 0 hz.2).mpr rfl
      simpa only [periodShift_zero, zero_add] using hh

theorem guardedPeriodizationSupport_periodic {d : ℕ}
    (c : Configuration (Ambient d)) (L r : ℝ) (n : Fin d → ℤ) :
    (fun x => periodShift L n + x) '' guardedPeriodizationSupport c L r =
      guardedPeriodizationSupport c L r := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨n + m, x, hx, ?_⟩
    change periodShift L (n + m) + x = periodShift L n + (periodShift L m + x)
    rw [periodShift_add, add_assoc]
  · intro hz
    obtain ⟨m, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    refine ⟨periodShift L (m - n) + x, Set.mem_iUnion.mpr ⟨m - n, x, hx, rfl⟩, ?_⟩
    change periodShift L n + (periodShift L (m - n) + x) = periodShift L m + x
    rw [← add_assoc, ← periodShift_add]
    congr 2
    abel

theorem guardedPeriodization_separated {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hL : 0 ≤ L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    ∀ x ∈ guardedPeriodizationSupport c L r,
      ∀ y ∈ guardedPeriodizationSupport c L r, x ≠ y → r ≤ dist x y := by
  intro x hx y hy hne
  obtain ⟨m, u, hu, rfl⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hy
  by_cases hmn : m = n
  · subst n
    have huv : u ≠ v := fun h => hne (congrArg (fun w => periodShift L m + w) h)
    simpa only [dist_add_left] using hs u hu.1 v hv.1 huv
  · exact guard_copies_distance hL hmn hu.2 hv.2

def guardedPeriodization {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    Configuration (Ambient d) where
  support := guardedPeriodizationSupport c L r
  finite_on_compacts _ hK := separated_inter_compact_finite hr
    (guardedPeriodization_separated c L r (by linarith) hs) hK

@[simp] theorem guardedPeriodization_support {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    (guardedPeriodization c L r hr hL hs).support = guardedPeriodizationSupport c L r := rfl

theorem count_guardedPeriodization {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y)
    (W : Set (Ambient d)) :
    (guardedPeriodization c L r hr hL hs).count W =
      ∑' m : Fin d → ℤ, c.count
        (guardInnerBox d L r ∩ ((fun x => periodShift L m + x) ⁻¹' W)) := by
  let S : (Fin d → ℤ) → Set (Ambient d) := fun m =>
    ((fun x => periodShift L m + x) '' (c.support ∩ guardInnerBox d L r)) ∩ W
  have hd : Pairwise (fun m n => Disjoint (S m) (S n)) := by
    intro m n hmn
    exact (guard_copies_disjoint c L r hr (by linarith) hmn).mono
      Set.inter_subset_left Set.inter_subset_left
  have hm : ∀ m, MeasurableSet (S m) := by
    intro m
    apply Set.Countable.measurableSet
    exact (((c.countable_support 0).mono Set.inter_subset_left).image
      (fun x => periodShift L m + x)).mono Set.inter_subset_left
  change Measure.count (guardedPeriodizationSupport c L r ∩ W) = _
  have he : guardedPeriodizationSupport c L r ∩ W = ⋃ m, S m := by
    simp only [guardedPeriodizationSupport, Set.iUnion_inter, S]
  rw [he, measure_iUnion hd hm]
  apply tsum_congr
  intro m
  change Measure.count (((fun x => periodShift L m + x) ''
    (c.support ∩ guardInnerBox d L r)) ∩ W) = _
  rw [← Set.image_inter_preimage]
  have hf : Function.Injective (fun x : Ambient d => periodShift L m + x) :=
    fun _ _ h => add_left_cancel h
  rw [Measure.count_injective_image hf]
  simp only [Configuration.count, Set.inter_assoc]

theorem count_guardedPeriodization_cell {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    (guardedPeriodization c L r hr hL hs).count (periodCell d L) =
      c.count (guardInnerBox d L r) := by
  exact congrArg Measure.count (guardedPeriodizationSupport_inter_cell c L r hr hL)

theorem measurable_guardedPeriodization_family {d : ℕ}
    {A : Type*} [MeasurableSpace A] (f : A → Configuration (Ambient d))
    (hf : Measurable f) (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ a, ∀ x ∈ (f a).support, ∀ y ∈ (f a).support, x ≠ y → r ≤ dist x y) :
    Measurable (fun a => guardedPeriodization (f a) L r hr hL (hs a)) := by
  apply Configuration.measurable_of_counts
  intro W hW
  simp_rw [count_guardedPeriodization]
  apply Measurable.tsum
  intro m
  exact (Configuration.measurable_count ((measurable_guardInnerBox d L r).inter
    (hW.preimage (continuous_const.add continuous_id).measurable))).comp hf

def guardedExpandedConfiguration {d : ℕ} (c : Configuration (Ambient d))
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1) :
    Configuration (Ambient d) :=
  guardedPeriodization (expandAfterDeletion c r t ht) L r hr hL
    (expandAfterDeletion_separated c r t ht)

theorem measurable_guardedExpandedConfiguration {d : ℕ}
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1) :
    Measurable (fun c : Configuration (Ambient d) =>
      guardedExpandedConfiguration c L r t hr hL ht) :=
  measurable_guardedPeriodization_family _ (measurable_expandAfterDeletion r t ht)
    L r hr hL (fun c => expandAfterDeletion_separated c r t ht)

theorem guardedExpandedConfiguration_separated {d : ℕ}
    (c : Configuration (Ambient d)) (L r t : ℝ)
    (hr : 0 < r) (hL : r < L) (ht : t < 1) :
    ∀ x ∈ (guardedExpandedConfiguration c L r t hr hL ht).support,
      ∀ y ∈ (guardedExpandedConfiguration c L r t hr hL ht).support,
        x ≠ y → r ≤ dist x y :=
  guardedPeriodization_separated _ L r (by linarith)
    (expandAfterDeletion_separated c r t ht)

def guardDensity {d : ℕ} (c : Configuration (Ambient d)) (L r : ℝ) : ℝ≥0∞ :=
  c.count (guardInnerBox d L r) / ENNReal.ofReal L ^ d

theorem measurable_guardDensity {d : ℕ} (L r : ℝ) :
    Measurable (fun c : Configuration (Ambient d) => guardDensity c L r) :=
  (Configuration.measurable_count (measurable_guardInnerBox d L r)).div_const _

theorem expected_guardDensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (L r : ℝ) :
    (∫⁻ c, guardDensity c L r ∂μ) =
      ρ * ENNReal.ofReal (L - r) ^ d / ENNReal.ofReal L ^ d := by
  simp only [guardDensity, div_eq_mul_inv]
  rw [lintegral_mul_const _ (Configuration.measurable_count (measurable_guardInnerBox d L r)),
    hρ _ (measurable_guardInnerBox d L r), volume_guardInnerBox]

theorem expected_guardDensity_normalized {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ)
    (L r : ℝ) (hr : 0 < r) (hL : r < L) :
    (∫⁻ c, guardDensity c L r ∂μ) =
      ρ * ENNReal.ofReal (((L - r) / L) ^ d) := by
  have hLp : 0 < L := hr.trans hL
  rw [expected_guardDensity μ ρ hρ, mul_div_assoc,
    ← ENNReal.ofReal_pow (sub_pos.mpr hL).le d,
    ← ENNReal.ofReal_pow hLp.le d,
    ← ENNReal.ofReal_div_of_pos (pow_pos hLp d), div_pow]

theorem guardedPeriodization_density {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    (guardedPeriodization c L r hr hL hs).count (periodCell d L) /
      volume (periodCell d L) = guardDensity c L r := by
  rw [count_guardedPeriodization_cell, volume_periodCell]
  rfl

theorem guardedPeriodization_periodic {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y)
    (n : Fin d → ℤ) :
    translate (periodShift L n) (guardedPeriodization c L r hr hL hs) =
      guardedPeriodization c L r hr hL hs := by
  apply Configuration.ext
  exact guardedPeriodizationSupport_periodic c L r n

theorem expected_expanded_guardDensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1) :
    (∫⁻ c, guardDensity (expandAfterDeletion c r t ht) L r ∂μ) =
      (retainedIntensity μ (r * (1 - t)) * ENNReal.ofReal ((1 - t) ^ d)) *
        ENNReal.ofReal (((L - r) / L) ^ d) := by
  rw [← lintegral_map (measurable_guardDensity L r) (measurable_expandAfterDeletion r t ht)]
  exact expected_guardDensity_normalized _ _
    (hasIntensity_expandAfterDeletion μ hμ ρ hρ hρtop r t ht) L r hr hL

theorem expected_guardedExpanded_density {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1) :
    (∫⁻ c, (guardedExpandedConfiguration c L r t hr hL ht).count (periodCell d L) /
        volume (periodCell d L) ∂μ) =
      (retainedIntensity μ (r * (1 - t)) * ENNReal.ofReal ((1 - t) ^ d)) *
        ENNReal.ofReal (((L - r) / L) ^ d) := by
  simp only [guardedExpandedConfiguration, guardedPeriodization_density]
  exact expected_expanded_guardDensity μ hμ ρ hρ hρtop L r t hr hL ht

theorem guardedPeriodization_restrict_inner {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y)
    (W : Set (Ambient d)) (hW : W ⊆ guardInnerBox d L r) :
    (guardedPeriodization c L r hr hL hs).restrict W = c.restrict W := by
  apply Configuration.ext
  ext z
  constructor
  · rintro ⟨hz, hzW⟩
    have hi := hW hzW
    have hq := (guard_shift_in_cell_iff L r hr hL 0 hi).mpr rfl
    simp only [periodShift_zero, zero_add] at hq
    have hh : z ∈ c.support ∩ guardInnerBox d L r := by
      rw [← guardedPeriodizationSupport_inter_cell c L r hr hL]
      exact ⟨hz, hq⟩
    exact ⟨hh.1, hzW⟩
  · rintro ⟨hz, hzW⟩
    refine ⟨Set.mem_iUnion.mpr ⟨0, z, ⟨hz, hW hzW⟩, by simp⟩, hzW⟩

def guardObservationCenters (d : ℕ) (L r R : ℝ) : Set (Ambient d) :=
  coordinateBox d (r / 2 + R) (L - r / 2 - R)

theorem measurable_guardObservationCenters (d : ℕ) (L r R : ℝ) :
    MeasurableSet (guardObservationCenters d L r R) := measurable_coordinateBox d _ _

theorem volume_guardObservationCenters (d : ℕ) (L r R : ℝ) :
    volume (guardObservationCenters d L r R) = ENNReal.ofReal (L - r - 2 * R) ^ d := by
  rw [guardObservationCenters, volume_coordinateBox]
  congr 2
  ring

theorem closedBall_subset_guardInnerBox {d : ℕ} (L r R : ℝ)
    {u : Ambient d} (hu : u ∈ guardObservationCenters d L r R) :
    Metric.closedBall u R ⊆ guardInnerBox d L r := by
  intro y hy i
  have hu' : r / 2 + R ≤ u i ∧ u i < L - r / 2 - R := hu i
  have hd : dist y u ≤ R := Metric.mem_closedBall.mp hy
  have hc : |y i - u i| ≤ R := by
    have hc' : |y i - u i| ≤ dist y u := by
      simpa only [Real.dist_eq] using (PiLp.dist_apply_le y u i)
    exact hc'.trans hd
  have hh := abs_le.mp hc
  constructor <;> linarith

theorem guardedPeriodization_restrict_ball {d : ℕ} (c : Configuration (Ambient d))
    (L r R : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y)
    {u : Ambient d} (hu : u ∈ guardObservationCenters d L r R) :
    (guardedPeriodization c L r hr hL hs).restrict (Metric.closedBall u R) =
      c.restrict (Metric.closedBall u R) :=
  guardedPeriodization_restrict_inner c L r hr hL hs _
    (closedBall_subset_guardInnerBox L r R hu)

theorem guardObservationCenters_subset_cell {d : ℕ} (L r R : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    guardObservationCenters d L r R ⊆ periodCell d L := by
  intro u hu i
  have hh : r / 2 + R ≤ u i ∧ u i < L - r / 2 - R := hu i
  constructor <;> linarith

theorem volume_guard_boundary {d : ℕ} (L r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    volume (periodCell d L \ guardObservationCenters d L r R) =
      ENNReal.ofReal L ^ d - ENNReal.ofReal (L - r - 2 * R) ^ d := by
  rw [measure_sdiff (guardObservationCenters_subset_cell L r R hr hR)
    (measurable_guardObservationCenters d L r R).nullMeasurableSet
    (by rw [volume_guardObservationCenters]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    volume_periodCell, volume_guardObservationCenters]

theorem count_coordinateBox_ne_top {d : ℕ} (c : Configuration (Ambient d)) (lo hi : ℝ) :
    c.count (coordinateBox d lo hi) ≠ ∞ := by
  let Q : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Icc lo hi)
  let K : Set (Ambient d) := (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Q
  have hQ : IsCompact Q := by
    have he : Q = {x : Fin d → ℝ | ∀ i, x i ∈ Icc lo hi} := by
      ext x
      change (∀ i ∈ (Set.univ : Set (Fin d)), x i ∈ Icc lo hi) ↔
        ∀ i, x i ∈ Icc lo hi
      constructor
      · intro h i
        exact h i (Set.mem_univ i)
      · intro h i _
        exact h i
    rw [he]
    exact isCompact_pi_infinite (fun _ : Fin d => isCompact_Icc)
  have hK : IsCompact K := (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr hQ
  apply ne_of_lt
  apply Measure.count_apply_lt_top.mpr
  apply (c.finite_on_compacts K hK).subset
  intro x hx
  refine ⟨hx.1, ?_⟩
  apply Set.mem_pi.mpr
  intro i _
  exact ⟨(hx.2 i).1, (hx.2 i).2.le⟩

theorem guardDensity_ne_top {d : ℕ} (c : Configuration (Ambient d))
    (L r : ℝ) (hL : 0 < L) : guardDensity c L r ≠ ∞ := by
  apply ENNReal.div_ne_top
  · exact count_coordinateBox_ne_top c _ _
  · exact ENNReal.pow_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hL)) _

theorem guard_boundary_fraction_le {d : ℕ} (L r R : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hL : 0 < L) (hw : r + 2 * R ≤ L) :
    volume (periodCell d L \ guardObservationCenters d L r R) /
      volume (periodCell d L) ≤ ENNReal.ofReal ((d : ℝ) * (r + 2 * R) / L) := by
  have hw0 : 0 ≤ L - r - 2 * R := by linarith
  have hb := contraction_power_lower_bound d
    (show (r + 2 * R) / L ≤ 1 from (div_le_one hL).mpr hw)
  rw [← mul_div_assoc] at hb
  have he : (L - r - 2 * R) / L = 1 - (r + 2 * R) / L := by
    field_simp
    ring
  have hreal : 1 - ((L - r - 2 * R) / L) ^ d ≤ (d : ℝ) * (r + 2 * R) / L := by
    rw [he]
    linarith
  rw [volume_guard_boundary L r R hr hR, volume_periodCell,
    ← ENNReal.ofReal_pow hL.le d, ← ENNReal.ofReal_pow hw0 d,
    ← ENNReal.ofReal_sub _ (pow_nonneg hw0 d),
    ← ENNReal.ofReal_div_of_pos (pow_pos hL d)]
  apply ENNReal.ofReal_le_ofReal
  have hd : (L ^ d - (L - r - 2 * R) ^ d) / L ^ d =
      1 - ((L - r - 2 * R) / L) ^ d := by
    rw [sub_div, div_self (ne_of_gt (pow_pos hL d)), div_pow]
  rwa [hd]

end E8Leech
