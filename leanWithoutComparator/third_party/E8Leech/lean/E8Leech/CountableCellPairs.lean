import E8Leech.FinitePairForms

/-!
# A concrete countable partition for full-space pair integrals

Integer coordinate floors assign every endpoint to exactly one half-open unit
cell. Nonnegative counting sums commute without a signed Fubini assumption.
Stationarity and the already derived unit second moment then control the actual
full-space pair integral by a summable cell envelope. This does not construct
the envelope of a CKMRV auxiliary function or prove a stationary LP inequality.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

abbrev IntegerCellIndex (d : ℕ) := Fin d → ℤ

def integerCellIndex {d : ℕ} (x : Ambient d) : IntegerCellIndex d :=
  fun i => Int.floor (x i)

def integerCellShift {d : ℕ} (z : IntegerCellIndex d) : Ambient d :=
  WithLp.toLp 2 (fun i => -(z i : ℝ))

def integerCell {d : ℕ} (z : IntegerCellIndex d) : Set (Ambient d) :=
  (fun x => integerCellShift z + x) ⁻¹' unitWindow d

theorem measurableSet_integerCell {d : ℕ} (z : IntegerCellIndex d) :
    MeasurableSet (integerCell z) :=
  (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable

@[simp] theorem mem_integerCell_iff {d : ℕ} (x : Ambient d) (z : IntegerCellIndex d) :
    x ∈ integerCell z ↔ z = integerCellIndex x := by
  change (∀ i, -(z i : ℝ) + x i ∈ Ico (0 : ℝ) 1) ↔ z = (fun i => Int.floor (x i))
  constructor
  · intro h
    funext i
    exact (Int.floor_eq_iff.mpr ⟨by linarith [(h i).1], by linarith [(h i).2]⟩).symm
  · intro h
    subst z
    intro i
    exact ⟨by linarith [Int.floor_le (x i)], by linarith [Int.lt_floor_add_one (x i)]⟩

theorem integerCell_pairwise_disjoint {d : ℕ} :
    Pairwise (fun z w : IntegerCellIndex d => Disjoint (integerCell z) (integerCell w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hzw ((mem_integerCell_iff x z).mp hx |>.trans ((mem_integerCell_iff x w).mp hy).symm)

theorem iUnion_integerCell {d : ℕ} : (⋃ z : IntegerCellIndex d, integerCell z) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨integerCellIndex x, (mem_integerCell_iff x _).mpr rfl⟩

theorem integerCell_zero {d : ℕ} : integerCell (0 : IntegerCellIndex d) = unitWindow d := by
  have hzero : integerCellShift (0 : IntegerCellIndex d) = 0 := by
    ext i
    simp [integerCellShift]
  ext x
  simp [integerCell, hzero]

theorem tsum_integerCell_indicator {d : ℕ} (x : Ambient d) (v : ℝ≥0∞) :
    (∑' z : IntegerCellIndex d, if x ∈ integerCell z then v else 0) = v := by
  simp only [mem_integerCell_iff, tsum_ite_eq]

/-- The exact partition identity does not require measurability of the kernel:
it is first proved as an identity of nonnegative counting sums. -/
theorem localizedPairIntegral_eq_integerCell_sum {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W U : Set (Ambient d)) :
    localizedPairIntegral V c W U =
      ∑' z : IntegerCellIndex d, localizedPairIntegral V c W (U ∩ integerCell z) := by
  simp only [localizedPairIntegral_eq_tsum]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) ∈ U
    · simpa only [mem_inter_iff, hy, true_and, if_true] using
        (tsum_integerCell_indicator (y : Ambient d) (V x y)).symm
    · simp [hy]
  · simp [hx]

theorem localizedPairIntegral_univ_eq_integerCell_sum {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W : Set (Ambient d)) :
    localizedPairIntegral V c W univ =
      ∑' z : IntegerCellIndex d, localizedPairIntegral V c W (integerCell z) := by
  simpa only [univ_inter] using localizedPairIntegral_eq_integerCell_sum V c W univ

/-- Tonelli for the concrete full-space decomposition, before subtracting
positive and negative parts. -/
theorem expected_pair_univ_eq_integerCell_sum {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, localizedPairIntegral V c W univ ∂μ) =
      ∑' z : IntegerCellIndex d, ∫⁻ c, localizedPairIntegral V c W (integerCell z) ∂μ := by
  simp only [localizedPairIntegral_univ_eq_integerCell_sum]
  exact lintegral_tsum (fun z =>
    (measurable_localizedPairIntegral hV hW (measurableSet_integerCell z)).aemeasurable)

theorem expected_pair_univ_le_cell_envelope {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z) :
    (∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ) ≤
      (∑' z, M z) * (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) := by
  rw [expected_pair_univ_eq_integerCell_sum μ V hV (W := (fun x => a + x) ⁻¹' unitWindow d)
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)]
  calc
    _ ≤ ∑' z, M z * (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) :=
      ENNReal.tsum_le_tsum fun z =>
        expected_localizedPairIntegral_unit_cells_le μ hμ V a (integerCellShift z) (M z) (hbound z)
    _ = _ := ENNReal.tsum_mul_right

theorem expected_pair_univ_ne_top_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞) (hM : (∑' z, M z) ≠ ∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z) :
    (∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d) univ ∂μ) ≠ ∞ := by
  exact ne_of_lt ((expected_pair_univ_le_cell_envelope μ hμ V hV a M hbound).trans_lt
    (ENNReal.mul_ne_top hM (ENNReal.mul_ne_top (by simp)
      (expected_unit_count_sq_ne_top_of_riesz hs μ ρ hρ hρtop henergy))).lt_top)

theorem pair_univ_ae_ne_top_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞) (hM : (∑' z, M z) ≠ ∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z) :
    ∀ᵐ c ∂μ, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d) univ ≠ ∞ := by
  exact (ae_lt_top (measurable_localizedPairIntegral hV
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)
    MeasurableSet.univ) (expected_pair_univ_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy
      V hV a M hM hbound)).mono (fun _ h => h.ne)

/-- The omitted cells of a finite computation, as an actual endpoint window. -/
def integerCellTail {d : ℕ} (F : Finset (IntegerCellIndex d)) : Set (Ambient d) :=
  (⋃ z ∈ F, integerCell z)ᶜ

@[simp] theorem mem_integerCellTail_iff {d : ℕ}
    (F : Finset (IntegerCellIndex d)) (y : Ambient d) :
    y ∈ integerCellTail F ↔ integerCellIndex y ∉ F := by
  simp [integerCellTail, mem_integerCell_iff]

theorem measurableSet_integerCellTail {d : ℕ} (F : Finset (IntegerCellIndex d)) :
    MeasurableSet (integerCellTail F) := by
  exact (MeasurableSet.iUnion fun z =>
    MeasurableSet.iUnion fun (_ : z ∈ F) => measurableSet_integerCell z).compl

theorem integerCellTail_inter {d : ℕ} (F : Finset (IntegerCellIndex d))
    (z : IntegerCellIndex d) :
    integerCellTail F ∩ integerCell z = if z ∈ F then ∅ else integerCell z := by
  ext y
  by_cases hy : y ∈ integerCell z
  · have hz : z = integerCellIndex y := (mem_integerCell_iff y z).mp hy
    simp [hy, ← hz]
  · simp [hy]

theorem localizedPairIntegral_empty_right {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W : Set (Ambient d)) : localizedPairIntegral V c W ∅ = 0 := by
  simp [localizedPairIntegral]

theorem pair_tail_eq_cell_sum {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (F : Finset (IntegerCellIndex d)) :
    localizedPairIntegral V c W (integerCellTail F) =
      ∑' z : {z : IntegerCellIndex d // z ∉ F}, localizedPairIntegral V c W (integerCell z.val) := by
  rw [localizedPairIntegral_eq_integerCell_sum]
  calc
    _ = ∑' z : IntegerCellIndex d, {z : IntegerCellIndex d | z ∉ F}.indicator
        (fun z => localizedPairIntegral V c W (integerCell z)) z := by
      apply tsum_congr
      intro z
      rw [integerCellTail_inter]
      by_cases hz : z ∈ F <;> simp [hz, localizedPairIntegral_empty_right]
    _ = _ := (tsum_subtype {z : IntegerCellIndex d | z ∉ F}
      (fun z => localizedPairIntegral V c W (integerCell z))).symm

/-- A finite cell computation and its omitted endpoint integral exhaust the
original quantity, including its diagonal and even when it is infinite. -/
theorem finite_cell_sum_add_pair_tail {d : ℕ}
    (V : Ambient d → Ambient d → ℝ≥0∞) (c : Configuration (Ambient d))
    (W : Set (Ambient d)) (F : Finset (IntegerCellIndex d)) :
    (∑ z ∈ F, localizedPairIntegral V c W (integerCell z)) +
      localizedPairIntegral V c W (integerCellTail F) = localizedPairIntegral V c W univ := by
  rw [pair_tail_eq_cell_sum, localizedPairIntegral_univ_eq_integerCell_sum]
  exact ENNReal.sum_add_tsum_compl F _

theorem expected_pair_tail_eq_cell_sum {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (F : Finset (IntegerCellIndex d)) :
    (∫⁻ c, localizedPairIntegral V c W (integerCellTail F) ∂μ) =
      ∑' z : {z : IntegerCellIndex d // z ∉ F},
        ∫⁻ c, localizedPairIntegral V c W (integerCell z.val) ∂μ := by
  simp only [pair_tail_eq_cell_sum]
  exact lintegral_tsum
    (f := fun (z : {z : IntegerCellIndex d // z ∉ F}) (c : Configuration (Ambient d)) =>
      localizedPairIntegral V c W (integerCell z.val))
    (fun z => (measurable_localizedPairIntegral hV hW
      (measurableSet_integerCell z.val)).aemeasurable)

theorem expected_pair_tail_le_cell_envelope {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z) (F : Finset (IntegerCellIndex d)) :
    (∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d)
      (integerCellTail F) ∂μ) ≤
      (∑' z : {z : IntegerCellIndex d // z ∉ F}, M z.val) *
        (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) := by
  rw [expected_pair_tail_eq_cell_sum μ V hV (W := (fun x => a + x) ⁻¹' unitWindow d)
    ((measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable)]
  calc
    _ ≤ ∑' z : {z : IntegerCellIndex d // z ∉ F},
        M z.val * (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) :=
      ENNReal.tsum_le_tsum fun z =>
        expected_localizedPairIntegral_unit_cells_le μ hμ V a (integerCellShift z.val) (M z.val) (hbound z.val)
    _ = _ := ENNReal.tsum_mul_right

theorem tendsto_expected_pair_tail_zero_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞) (hM : (∑' z, M z) ≠ ∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z) :
    Filter.Tendsto (fun F : Finset (IntegerCellIndex d) =>
      ∫⁻ c, localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d)
        (integerCellTail F) ∂μ) Filter.atTop (nhds 0) := by
  have hK : (2 * ∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp)
      (expected_unit_count_sq_ne_top_of_riesz hs μ ρ hρ hρtop henergy)
  have ht := (ENNReal.continuous_mul_const hK).tendsto 0 |>.comp
    (ENNReal.tendsto_tsum_compl_atTop_zero hM)
  simp only [zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) (expected_pair_tail_le_cell_envelope μ hμ V hV a M hbound)

theorem pair_tail_ae_tendsto_zero_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞) (hV : Measurable (Function.uncurry V))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ≥0∞) (hM : (∑' z, M z) ≠ ∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, V x y ≤ M z) :
    ∀ᵐ c ∂μ, Filter.Tendsto (fun F : Finset (IntegerCellIndex d) =>
      localizedPairIntegral V c ((fun x => a + x) ⁻¹' unitWindow d) (integerCellTail F))
      Filter.atTop (nhds 0) := by
  filter_upwards [pair_univ_ae_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy V hV a M hM hbound]
    with c hc
  rw [localizedPairIntegral_univ_eq_integerCell_sum] at hc
  simpa only [pair_tail_eq_cell_sum] using ENNReal.tendsto_tsum_compl_atTop_zero hc

/-- Summable absolute envelopes make both full-space Jordan parts integrable.
No absolute convergence is hidden in a real-valued infinite-sum convention. -/
theorem integrable_signed_pair_univ_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞)
    (H : Ambient d → Ambient d → ℝ) (hH : Measurable (Function.uncurry H))
    (a : Ambient d) (M : IntegerCellIndex d → ℝ)
    (hM : (∑' z, ENNReal.ofReal (M z)) ≠ ∞)
    (hbound : ∀ z, ∀ x ∈ (fun x => a + x) ⁻¹' unitWindow d,
      ∀ y ∈ integerCell z, |H x y| ≤ M z) :
    Integrable (fun c => signedLocalizedPairIntegral H c
      ((fun x => a + x) ⁻¹' unitWindow d) univ) μ := by
  have hW : MeasurableSet ((fun x => a + x) ⁻¹' unitWindow d) :=
    (measurable_unitWindow d).preimage (continuous_const.add continuous_id).measurable
  have hp := expected_pair_univ_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy
    (fun x y => ENNReal.ofReal (H x y)) hH.ennreal_ofReal a
    (fun z => ENNReal.ofReal (M z)) hM
    (fun z x hx y hy => ENNReal.ofReal_le_ofReal
      ((le_abs_self (H x y)).trans (hbound z x hx y hy)))
  have hn := expected_pair_univ_ne_top_of_riesz hs μ hμ ρ hρ hρtop henergy
    (fun x y => ENNReal.ofReal (-H x y)) hH.neg.ennreal_ofReal a
    (fun z => ENNReal.ofReal (M z)) hM
    (fun z x hx y hy => ENNReal.ofReal_le_ofReal
      ((neg_le_abs (H x y)).trans (hbound z x hx y hy)))
  exact (integrable_toReal_of_lintegral_ne_top
    (measurable_localizedPairIntegral (V := fun x y => ENNReal.ofReal (H x y))
      hH.ennreal_ofReal hW MeasurableSet.univ).aemeasurable hp).sub
    (integrable_toReal_of_lintegral_ne_top
      (measurable_localizedPairIntegral (V := fun x y => ENNReal.ofReal (-H x y))
        hH.neg.ennreal_ofReal hW MeasurableSet.univ).aemeasurable hn)

end E8Leech
