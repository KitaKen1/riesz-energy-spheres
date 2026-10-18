import E8Leech.CountingKernel
import E8Leech.GlobalDeletion
import E8Leech.Energy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Measurable close-neighbour counts, thinning and energy

The counting kernel carries each unlabelled configuration. Measurable parameterized counting
queries turn the existence of a close neighbour into the event that a count is nonzero.
The compact-window exhaustion supplies measurability without choosing point labels.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

def neighborWindow {d : ℕ} (x : Ambient d) (r : ℝ) : Set (Ambient d) :=
  {y | y ≠ x ∧ dist x y < r}

theorem measurable_neighborWindow {d : ℕ} (x : Ambient d) (r : ℝ) :
    MeasurableSet (neighborWindow x r) :=
  (measurableSet_eq_fun measurable_id measurable_const).compl.inter
    (measurableSet_lt (measurable_const.dist measurable_id) measurable_const)

def neighborCount {d : ℕ} (c : Configuration (Ambient d)) (x : Ambient d) (r : ℝ) : ℝ≥0∞ :=
  c.count (neighborWindow x r)

set_option maxHeartbeats 800000 in
theorem measurable_neighborCount {d : ℕ} (r : ℝ) :
    Measurable (fun p : Configuration (Ambient d) × Ambient d => neighborCount p.1 p.2 r) := by
  let T : Set ((Configuration (Ambient d) × Ambient d) × Ambient d) :=
    {p | p.2 ≠ p.1.2 ∧ dist p.1.2 p.2 < r}
  have hT : MeasurableSet T :=
    (measurableSet_eq_fun
      (f := fun p : (Configuration (Ambient d) × Ambient d) × Ambient d => p.2)
      (g := fun p => p.1.2) measurable_snd measurable_fst.snd).compl.inter
      (measurableSet_lt
        (f := fun p : (Configuration (Ambient d) × Ambient d) × Ambient d => dist p.1.2 p.2)
        (g := fun _ => r) (measurable_fst.snd.dist measurable_snd) measurable_const)
  have hm := measurable_count_query (d := d)
    (fun p : Configuration (Ambient d) × Ambient d => p.1) measurable_fst hT
  have heq : (fun p : Configuration (Ambient d) × Ambient d =>
      p.1.count (Prod.mk p ⁻¹' T)) = fun p => neighborCount p.1 p.2 r := rfl
  rwa [heq] at hm

theorem neighborCount_ne_zero_iff {d : ℕ} (c : Configuration (Ambient d))
    (x : Ambient d) (r : ℝ) :
    neighborCount c x r ≠ 0 ↔ ∃ y ∈ c.support, x ≠ y ∧ dist x y < r := by
  rw [neighborCount, ne_eq, Configuration.count_eq_zero_iff]
  change (c.support ∩ neighborWindow x r ≠ ∅) ↔ _
  rw [← Set.nonempty_iff_ne_empty]
  simp only [Set.nonempty_def, Set.mem_inter_iff, neighborWindow, Set.mem_ofPred_eq, ne_comm]

theorem badPoints_eq_neighborCount {d : ℕ} (c : Configuration (Ambient d)) (r : ℝ) :
    globalBadPoints c.support r = {x | x ∈ c.support ∧ neighborCount c x r ≠ 0} := by
  ext x
  exact and_congr_right fun _ => (neighborCount_ne_zero_iff c x r).symm

theorem measurable_deletedCount {d : ℕ} (r : ℝ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) :
    Measurable (fun c : Configuration (Ambient d) =>
      c.count (globalBadPoints c.support r ∩ W)) := by
  let T : Set (Configuration (Ambient d) × Ambient d) :=
    {p | neighborCount p.1 p.2 r ≠ 0 ∧ p.2 ∈ W}
  have hT : MeasurableSet T :=
    (measurableSet_eq_fun (measurable_neighborCount r) measurable_const).compl.inter
      (hW.preimage measurable_snd)
  have hm := measurable_count_query (d := d)
    (id : Configuration (Ambient d) → Configuration (Ambient d)) measurable_id hT
  change Measurable (fun c : Configuration (Ambient d) => c.count (Prod.mk c ⁻¹' T)) at hm
  have heq : (fun c : Configuration (Ambient d) => c.count (Prod.mk c ⁻¹' T)) =
      fun c => c.count (globalBadPoints c.support r ∩ W) := by
    ext c
    unfold Configuration.count
    congr 1
    rw [badPoints_eq_neighborCount]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, T, Set.mem_ofPred_eq]
    tauto
  rwa [heq] at hm

theorem measurable_retainedCount {d : ℕ} (r : ℝ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) :
    Measurable (fun c : Configuration (Ambient d) => (c.deleteClose r).count W) := by
  let T : Set (Configuration (Ambient d) × Ambient d) :=
    {p | neighborCount p.1 p.2 r = 0 ∧ p.2 ∈ W}
  have hT : MeasurableSet T :=
    (measurableSet_eq_fun (measurable_neighborCount r) measurable_const).inter
      (hW.preimage measurable_snd)
  have hm := measurable_count_query (d := d)
    (id : Configuration (Ambient d) → Configuration (Ambient d)) measurable_id hT
  change Measurable (fun c : Configuration (Ambient d) => c.count (Prod.mk c ⁻¹' T)) at hm
  have heq : (fun c : Configuration (Ambient d) => c.count (Prod.mk c ⁻¹' T)) =
      fun c => (c.deleteClose r).count W := by
    ext c
    unfold Configuration.count
    congr 1
    rw [Configuration.deleteClose_support, globalKeptPoints, badPoints_eq_neighborCount]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, T, Set.mem_ofPred_eq, Set.mem_sdiff]
    tauto
  rwa [heq] at hm

theorem measurable_deleteClose {d : ℕ} (r : ℝ) :
    Measurable (fun c : Configuration (Ambient d) => c.deleteClose r) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun c : Configuration (Ambient d) => c.deleteClose r)
    (⨆ W : {W : Set (Ambient d) // MeasurableSet W},
      MeasurableSpace.comap (fun c : Configuration (Ambient d) => c.count W.1) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun W => ?_
  rw [MeasurableSpace.comap_comp]
  exact (measurable_retainedCount r W.2).comap_le

theorem orderedWindowEnergy_eq_kernel {d : ℕ} (V : Ambient d → Ambient d → ℝ≥0∞)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy V c W = ∫⁻ x, if x ∈ W then
      ∫⁻ y, if y = x then 0 else V x y ∂countingKernel d c
      else 0 ∂countingKernel d c := by
  rw [countingKernel_lintegral_eq_tsum]
  unfold orderedWindowEnergy
  apply tsum_congr
  intro x
  split_ifs
  · rw [countingKernel_lintegral_eq_tsum]
    apply tsum_congr
    intro y
    split_ifs <;> rfl
  · rfl

theorem measurable_orderedWindowEnergy {d : ℕ}
    {V : Ambient d → Ambient d → ℝ≥0∞} (hV : Measurable (Function.uncurry V))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    Measurable (fun c : Configuration (Ambient d) => orderedWindowEnergy V c W) := by
  have hinner : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      ∫⁻ y, if y = p.2 then 0 else V p.2 y ∂countingKernel d p.1) := by
    apply measurable_countingKernel_lintegral_param (d := d)
      (f := fun p : (Configuration (Ambient d) × Ambient d) × Ambient d =>
        if p.2 = p.1.2 then 0 else V p.1.2 p.2)
      (fun p : Configuration (Ambient d) × Ambient d => p.1) measurable_fst
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_fst.snd)
      measurable_const (hV.comp (measurable_fst.snd.prodMk measurable_snd))
  simp_rw [orderedWindowEnergy_eq_kernel]
  apply measurable_countingKernel_lintegral (d := d)
    (f := fun p : Configuration (Ambient d) × Ambient d => if p.2 ∈ W then
      ∫⁻ y, if y = p.2 then 0 else V p.2 y ∂countingKernel d p.1 else 0)
  exact Measurable.ite (hW.preimage measurable_snd) hinner measurable_const

theorem measurable_rieszPotential {d : ℕ} (s : ℝ) :
    Measurable (Function.uncurry (rieszPotential (d := d) s)) :=
  ENNReal.continuous_rpow_const.measurable.comp
    (measurable_fst.dist measurable_snd).ennreal_ofReal

theorem measurable_unitWindow (d : ℕ) : MeasurableSet (unitWindow d) := by
  have heq : unitWindow d = ⋂ i : Fin d, {x : Ambient d | x i ∈ Set.Ico (0 : ℝ) 1} := by
    ext x
    simp [unitWindow]
  rw [heq]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage (by fun_prop)

theorem measurable_rieszWindowEnergy {d : ℕ} (s : ℝ) :
    Measurable (fun c : Configuration (Ambient d) =>
      orderedWindowEnergy (rieszPotential s) c (unitWindow d)) :=
  measurable_orderedWindowEnergy (measurable_rieszPotential s) (measurable_unitWindow d)

end E8Leech
