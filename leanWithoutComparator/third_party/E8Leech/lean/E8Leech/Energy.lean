import E8Leech.StationaryProcess
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Ordered energy with extended nonnegative values

The outer point is anchored in the window, and the inner point ranges over the entire
configuration. The diagonal is excluded. No factor `1/2` is inserted. `ENNReal` sums preserve
divergence as infinity; a finite-energy hypothesis is needed before taking real excesses.
Measurability of the energy as a function of configurations is proved in Measurability.lean.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def orderedWindowEnergy {X : Type*} [TopologicalSpace X]
    (V : X → X → ℝ≥0∞) (c : Configuration X) (W : Set X) : ℝ≥0∞ :=
  ∑' x : c.support, if (x : X) ∈ W then
    ∑' y : c.support, if (y : X) = (x : X) then 0 else V x y
    else 0

def rieszPotential {d : ℕ} (s : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (dist x y) ^ (-s)

def unitWindow (d : ℕ) : Set (Ambient d) :=
  {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

def rieszEnergy {d : ℕ} (s : ℝ) (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ c, orderedWindowEnergy (rieszPotential s) c (unitWindow d) ∂μ

/-- Use an upper bound in extended values, without subtracting two infinite real energies. -/
def HasRieszExcessAtMost {d : ℕ} (s : ℝ)
    (μ : Measure (Configuration (Ambient d))) (latticeEnergy δ : ℝ≥0∞) : Prop :=
  latticeEnergy ≠ ∞ ∧ rieszEnergy s μ ≤ latticeEnergy + δ

theorem orderedWindowEnergy_empty {X : Type*} [TopologicalSpace X]
    (V : X → X → ℝ≥0∞) (c : Configuration X) :
    orderedWindowEnergy V c ∅ = 0 := by
  simp [orderedWindowEnergy]

theorem orderedWindowEnergy_mono_potential {X : Type*} [TopologicalSpace X]
    {V U : X → X → ℝ≥0∞} (hVU : ∀ x y, V x y ≤ U x y)
    (c : Configuration X) (W : Set X) :
    orderedWindowEnergy V c W ≤ orderedWindowEnergy U c W := by
  unfold orderedWindowEnergy
  apply ENNReal.tsum_le_tsum
  intro x
  split_ifs
  · apply ENNReal.tsum_le_tsum
    intro y
    split_ifs
    · exact le_rfl
    · exact hVU x y
  · exact le_rfl

end E8Leech
