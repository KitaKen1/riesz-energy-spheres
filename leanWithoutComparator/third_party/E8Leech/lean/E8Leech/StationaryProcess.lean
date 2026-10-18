import E8Leech.Configuration
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Stationary simple point processes

The law lives on unlabelled, locally finite configurations. Stationarity means that every
deterministic translation preserves the law; ergodicity is not imposed. Intensity is an
identity of extended expectations on all Borel windows, including unbounded ones.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def translate {d : ℕ} (a : Ambient d) : Configuration (Ambient d) → Configuration (Ambient d) :=
  Configuration.mapHomeomorph (Homeomorph.addLeft a)

theorem measurable_translate {d : ℕ} (a : Ambient d) : Measurable (translate a) :=
  Configuration.measurable_mapHomeomorph _

@[simp] theorem count_translate {d : ℕ} (a : Ambient d)
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    (translate a c).count W = c.count ((fun x => a + x) ⁻¹' W) :=
  Configuration.count_mapHomeomorph _ _ _

def IsStationary {d : ℕ} (μ : Measure (Configuration (Ambient d))) : Prop :=
  ∀ a : Ambient d, MeasurePreserving (translate a) μ μ

def HasIntensity {d : ℕ} (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) : Prop :=
  ∀ W : Set (Ambient d), MeasurableSet W →
    (∫⁻ c, c.count W ∂μ) = ρ * volume W

/-- A probability law, with no ergodicity or hard-core hypothesis. -/
structure StationaryPointProcess (d : ℕ) where
  law : Measure (Configuration (Ambient d))
  probability : IsProbabilityMeasure law
  stationary : IsStationary law

theorem expected_count_translate {d : ℕ} (μ : Measure (Configuration (Ambient d)))
    (hμ : IsStationary μ) (a : Ambient d) {W : Set (Ambient d)}
    (hW : MeasurableSet W) :
    (∫⁻ c, c.count ((fun x => a + x) ⁻¹' W) ∂μ) = ∫⁻ c, c.count W ∂μ := by
  simpa only [count_translate] using
    (hμ a).lintegral_comp (Configuration.measurable_count hW)

end E8Leech
