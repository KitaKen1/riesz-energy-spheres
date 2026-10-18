import E8Leech.Energy
import E8Leech.E8Coordinates
import E8Leech.LeechCoordinates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Isometry

/-!
# The quantitative target as a proposition, not a proved theorem

The constants are chosen before the process law and the excess parameter. Both directions of
the finite-window matching condition use ALL original points, including points later deleted
in intermediate constructions. A measurable good subevent is required: a large outer measure
of a potentially nonmeasurable existential event would not establish the requested probability.

`e8CrystallizationTarget` is a concrete definition. This file asserts no crystallization theorem,
and it is not yet an FC-ready submission. Energy and thinning measurability and unit-window
volume are proved in the supporting modules. E8Lattice and LatticeEnergy also prove the E8
integer-span identification, covolume one, and finite lattice energy for s > 8. LeechGeometry
and LeechLattice prove minimum distance two, local finiteness, full rank and finite lattice
energy for s > 24. LeechBasis proves the integer-span identification and covolume one.
The complete statement/model audit and the crystallization proof remain work items.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def observationRadius (δ : ℝ) : ℝ :=
  Real.log (1 / δ) / Real.log (Real.log (1 / δ))

def latticeRieszEnergy {d : ℕ} (Λ : Set (Ambient d)) (s : ℝ) : ℝ≥0∞ :=
  ∑' y : Λ, if (y : Ambient d) = 0 then 0 else rieszPotential s 0 (y : Ambient d)

def LocalCrystal {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) (R error loss : ℝ) : Prop :=
  (∃ Φ : Ambient d ≃ᵢ Ambient d, ∃ Z : Finset (Ambient d),
    (↑Z : Set (Ambient d)) ⊆ Λ ∧
    (∀ x ∈ c.support ∩ Metric.closedBall 0 R, ∃ z ∈ Z, dist x (Φ z) ≤ error) ∧
    (∀ z ∈ Z, ∃ x ∈ c.support ∩ Metric.closedBall 0 R, dist (Φ z) x ≤ error)) ∧
  ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
    c.count (Metric.closedBall 0 R)

def StationaryCrystallizationFor {d : ℕ} (Λ : Set (Ambient d)) : Prop :=
  ∀ s : ℝ, (d : ℝ) < s →
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient d)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          HasRieszExcessAtMost s μ (latticeRieszEnergy Λ s) (ENNReal.ofReal δ) →
          ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal Λ c (observationRadius δ)
              (C * δ ^ (1 / 13 : ℝ)) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G

def e8CrystallizationTarget : Prop := StationaryCrystallizationFor e8Set

def leechCrystallizationTarget : Prop := StationaryCrystallizationFor leechSet

def e8LeechCrystallizationTarget : Prop := e8CrystallizationTarget ∧ leechCrystallizationTarget

end E8Leech
