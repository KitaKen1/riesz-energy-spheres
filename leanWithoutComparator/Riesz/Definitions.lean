import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Target normalization: unit sphere, chordal distance, and ordered pairs. -/

set_option autoImplicit false

noncomputable section
namespace SphericalRiesz

abbrev Sphere8 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 9)) 1
abbrev Configuration (N : ℕ) := Fin N ↪ Sphere8

def energy4 {N : ℕ} (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))⁻¹ ^ 4

theorem offDiagonal_dist_pos {N : ℕ} (X : Configuration N)
    {i j : Fin N} (hij : i ≠ j) : 0 < dist (X i) (X j) :=
  dist_pos.mpr (fun h => hij (X.injective h))

theorem energy4_nonneg {N : ℕ} (X : Configuration N) : 0 ≤ energy4 X := by
  unfold energy4
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

def predictedCoefficient : ℝ := -5 * Real.sqrt 210 / 48

def normalizedEnergy {N : ℕ} (X : Configuration N) : ℝ :=
  (energy4 X - (7/16 : ℝ) * (N : ℝ)^2) / ((N : ℝ) * Real.sqrt N)

/-- Unproved main goal. All sufficiently large integers N occur in the quantifier. -/
def S8s4Target : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    (∀ X : Configuration N, predictedCoefficient - ε ≤ normalizedEnergy X) ∧
    (∃ X : Configuration N, normalizedEnergy X ≤ predictedCoefficient + ε)

#print axioms offDiagonal_dist_pos
#print axioms energy4_nonneg

end SphericalRiesz
