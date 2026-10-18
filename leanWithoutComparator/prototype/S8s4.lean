import Mathlib

/-!
Planning prototype for spherical Riesz energy, d = 8 and s = 4.

The asymptotic statement below is a definition of the target proposition,
NOT a proof. Only the elementary lemmas and finite polynomial certificate
in this file are proved. No Gaussian sharpness or spherical transfer theorem
is assumed or claimed here.
-/

namespace RieszPrototype

abbrev Sphere8 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 9)) 1

/-- Embeddings rule out coincident particles. -/
abbrev Configuration (N : ℕ) := Fin N ↪ Sphere8

/-- Ordered pairs: each unordered pair contributes twice. -/
noncomputable def energy4 {N : ℕ} (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))⁻¹ ^ 4

theorem offDiagonal_dist_pos {N : ℕ} (X : Configuration N)
    {i j : Fin N} (hij : i ≠ j) : 0 < dist (X i) (X j) := by
  exact dist_pos.mpr (fun h => hij (X.injective h))

theorem energy4_nonneg {N : ℕ} (X : Configuration N) : 0 ≤ energy4 X := by
  unfold energy4
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

noncomputable def predictedCoefficient : ℝ := -5 * Real.sqrt 210 / 48

noncomputable def normalizedEnergy {N : ℕ} (X : Configuration N) : ℝ :=
  (energy4 X - (7 / 16 : ℝ) * (N : ℝ) ^ 2) /
    ((N : ℝ) * Real.sqrt (N : ℝ))

/-- A two-sided epsilon formulation avoids proving existence of minimizers first.
The existence quantifier is for every sufficiently large N, not a subsequence.
This target has NOT been proved.
-/
def S8s4Target : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N →
      (∀ X : Configuration N,
        predictedCoefficient - ε ≤ normalizedEnergy X) ∧
      (∃ X : Configuration N,
        normalizedEnergy X ≤ predictedCoefficient + ε)

/-- Polynomial specifying the proposed six-order boundary correction. -/
def boundaryPolynomial (x : ℚ) : ℚ :=
  39813120 * x ^ 4 - 316846080 * x ^ 3 + 842745600 * x ^ 2 -
    840595488 * x + 226287557

/-- Exact rational endpoint signs, not floating point root approximations.
Root existence, moment identities, and quadrature estimates are separate tasks.
-/
theorem boundaryPolynomial_sign_certificate :
    0 < boundaryPolynomial (418 / 1000) ∧
    boundaryPolynomial (419 / 1000) < 0 ∧
    boundaryPolynomial (1575 / 1000) < 0 ∧
    0 < boundaryPolynomial (1576 / 1000) ∧
    0 < boundaryPolynomial (2453 / 1000) ∧
    boundaryPolynomial (2454 / 1000) < 0 ∧
    boundaryPolynomial (3510 / 1000) < 0 ∧
    0 < boundaryPolynomial (3511 / 1000) := by
  norm_num [boundaryPolynomial]

/-- A normalization check for an ordered antipodal two-point configuration. -/
theorem antipodal_two_point_value : (2 : ℝ) * (2⁻¹) ^ 4 = 1 / 8 := by
  norm_num

#print axioms offDiagonal_dist_pos
#print axioms energy4_nonneg
#print axioms boundaryPolynomial_sign_certificate
#print axioms antipodal_two_point_value

end RieszPrototype
