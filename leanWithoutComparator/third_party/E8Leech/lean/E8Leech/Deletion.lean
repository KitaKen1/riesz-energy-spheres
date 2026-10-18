import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-!
Finite deletion and scalar estimates for the stationary crystallization project.
These lemmas do not establish the stationary energy or packing stability inputs.
-/

namespace E8Leech

open Finset

section Deletion

variable {X : Type*} [DecidableEq X] [PseudoMetricSpace X]

/-- Ordered close pairs in a finite configuration. -/
noncomputable def closePairs (s : Finset X) (r : ℝ) : Finset (X × X) := by
  classical
  exact (s ×ˢ s).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 < r)

/-- Delete every point which participates in a close pair. -/
noncomputable def badPoints (s : Finset X) (r : ℝ) : Finset X :=
  (closePairs s r).image Prod.fst

noncomputable def keptPoints (s : Finset X) (r : ℝ) : Finset X :=
  s \ badPoints s r

theorem badPoints_card_le (s : Finset X) (r : ℝ) :
    (badPoints s r).card ≤ (closePairs s r).card :=
  Finset.card_image_le

theorem keptPoints_separated (s : Finset X) (r : ℝ)
    {x y : X} (hx : x ∈ keptPoints s r) (hy : y ∈ keptPoints s r)
    (hne : x ≠ y) : r ≤ dist x y := by
  classical
  obtain ⟨hxs, hxb⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hys, _⟩ := Finset.mem_sdiff.mp hy
  by_contra h
  apply hxb
  apply Finset.mem_image.mpr
  refine ⟨(x, y), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxs, hys⟩, hne, lt_of_not_ge h⟩

end Deletion

/-- Choose the cutoff first and bound the energy excess by its cube. -/
theorem balance_loss {δ t : ℝ} (ht : 0 < t) (hδ : δ ≤ t ^ 3) :
    t + δ / t ^ 2 ≤ 2 * t := by
  have h : δ / t ^ 2 ≤ t := (div_le_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith)
  linarith

/-- Intensity of deleted points after the same parameter choice. -/
theorem deletion_loss {δ t C q : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (hδ : δ ≤ t ^ 3) (hq : q ≤ C * (δ / t ^ 2)) : q ≤ C * t := by
  have h : δ / t ^ 2 ≤ t := (div_le_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith)
  exact hq.trans (mul_le_mul_of_nonneg_left h hC)

/-- Strict exponent budget reserved for the logarithmic losses in BRR. -/
theorem exponent_budget :
    (1 / 13 : ℚ) < (25 / 26 : ℚ) / 12 ∧
    (25 / 26 : ℚ) / 12 - 1 / 13 = 1 / 312 := by
  norm_num

/-- For the later all-γ extension, give Lean an explicit interior exponent. -/
theorem general_exponent_budget {γ : ℝ} (hγ : 0 < γ) (hlt : γ < 1 / 12) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 0 < a / 12 - γ := by
  refine ⟨(1 + 12 * γ) / 2, ?_, ?_, ?_⟩ <;> linarith

#print axioms badPoints_card_le
#print axioms keptPoints_separated
#print axioms balance_loss
#print axioms deletion_loss
#print axioms exponent_budget
#print axioms general_exponent_budget

end E8Leech
