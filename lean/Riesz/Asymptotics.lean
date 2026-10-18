import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
The infimum formulation needs approximate competitors, not existence of a minimizer.
This generic assembly lemma does not prove the spherical energy estimates.
-/

set_option autoImplicit false

noncomputable section
namespace SphericalRiesz

def TwoSidedTarget {α : ℕ → Type*} (f : ∀ n, α n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (∀ x, c - ε ≤ f n x) ∧ (∃ x, f n x ≤ c + ε)

def InfimumTarget {α : ℕ → Type*} (f : ∀ n, α n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    c - ε ≤ sInf (Set.range (f n)) ∧ sInf (Set.range (f n)) ≤ c + ε

/-- An epsilon characterization of the infimum, avoiding minimizer compactness. -/
theorem twoSidedTarget_iff_infimumTarget {α : ℕ → Type*}
    (f : ∀ n, α n → ℝ) (c : ℝ)
    (hne : ∀ n, (Set.range (f n)).Nonempty)
    (hbounded : ∀ n, BddBelow (Set.range (f n))) :
    TwoSidedTarget f c ↔ InfimumTarget f c := by
  constructor
  · intro h ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨hl, x, hx⟩ := hn₀ n hn
    constructor
    · apply le_csInf (hne n)
      rintro _ ⟨y, rfl⟩
      exact hl y
    · exact (csInf_le (hbounded n) (Set.mem_range_self x)).trans hx
  · intro h ε hε
    obtain ⟨n₀, hn₀⟩ := h (ε/2) (by linarith)
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨hl, hu⟩ := hn₀ n hn
    constructor
    · intro x
      have hx := csInf_le (hbounded n) (Set.mem_range_self x)
      linarith
    · have hlt : sInf (Set.range (f n)) < c + ε := by linarith
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_csInf_lt (hne n) hlt
      exact ⟨x, hx.le⟩

#print axioms twoSidedTarget_iff_infimumTarget

end SphericalRiesz
