import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
A finite partition of cutoff squares, with its actual normalization.
The correlation upper bound follows from a sum of squared differences.
These identities are independent of the sphere dimension and do not assume
any positivity certificate for the kernel to be localized later.
-/

set_option autoImplicit false
noncomputable section
open Finset
namespace SphericalRiesz

variable {S : Type*} {K : ℕ}

def finiteCutoffSquareMass (φ : Fin K → S → ℝ) (x : S) : ℝ :=
  ∑ i, (φ i x)^2

def finiteCutoffSquarePartition (φ : Fin K → S → ℝ) (i : Fin K) (x : S) : ℝ :=
  φ i x / Real.sqrt (finiteCutoffSquareMass φ x)

theorem finiteCutoffSquareMass_nonneg (φ : Fin K → S → ℝ) (x : S) :
    0 ≤ finiteCutoffSquareMass φ x :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem finiteCutoffSquareMass_pos_of_cover (φ : Fin K → S → ℝ)
    (hcover : ∀ x, ∃ i, 0 < φ i x) (x : S) : 0 < finiteCutoffSquareMass φ x := by
  obtain ⟨i,hi⟩ := hcover x
  exact (sq_pos_of_pos hi).trans_le
    (single_le_sum (fun j _ => sq_nonneg (φ j x)) (mem_univ i))

theorem finiteCutoffSquareMass_continuous [TopologicalSpace S] (φ : Fin K → S → ℝ)
    (hφ : ∀ i, Continuous (φ i)) : Continuous (finiteCutoffSquareMass φ) := by
  unfold finiteCutoffSquareMass
  exact continuous_finsetSum _ (fun i _ => (hφ i).pow 2)

theorem finiteCutoffSquarePartition_nonneg (φ : Fin K → S → ℝ)
    (hφ : ∀ i x, 0 ≤ φ i x) (i : Fin K) (x : S) :
    0 ≤ finiteCutoffSquarePartition φ i x :=
  div_nonneg (hφ i x) (Real.sqrt_nonneg _)

theorem finiteCutoffSquarePartition_le_one (φ : Fin K → S → ℝ)
    (hpos : ∀ x, 0 < finiteCutoffSquareMass φ x)
    (i : Fin K) (x : S) : finiteCutoffSquarePartition φ i x ≤ 1 := by
  have hs := Real.sqrt_pos.mpr (hpos x)
  apply (div_le_one hs).mpr
  have hi : (φ i x)^2 ≤ finiteCutoffSquareMass φ x :=
    single_le_sum (fun j _ => sq_nonneg (φ j x)) (mem_univ i)
  have he := Real.sq_sqrt (hpos x).le
  nlinarith

theorem finiteCutoffSquarePartition_continuous [TopologicalSpace S]
    (φ : Fin K → S → ℝ) (hφ : ∀ i, Continuous (φ i))
    (hpos : ∀ x, 0 < finiteCutoffSquareMass φ x) (i : Fin K) :
    Continuous (finiteCutoffSquarePartition φ i) :=
  (hφ i).div (finiteCutoffSquareMass_continuous φ hφ).sqrt
    (fun x => (Real.sqrt_pos.mpr (hpos x)).ne')

theorem finiteCutoffSquarePartition_sum_square (φ : Fin K → S → ℝ)
    (hpos : ∀ x, 0 < finiteCutoffSquareMass φ x) (x : S) :
    (∑ i, (finiteCutoffSquarePartition φ i x)^2) = 1 := by
  simp only [finiteCutoffSquarePartition, div_pow]
  rw [← sum_div, Real.sq_sqrt (hpos x).le]
  exact div_self (hpos x).ne'

theorem finiteCutoffSquarePartition_ne_zero_iff (φ : Fin K → S → ℝ)
    (hpos : ∀ x, 0 < finiteCutoffSquareMass φ x) (i : Fin K) (x : S) :
    finiteCutoffSquarePartition φ i x ≠ 0 ↔ φ i x ≠ 0 := by
  constructor
  · intro h
    exact (div_ne_zero_iff.mp h).1
  · intro h
    exact div_ne_zero h (Real.sqrt_pos.mpr (hpos x)).ne'

theorem finiteCutoffSquarePartition_correlation_nonneg (φ : Fin K → S → ℝ)
    (hφ : ∀ i x, 0 ≤ φ i x) (x y : S) :
    0 ≤ ∑ i, finiteCutoffSquarePartition φ i x*finiteCutoffSquarePartition φ i y :=
  sum_nonneg (fun i _ => mul_nonneg
    (finiteCutoffSquarePartition_nonneg φ hφ i x)
    (finiteCutoffSquarePartition_nonneg φ hφ i y))

theorem finiteCutoffSquarePartition_correlation_le_one (φ : Fin K → S → ℝ)
    (hpos : ∀ x, 0 < finiteCutoffSquareMass φ x) (x y : S) :
    (∑ i, finiteCutoffSquarePartition φ i x*finiteCutoffSquarePartition φ i y) ≤ 1 := by
  have h : 0 ≤ ∑ i, (finiteCutoffSquarePartition φ i x-
      finiteCutoffSquarePartition φ i y)^2 := sum_nonneg (fun i _ => sq_nonneg _)
  have he : (∑ i, (finiteCutoffSquarePartition φ i x-
      finiteCutoffSquarePartition φ i y)^2) =
      (∑ i, (finiteCutoffSquarePartition φ i x)^2)+
      (∑ i, (finiteCutoffSquarePartition φ i y)^2)-
      2*(∑ i, finiteCutoffSquarePartition φ i x*finiteCutoffSquarePartition φ i y) := by
    calc
      _ = ∑ i, ((finiteCutoffSquarePartition φ i x)^2+
          (finiteCutoffSquarePartition φ i y)^2-
          2*(finiteCutoffSquarePartition φ i x*finiteCutoffSquarePartition φ i y)) :=
        sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [sum_sub_distrib, sum_add_distrib, mul_sum]
  rw [he, finiteCutoffSquarePartition_sum_square φ hpos x,
    finiteCutoffSquarePartition_sum_square φ hpos y] at h
  linarith

end SphericalRiesz
