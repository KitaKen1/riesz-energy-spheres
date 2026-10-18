import Riesz.CompactGrid8
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact coordinate volumes and strict gaps for the known shrink factor.
Original half-open cells partition without boundary overlaps; shrunk closed
cells are compact, disjoint, and retain the exact factor (1-gamma)^8. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

def gridShrunkCell8 (h γ : ℝ) (z : Fin 8 → ℤ) : Set (Fin 8 → ℝ) :=
  {x | ∀ i, h*((z i : ℝ)+γ/2) ≤ x i ∧ x i ≤ h*((z i : ℝ)+1-γ/2)}

theorem gridHalfOpenCell8_measurable (h : ℝ) (z : Fin 8 → ℤ) :
    MeasurableSet (gridHalfOpenCell8 h z) := by
  have he : gridHalfOpenCell8 h z =
      Set.pi univ (fun i => Ico (h*(z i : ℝ)) (h*((z i : ℝ)+1))) := by
    ext x
    simp [gridHalfOpenCell8, Set.mem_pi]
  rw [he]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem gridClosedCell8_isCompact (h : ℝ) (z : Fin 8 → ℤ) :
    IsCompact (gridClosedCell8 h z) := by
  have he : gridClosedCell8 h z =
      Icc (fun i => h*(z i : ℝ)) (fun i => h*((z i : ℝ)+1)) := by
    ext x
    simp only [gridClosedCell8, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

theorem gridShrunkCell8_isCompact (h γ : ℝ) (z : Fin 8 → ℤ) :
    IsCompact (gridShrunkCell8 h γ z) := by
  have he : gridShrunkCell8 h γ z =
      Icc (fun i => h*((z i : ℝ)+γ/2)) (fun i => h*((z i : ℝ)+1-γ/2)) := by
    ext x
    simp only [gridShrunkCell8, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

theorem gridShrunkCell8_subset_halfOpen (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ)
    (z : Fin 8 → ℤ) : gridShrunkCell8 h γ z ⊆ gridHalfOpenCell8 h z := by
  intro x hx i
  have hi := hx i
  have hp : 0 < h*γ := mul_pos hh hγ
  constructor <;> nlinarith

theorem gridShrunkCell8_pairwise_disjoint (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) :
    Pairwise (fun z w : Fin 8 → ℤ => Disjoint (gridShrunkCell8 h γ z) (gridShrunkCell8 h γ w)) := by
  intro z w hzw
  exact (gridHalfOpenCell8_pairwise_disjoint h hh hzw).mono
    (gridShrunkCell8_subset_halfOpen h γ hh hγ z)
    (gridShrunkCell8_subset_halfOpen h γ hh hγ w)

theorem gridHalfOpenCell8_volume (h : ℝ) (hh : 0 ≤ h) (z : Fin 8 → ℤ) :
    volume (gridHalfOpenCell8 h z) = ENNReal.ofReal (h^8) := by
  have he : gridHalfOpenCell8 h z =
      Set.pi univ (fun i => Ico (h*(z i : ℝ)) (h*((z i : ℝ)+1))) := by
    ext x
    simp [gridHalfOpenCell8, Set.mem_pi]
  rw [he, Real.volume_pi_Ico]
  have hw : ∀ i : Fin 8, h*((z i : ℝ)+1)-h*(z i : ℝ) = h := by intro i; ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hh 8).symm

theorem gridShrunkCell8_volume (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1) (z : Fin 8 → ℤ) :
    volume (gridShrunkCell8 h γ z) = ENNReal.ofReal ((h*(1-γ))^8) := by
  have he : gridShrunkCell8 h γ z =
      Icc (fun i => h*((z i : ℝ)+γ/2)) (fun i => h*((z i : ℝ)+1-γ/2)) := by
    ext x
    simp only [gridShrunkCell8, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he, Real.volume_Icc_pi]
  have hw : ∀ i : Fin 8, h*((z i : ℝ)+1-γ/2)-h*((z i : ℝ)+γ/2) = h*(1-γ) := by
    intro i
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (mul_nonneg hh (sub_nonneg.mpr hγ)) 8).symm

theorem gridShrunkCell8_volume_factor (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1)
    (z : Fin 8 → ℤ) : volume (gridShrunkCell8 h γ z) =
      ENNReal.ofReal ((1-γ)^8)*volume (gridHalfOpenCell8 h z) := by
  rw [gridShrunkCell8_volume h γ hh hγ z,gridHalfOpenCell8_volume h hh z,
    mul_pow,ENNReal.ofReal_mul (pow_nonneg hh 8),mul_comm]

theorem gridFiniteUnion8_volume (h : ℝ) (hh : 0 < h) (Z : Finset (Fin 8 → ℤ)) :
    volume (⋃ z ∈ Z, gridHalfOpenCell8 h z) = (Z.card : ℝ≥0∞)*ENNReal.ofReal (h^8) := by
  classical
  rw [measure_biUnion_finset (fun z hz w hw hzw => gridHalfOpenCell8_pairwise_disjoint h hh hzw)
    (fun z _ => gridHalfOpenCell8_measurable h z)]
  simp only [gridHalfOpenCell8_volume h hh.le, Finset.sum_const, nsmul_eq_mul]

theorem gridShrunkFiniteUnion8_volume_factor (h γ : ℝ) (hh : 0 < h)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (Z : Finset (Fin 8 → ℤ)) :
    volume (⋃ z ∈ Z, gridShrunkCell8 h γ z) =
      ENNReal.ofReal ((1-γ)^8)*volume (⋃ z ∈ Z, gridHalfOpenCell8 h z) := by
  classical
  rw [measure_biUnion_finset (fun z hz w hw hzw => gridShrunkCell8_pairwise_disjoint h γ hh hγ hzw)
    (fun z _ => (gridShrunkCell8_isCompact h γ z).isClosed.measurableSet),
    measure_biUnion_finset (fun z hz w hw hzw => gridHalfOpenCell8_pairwise_disjoint h hh hzw)
    (fun z _ => gridHalfOpenCell8_measurable h z), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => gridShrunkCell8_volume_factor h γ hh.le hγ1 z)

end SphericalRiesz
