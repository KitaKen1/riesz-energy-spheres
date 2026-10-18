import Riesz.EqualAreaFinitePatchGeometry8
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Normed.Group.Bounded

/-! A common finite coordinate grid covers compact cores with the closed
cells inside their open buffers. No interior of a compact core is assumed.
The coordinate norm here is the Pi sup norm, so a cell has diameter at most h. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
namespace SphericalRiesz

def gridLabel8 (h : ℝ) (x : Fin 8 → ℝ) : Fin 8 → ℤ := fun i => Int.floor (x i/h)

def gridHalfOpenCell8 (h : ℝ) (z : Fin 8 → ℤ) : Set (Fin 8 → ℝ) :=
  {x | ∀ i, h*(z i : ℝ) ≤ x i ∧ x i < h*((z i : ℝ)+1)}

def gridClosedCell8 (h : ℝ) (z : Fin 8 → ℤ) : Set (Fin 8 → ℝ) :=
  {x | ∀ i, h*(z i : ℝ) ≤ x i ∧ x i ≤ h*((z i : ℝ)+1)}

theorem gridLabel8_mem_cell (h : ℝ) (hh : 0 < h) (x : Fin 8 → ℝ) :
    x ∈ gridHalfOpenCell8 h (gridLabel8 h x) := by
  intro i
  constructor
  · have ht := (le_div_iff₀ hh).mp (Int.floor_le (x i/h))
    simpa only [gridLabel8, mul_comm] using ht
  · have ht := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x i/h))
    simpa only [gridLabel8, mul_comm] using ht

theorem gridLabel8_eq_of_mem_cell (h : ℝ) (hh : 0 < h) (z : Fin 8 → ℤ)
    (x : Fin 8 → ℝ) (hx : x ∈ gridHalfOpenCell8 h z) : gridLabel8 h x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using (hx i).1)
  · exact (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using (hx i).2)

theorem gridHalfOpenCell8_subset_closed (h : ℝ) (z : Fin 8 → ℤ) :
    gridHalfOpenCell8 h z ⊆ gridClosedCell8 h z :=
  fun _ hx i => ⟨(hx i).1,(hx i).2.le⟩

theorem gridHalfOpenCell8_pairwise_disjoint (h : ℝ) (hh : 0 < h) :
    Pairwise (fun z w : Fin 8 → ℤ => Disjoint (gridHalfOpenCell8 h z) (gridHalfOpenCell8 h w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hw
  exact hzw ((gridLabel8_eq_of_mem_cell h hh z x hx).symm.trans
    (gridLabel8_eq_of_mem_cell h hh w x hw))

theorem gridClosedCell8_dist_le (h : ℝ) (hh : 0 ≤ h) (z : Fin 8 → ℤ)
    (x y : Fin 8 → ℝ) (hx : x ∈ gridClosedCell8 h z) (hy : y ∈ gridClosedCell8 h z) :
    dist x y ≤ h := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hh).mpr
  intro i
  change |x i-y i| ≤ h
  apply abs_le.mpr
  have hxi := hx i
  have hyi := hy i
  constructor <;> nlinarith

theorem gridLabel8_image_finite (h : ℝ) (hh : 0 < h)
    (k : Set (Fin 8 → ℝ)) (hk : IsCompact k) : (gridLabel8 h '' k).Finite := by
  obtain ⟨R,hR,hbound⟩ := hk.isBounded.exists_pos_norm_le
  apply (Set.Finite.pi' (fun _ : Fin 8 =>
    Set.finite_Icc (Int.floor (-R/h)) (Int.floor (R/h)))).subset
  rintro z ⟨x,hx,rfl⟩ i
  have hi : |x i| ≤ R := (norm_le_pi_norm x i).trans (hbound x hx)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hi
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hlo hh.le),
    Int.floor_mono (div_le_div_of_nonneg_right hhi hh.le)⟩

theorem gridCells8_cover (h : ℝ) (hh : 0 < h) (k : Set (Fin 8 → ℝ)) :
    k ⊆ ⋃ z ∈ gridLabel8 h '' k, gridHalfOpenCell8 h z := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨gridLabel8 h x,⟨x,hx,rfl⟩,gridLabel8_mem_cell h hh x⟩

theorem gridClosedCells8_subset_buffer (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (k U : Set (Fin 8 → ℝ)) (hbuffer : thickening r k ⊆ U) :
    ∀ z ∈ gridLabel8 h '' k, gridClosedCell8 h z ⊆ U := by
  rintro z ⟨x,hx,rfl⟩ y hy
  apply hbuffer
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  exact (gridClosedCell8_dist_le h hh.le _ y x hy
    (gridHalfOpenCell8_subset_closed _ _ (gridLabel8_mem_cell h hh x))).trans_lt hhr

theorem finite_compact_grid8 {ι : Type*} [Fintype ι]
    (k U : ι → Set (Fin 8 → ℝ)) (hk : ∀ i, IsCompact (k i))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, k i ⊆ U i) :
    ∃ h > 0, ∃ Z : ι → Finset (Fin 8 → ℤ),
      ∀ i, k i ⊆ ⋃ z ∈ Z i, gridHalfOpenCell8 h z ∧
        ∀ z ∈ Z i, gridClosedCell8 h z ⊆ U i := by
  classical
  have hm : ∀ i, ∃ r > 0, thickening r (k i) ⊆ U i := fun i =>
    (hk i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hbuffer using hm
  obtain ⟨δ,hδ,hδr⟩ := finite_positive_lower_bound8 r hr
  let h := δ/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Z : ι → Finset (Fin 8 → ℤ) := fun i => (gridLabel8_image_finite h hh (k i) (hk i)).toFinset
  refine ⟨h,hh,Z,?_⟩
  intro i
  have hZ : ∀ z, z ∈ Z i ↔ z ∈ gridLabel8 h '' k i := by
    intro z
    exact Set.Finite.mem_toFinset _
  constructor
  · simpa only [hZ] using gridCells8_cover h hh (k i)
  · intro z hz
    apply gridClosedCells8_subset_buffer h (r i) hh ?_ (k i) (U i) (hbuffer i) z ((hZ z).mp hz)
    dsimp [h]
    linarith [hδr i]

end SphericalRiesz
