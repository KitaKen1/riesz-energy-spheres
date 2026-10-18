import Riesz.EqualAreaFinitePatchGeometry24
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.Disjointed
import Mathlib.Data.Fintype.EquivFin
import Riesz.EqualAreaInverseD
import Riesz.LeechProfileLower24
import Riesz.EqualAreaCoordinateBuffers24
import Riesz.EqualAreaFinitePatchMass24
import Mathlib.Algebra.Order.Ring.Pow
import Riesz.LeechTwelfthSmallBudget24
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order

/-! Near-full rational families of Leech cube patches on S²⁴.

This module is the dimension-24 form of the dimension-8 covering chain (compact coordinate
grids, shrunk cells, finite compact cores, small chart cores, sphere grids and their masses,
capped grids, affine cubes, rational normalization of the common scale).  The parts keep the
order and the statements of that chain, with `S⁸`, the `E8` map and the exponent 8 replaced by
`S²⁴`, the Leech map and the exponent 24.  The result is
`sphere24_near_full_rational_affine_cubes`: for every smallness radius and every residual
fraction there is a finite, pairwise disjoint, separated family of small Leech cube patches of
one common rational scale `r₀ p/q`, each of probability exactly `(p/q)²⁴`, covering more than
`1-b` of the sphere, with `K p²⁴ < q²⁴`.  No points, energies or budgets are asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SphericalRiesz

section CompactGrid
open Set Metric

/-! ### CompactGrid

A common finite coordinate grid covers compact cores with the closed
cells inside their open buffers. No interior of a compact core is assumed.
The coordinate norm here is the Pi sup norm, so a cell has diameter at most h. -/

def gridLabel24 (h : ℝ) (x : Fin 24 → ℝ) : Fin 24 → ℤ := fun i => Int.floor (x i/h)

def gridHalfOpenCell24 (h : ℝ) (z : Fin 24 → ℤ) : Set (Fin 24 → ℝ) :=
  {x | ∀ i, h*(z i : ℝ) ≤ x i ∧ x i < h*((z i : ℝ)+1)}

def gridClosedCell24 (h : ℝ) (z : Fin 24 → ℤ) : Set (Fin 24 → ℝ) :=
  {x | ∀ i, h*(z i : ℝ) ≤ x i ∧ x i ≤ h*((z i : ℝ)+1)}

theorem gridLabel24_mem_cell (h : ℝ) (hh : 0 < h) (x : Fin 24 → ℝ) :
    x ∈ gridHalfOpenCell24 h (gridLabel24 h x) := by
  intro i
  constructor
  · have ht := (le_div_iff₀ hh).mp (Int.floor_le (x i/h))
    simpa only [gridLabel24, mul_comm] using ht
  · have ht := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x i/h))
    simpa only [gridLabel24, mul_comm] using ht

theorem gridLabel24_eq_of_mem_cell (h : ℝ) (hh : 0 < h) (z : Fin 24 → ℤ)
    (x : Fin 24 → ℝ) (hx : x ∈ gridHalfOpenCell24 h z) : gridLabel24 h x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using (hx i).1)
  · exact (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using (hx i).2)

theorem gridHalfOpenCell24_subset_closed (h : ℝ) (z : Fin 24 → ℤ) :
    gridHalfOpenCell24 h z ⊆ gridClosedCell24 h z :=
  fun _ hx i => ⟨(hx i).1,(hx i).2.le⟩

theorem gridHalfOpenCell24_pairwise_disjoint (h : ℝ) (hh : 0 < h) :
    Pairwise (fun z w : Fin 24 → ℤ => Disjoint (gridHalfOpenCell24 h z) (gridHalfOpenCell24 h w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hw
  exact hzw ((gridLabel24_eq_of_mem_cell h hh z x hx).symm.trans
    (gridLabel24_eq_of_mem_cell h hh w x hw))

theorem gridClosedCell24_dist_le (h : ℝ) (hh : 0 ≤ h) (z : Fin 24 → ℤ)
    (x y : Fin 24 → ℝ) (hx : x ∈ gridClosedCell24 h z) (hy : y ∈ gridClosedCell24 h z) :
    dist x y ≤ h := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hh).mpr
  intro i
  change |x i-y i| ≤ h
  apply abs_le.mpr
  have hxi := hx i
  have hyi := hy i
  constructor <;> nlinarith

theorem gridLabel24_image_finite (h : ℝ) (hh : 0 < h)
    (k : Set (Fin 24 → ℝ)) (hk : IsCompact k) : (gridLabel24 h '' k).Finite := by
  obtain ⟨R,hR,hbound⟩ := hk.isBounded.exists_pos_norm_le
  apply (Set.Finite.pi' (fun _ : Fin 24 =>
    Set.finite_Icc (Int.floor (-R/h)) (Int.floor (R/h)))).subset
  rintro z ⟨x,hx,rfl⟩ i
  have hi : |x i| ≤ R := (norm_le_pi_norm x i).trans (hbound x hx)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hi
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hlo hh.le),
    Int.floor_mono (div_le_div_of_nonneg_right hhi hh.le)⟩

theorem gridCells24_cover (h : ℝ) (hh : 0 < h) (k : Set (Fin 24 → ℝ)) :
    k ⊆ ⋃ z ∈ gridLabel24 h '' k, gridHalfOpenCell24 h z := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨gridLabel24 h x,⟨x,hx,rfl⟩,gridLabel24_mem_cell h hh x⟩

theorem gridClosedCells24_subset_buffer (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (k U : Set (Fin 24 → ℝ)) (hbuffer : thickening r k ⊆ U) :
    ∀ z ∈ gridLabel24 h '' k, gridClosedCell24 h z ⊆ U := by
  rintro z ⟨x,hx,rfl⟩ y hy
  apply hbuffer
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  exact (gridClosedCell24_dist_le h hh.le _ y x hy
    (gridHalfOpenCell24_subset_closed _ _ (gridLabel24_mem_cell h hh x))).trans_lt hhr

theorem finite_compact_grid24 {ι : Type*} [Fintype ι]
    (k U : ι → Set (Fin 24 → ℝ)) (hk : ∀ i, IsCompact (k i))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, k i ⊆ U i) :
    ∃ h > 0, ∃ Z : ι → Finset (Fin 24 → ℤ),
      ∀ i, k i ⊆ ⋃ z ∈ Z i, gridHalfOpenCell24 h z ∧
        ∀ z ∈ Z i, gridClosedCell24 h z ⊆ U i := by
  classical
  have hm : ∀ i, ∃ r > 0, thickening r (k i) ⊆ U i := fun i =>
    (hk i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hbuffer using hm
  obtain ⟨δ,hδ,hδr⟩ := finite24_positive_lower_bound8 r hr
  let h := δ/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Z : ι → Finset (Fin 24 → ℤ) := fun i => (gridLabel24_image_finite h hh (k i) (hk i)).toFinset
  refine ⟨h,hh,Z,?_⟩
  intro i
  have hZ : ∀ z, z ∈ Z i ↔ z ∈ gridLabel24 h '' k i := by
    intro z
    exact Set.Finite.mem_toFinset _
  constructor
  · simpa only [hZ] using gridCells24_cover h hh (k i)
  · intro z hz
    apply gridClosedCells24_subset_buffer h (r i) hh ?_ (k i) (U i) (hbuffer i) z ((hZ z).mp hz)
    dsimp [h]
    linarith [hδr i]

end CompactGrid

section GridShrink
open Set MeasureTheory
open scoped ENNReal

/-! ### GridShrink

Exact coordinate volumes and strict gaps for the known shrink factor.
Original half-open cells partition without boundary overlaps; shrunk closed
cells are compact, disjoint, and retain the exact factor (1-gamma)^24. -/

def gridShrunkCell24 (h γ : ℝ) (z : Fin 24 → ℤ) : Set (Fin 24 → ℝ) :=
  {x | ∀ i, h*((z i : ℝ)+γ/2) ≤ x i ∧ x i ≤ h*((z i : ℝ)+1-γ/2)}

theorem gridHalfOpenCell24_measurable (h : ℝ) (z : Fin 24 → ℤ) :
    MeasurableSet (gridHalfOpenCell24 h z) := by
  have he : gridHalfOpenCell24 h z =
      Set.pi univ (fun i => Ico (h*(z i : ℝ)) (h*((z i : ℝ)+1))) := by
    ext x
    simp [gridHalfOpenCell24, Set.mem_pi]
  rw [he]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem gridClosedCell24_isCompact (h : ℝ) (z : Fin 24 → ℤ) :
    IsCompact (gridClosedCell24 h z) := by
  have he : gridClosedCell24 h z =
      Icc (fun i => h*(z i : ℝ)) (fun i => h*((z i : ℝ)+1)) := by
    ext x
    simp only [gridClosedCell24, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

theorem gridShrunkCell24_isCompact (h γ : ℝ) (z : Fin 24 → ℤ) :
    IsCompact (gridShrunkCell24 h γ z) := by
  have he : gridShrunkCell24 h γ z =
      Icc (fun i => h*((z i : ℝ)+γ/2)) (fun i => h*((z i : ℝ)+1-γ/2)) := by
    ext x
    simp only [gridShrunkCell24, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact isCompact_Icc

theorem gridShrunkCell24_subset_halfOpen (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ)
    (z : Fin 24 → ℤ) : gridShrunkCell24 h γ z ⊆ gridHalfOpenCell24 h z := by
  intro x hx i
  have hi := hx i
  have hp : 0 < h*γ := mul_pos hh hγ
  constructor <;> nlinarith

theorem gridShrunkCell24_pairwise_disjoint (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) :
    Pairwise (fun z w : Fin 24 → ℤ => Disjoint (gridShrunkCell24 h γ z) (gridShrunkCell24 h γ w)) := by
  intro z w hzw
  exact (gridHalfOpenCell24_pairwise_disjoint h hh hzw).mono
    (gridShrunkCell24_subset_halfOpen h γ hh hγ z)
    (gridShrunkCell24_subset_halfOpen h γ hh hγ w)

theorem gridHalfOpenCell24_volume (h : ℝ) (hh : 0 ≤ h) (z : Fin 24 → ℤ) :
    volume (gridHalfOpenCell24 h z) = ENNReal.ofReal (h^24) := by
  have he : gridHalfOpenCell24 h z =
      Set.pi univ (fun i => Ico (h*(z i : ℝ)) (h*((z i : ℝ)+1))) := by
    ext x
    simp [gridHalfOpenCell24, Set.mem_pi]
  rw [he, Real.volume_pi_Ico]
  have hw : ∀ i : Fin 24, h*((z i : ℝ)+1)-h*(z i : ℝ) = h := by intro i; ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hh 24).symm

theorem gridShrunkCell24_volume (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1) (z : Fin 24 → ℤ) :
    volume (gridShrunkCell24 h γ z) = ENNReal.ofReal ((h*(1-γ))^24) := by
  have he : gridShrunkCell24 h γ z =
      Icc (fun i => h*((z i : ℝ)+γ/2)) (fun i => h*((z i : ℝ)+1-γ/2)) := by
    ext x
    simp only [gridShrunkCell24, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he, Real.volume_Icc_pi]
  have hw : ∀ i : Fin 24, h*((z i : ℝ)+1-γ/2)-h*((z i : ℝ)+γ/2) = h*(1-γ) := by
    intro i
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (mul_nonneg hh (sub_nonneg.mpr hγ)) 24).symm

theorem gridShrunkCell24_volume_factor (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1)
    (z : Fin 24 → ℤ) : volume (gridShrunkCell24 h γ z) =
      ENNReal.ofReal ((1-γ)^24)*volume (gridHalfOpenCell24 h z) := by
  rw [gridShrunkCell24_volume h γ hh hγ z,gridHalfOpenCell24_volume h hh z,
    mul_pow,ENNReal.ofReal_mul (pow_nonneg hh 24),mul_comm]

theorem gridFiniteUnion24_volume (h : ℝ) (hh : 0 < h) (Z : Finset (Fin 24 → ℤ)) :
    volume (⋃ z ∈ Z, gridHalfOpenCell24 h z) = (Z.card : ℝ≥0∞)*ENNReal.ofReal (h^24) := by
  classical
  rw [measure_biUnion_finset (fun z hz w hw hzw => gridHalfOpenCell24_pairwise_disjoint h hh hzw)
    (fun z _ => gridHalfOpenCell24_measurable h z)]
  simp only [gridHalfOpenCell24_volume h hh.le, Finset.sum_const, nsmul_eq_mul]

theorem gridShrunkFiniteUnion24_volume_factor (h γ : ℝ) (hh : 0 < h)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (Z : Finset (Fin 24 → ℤ)) :
    volume (⋃ z ∈ Z, gridShrunkCell24 h γ z) =
      ENNReal.ofReal ((1-γ)^24)*volume (⋃ z ∈ Z, gridHalfOpenCell24 h z) := by
  classical
  rw [measure_biUnion_finset (fun z hz w hw hzw => gridShrunkCell24_pairwise_disjoint h γ hh hγ hzw)
    (fun z _ => (gridShrunkCell24_isCompact h γ z).isClosed.measurableSet),
    measure_biUnion_finset (fun z hz w hw hzw => gridHalfOpenCell24_pairwise_disjoint h hh hzw)
    (fun z _ => gridHalfOpenCell24_measurable h z), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => gridShrunkCell24_volume_factor h γ hh.le hγ1 z)

end GridShrink

section SphereFiniteCompactCores
open Set MeasureTheory Metric
open scoped Topology ENNReal

/-! ### SphereFiniteCompactCores

Any supplied finite measurable sphere cover admits compact cores with
arbitrarily small lost probability. For an open cover, the cores have a
common positive buffer inside the original cover and disjoint buffers.
This is an actual probability-measure existence theorem, not yet an Leech
chart atlas or a finite equal-scale cube extraction theorem. -/

theorem sphereProbability24_compact_core (s : Set (SphereD 24)) (hs : MeasurableSet s)
    (b : ℝ) (hb : 0 < b) :
    ∃ k ⊆ s, IsCompact k ∧ (sphereProbabilityD 24) (s \ k) < ENNReal.ofReal b := by
  have hS : IsClosed ((SphereD 24) : Set (AmbientD 24)) := isClosed_sphere
  let : PolishSpace (SphereD 24) := hS.polishSpace
  exact hs.exists_isCompact_sdiff_lt (measure_ne_top (sphereProbabilityD 24) s)
    (ENNReal.ofReal_pos.mpr hb).ne'

theorem sphereFiniteCover24_residual_le {K : ℕ} (s k : Fin K → Set (SphereD 24))
    (hcover : (⋃ i, s i) = univ) :
    (sphereProbabilityD 24) (⋃ i, k i)ᶜ ≤ ∑ i : Fin K, (sphereProbabilityD 24) (s i \ k i) := by
  have hsub : (⋃ i, k i)ᶜ ⊆ ⋃ i, s i \ k i := by
    intro x hx
    have hxcover : x ∈ ⋃ i, s i := hcover.symm ▸ mem_univ x
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxcover
    exact mem_iUnion.mpr ⟨i,hi,fun hki => hx (mem_iUnion.mpr ⟨i,hki⟩)⟩
  have hsum : (sphereProbabilityD 24) (⋃ i, s i \ k i) ≤
      ∑ i : Fin K, (sphereProbabilityD 24) (s i \ k i) := by
    simpa only [tsum_fintype] using
      (measure_iUnion_le (μ := (sphereProbabilityD 24)) (fun i : Fin K => s i \ k i))
  exact (measure_mono hsub).trans hsum

theorem sphereFiniteCover24_compact_cores {K : ℕ} (s : Fin K → Set (SphereD 24))
    (hs : ∀ i, MeasurableSet (s i)) (hcover : (⋃ i, s i) = univ)
    (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set (SphereD 24), (∀ i, k i ⊆ s i) ∧ (∀ i, IsCompact (k i)) ∧
      (sphereProbabilityD 24) (⋃ i, k i)ᶜ < ENNReal.ofReal b := by
  classical
  let a : ℝ := b/((K : ℝ)+1)
  have ha : 0 < a := div_pos hb (by positivity)
  have h : ∀ i, ∃ k ⊆ s i, IsCompact k ∧ (sphereProbabilityD 24) (s i \ k) < ENNReal.ofReal a :=
    fun i => sphereProbability24_compact_core (s i) (hs i) a ha
  choose k hsub hcompact hloss using h
  refine ⟨k,hsub,hcompact,?_⟩
  have hab : (K : ℝ)*a < b := by
    have he : ((K : ℝ)+1)*a = b := by
      dsimp [a]
      field_simp
    nlinarith
  calc
    (sphereProbabilityD 24) (⋃ i, k i)ᶜ ≤ ∑ i, (sphereProbabilityD 24) (s i \ k i) :=
      sphereFiniteCover24_residual_le s k hcover
    _ ≤ ∑ _i : Fin K, ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => (hloss i).le)
    _ = ENNReal.ofReal ((K : ℝ)*a) := by
      simp [ENNReal.ofReal_mul]
    _ < ENNReal.ofReal b := (ENNReal.ofReal_lt_ofReal_iff hb).mpr hab

theorem sphereFiniteCover24_disjoint_partition {K : ℕ} (U : Fin K → Set (SphereD 24))
    (hU : ∀ i, MeasurableSet (U i)) (hcover : (⋃ i, U i) = univ) :
    ∃ s : Fin K → Set (SphereD 24), (∀ i, MeasurableSet (s i)) ∧ (∀ i, s i ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ := by
  refine ⟨disjointed U,?_,fun i => disjointed_subset U i,disjoint_disjointed U,?_⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hU i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun (_h : j < i) => (hU j).compl)
  · rw [iUnion_disjointed,hcover]

theorem sphereFinitePartition24_separated_cores {K : ℕ} (s : Fin K → Set (SphereD 24))
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) = univ) (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set (SphereD 24), ∃ δ > 0,
      (∀ i, k i ⊆ s i ∧ IsCompact (k i)) ∧
      (sphereProbabilityD 24) (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      (∀ i j, i ≠ j → ∀ x ∈ k i, ∀ y ∈ k j, δ < dist x y) := by
  obtain ⟨k,hsub,hcomp,hloss⟩ := sphereFiniteCover24_compact_cores s hs hcover b hb
  have hkd : Pairwise (fun i j => Disjoint (k i) (k j)) :=
    fun i j hij => (hd hij).mono (hsub i) (hsub j)
  obtain ⟨δ,hδ,hsep⟩ := finite24_compact_disjoint_distance8 k hcomp hkd
  exact ⟨k,δ,hδ,fun i => ⟨hsub i,hcomp i⟩,hloss,hsep⟩

theorem sphereFiniteOpenCover24_buffered_cores {K : ℕ} (U : Fin K → Set (SphereD 24))
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set (SphereD 24), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ U i ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ U i) ∧
      (sphereProbabilityD 24) (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨s,hsm,hss,hsd,hscov⟩ := sphereFiniteCover24_disjoint_partition U
    (fun i => (hU i).measurableSet) hcover
  obtain ⟨k,hks,hcomp,hloss⟩ := sphereFiniteCover24_compact_cores s hsm hscov b hb
  have hkd : Pairwise (fun i j => Disjoint (k i) (k j)) :=
    fun i j hij => (hsd hij).mono (hks i) (hks j)
  have hkU : ∀ i, k i ⊆ U i := fun i => (hks i).trans (hss i)
  obtain ⟨ρ,hρ,hbuf,hdis⟩ := finite24_compact_chart_buffers8 k U hcomp hkd hU hkU
  exact ⟨k,ρ,hρ,fun i => ⟨hcomp i,hkU i,hbuf i⟩,hloss,hdis⟩

theorem sphere24_finite_ball_cover (r : ℝ) (hr : 0 < r) :
    ∃ K : ℕ, ∃ p : Fin K → (SphereD 24), (⋃ i, ball (p i) r) = univ := by
  classical
  let : CompactSpace (SphereD 24) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (AmbientD 24)) 1)
  obtain ⟨t,ht⟩ := (isCompact_univ : IsCompact (univ : Set (SphereD 24))).elim_finite_subcover
    (fun p : (SphereD 24) => ball p r) (fun _ => isOpen_ball)
    (fun p _ => mem_iUnion.mpr ⟨p,mem_ball_self hr⟩)
  let p : Fin t.card → (SphereD 24) := fun i => (t.equivFin.symm i).val
  refine ⟨t.card,p,?_⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨y,hy⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨t.equivFin ⟨y,hyt⟩,by simpa only [p,Equiv.symm_apply_apply] using hxy⟩

theorem sphere24_finite_ball_buffered_cores (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ K : ℕ, ∃ p : Fin K → (SphereD 24), ∃ k : Fin K → Set (SphereD 24), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ ball (p i) r ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ ball (p i) r) ∧
      (sphereProbabilityD 24) (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨K,p,hcover⟩ := sphere24_finite_ball_cover r hr
  obtain ⟨k,ρ,hρ,hk,hloss,hd⟩ := sphereFiniteOpenCover24_buffered_cores
    (fun i => ball (p i) r) (fun _ => isOpen_ball) hcover b hb
  exact ⟨K,p,k,ρ,hρ,hk,hloss,hd⟩

theorem sphereProbability24_mass_of_residual (s : Set (SphereD 24)) (hs : MeasurableSet s)
    (b : ℝ) (hb : 0 < b) (hloss : (sphereProbabilityD 24) sᶜ < ENNReal.ofReal b) :
    1-b < (sphereProbabilityD 24).real s := by
  have h := (ENNReal.toReal_lt_toReal (measure_ne_top (sphereProbabilityD 24) sᶜ)
    ENNReal.ofReal_ne_top).mpr hloss
  rw [ENNReal.toReal_ofReal hb.le] at h
  change (sphereProbabilityD 24).real sᶜ < b at h
  rw [measureReal_compl hs,probReal_univ] at h
  linarith

theorem sphere24_finite_ball_buffered_cores_mass (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ K : ℕ, ∃ p : Fin K → (SphereD 24), ∃ k : Fin K → Set (SphereD 24), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ ball (p i) r ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ ball (p i) r) ∧
      1-b < (sphereProbabilityD 24).real (⋃ i, k i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨K,p,k,ρ,hρ,hk,hloss,hd⟩ := sphere24_finite_ball_buffered_cores r b hr hb
  exact ⟨K,p,k,ρ,hρ,hk,sphereProbability24_mass_of_residual _
    (MeasurableSet.iUnion fun i => (hk i).1.measurableSet) b hb hloss,hd⟩

end SphereFiniteCompactCores

section SphereSmallChartCores
open Set MeasureTheory Metric
open scoped Topology

/-! ### SphereSmallChartCores

Quantitative small-ball coverage by explicit rotated equal-area charts.
The near-full compact cores now lie in actual small chart images, with
disjoint open buffers. Equal-scale Leech grid cells remain a separate step. -/

theorem equalAreaInverse24_small_ball_norm (q : (SphereD 24)) (r : ℝ) (hr : r ≤ 1/2)
    (hq : q ∈ ball northPole24 r) : ‖equalAreaInverseD (q : (AmbientD 24))‖ ≤ 2*r := by
  have hfirst := northPole24_ball_first_pos q r hr hq
  have hrpos : 0 < r := (dist_nonneg : 0 ≤ dist q northPole24).trans_lt hq
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*r)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |Real.arctan ((q : (AmbientD 24)) 1/(q : (AmbientD 24)) 0)| ≤ 2*r
    have h := (sphere24_coordinate_difference_le_dist q northPole24 1).trans_lt hq
    have hcoord : |(q : (AmbientD 24)) 1| < r := by simpa [northPole24] using h
    have hquot : |(q : (AmbientD 24)) 1/(q : (AmbientD 24)) 0| < 2*r := by
      rw [abs_div,abs_of_pos (by linarith : 0 < (q : (AmbientD 24)) 0)]
      apply (div_lt_iff₀ (by linarith : 0 < (q : (AmbientD 24)) 0)).mpr
      nlinarith
    exact Real.abs_arctan_le_abs.trans hquot.le
  · change |(q : (AmbientD 24)) j.succ.succ| ≤ 2*r
    have h := (sphere24_coordinate_difference_le_dist q northPole24 j.succ.succ).trans_lt hq
    have hcoord : |(q : (AmbientD 24)) j.succ.succ| < r := by
      simpa [northPole24] using h
    linarith

theorem northPole24_ball_chart (q : (SphereD 24)) (r : ℝ) (hr : r ≤ 1/2)
    (hq : q ∈ ball northPole24 r) :
    equalAreaInverseD (q : (AmbientD 24)) ∈ equalAreaChartDomainD ∧
      ‖equalAreaInverseD (q : (AmbientD 24))‖ ≤ 2*r ∧ equalAreaPhiD (equalAreaInverseD (q : (AmbientD 24))) = (q : (AmbientD 24)) := by
  have hf : 0 < (q : (AmbientD 24)) 0 := by
    have h := northPole24_ball_first_pos q r hr hq
    linarith
  exact ⟨equalAreaInverseD_mem_domain q hf,equalAreaInverse24_small_ball_norm q r hr hq,
    equalAreaPhiD_inverse8 q hf⟩

theorem sphere24_ball_rotated_chart (p : (SphereD 24)) (r : ℝ) (hr : r ≤ 1/2) :
    ∃ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), sphereRotationD g northPole24 = p ∧
      ∀ q ∈ ball p r, ∃ u ∈ equalAreaChartDomainD, ‖u‖ ≤ 2*r ∧
        g (equalAreaPhiD u) = (q : (AmbientD 24)) := by
  obtain ⟨g,hg⟩ := sphereRotation24_transitive northPole24 p
  refine ⟨g,hg,?_⟩
  intro q hq
  let z : (SphereD 24) := sphereRotationD g.symm q
  have hgz : sphereRotationD g z = q := by
    apply Subtype.ext
    exact g.apply_symm_apply q
  have hz : z ∈ ball northPole24 r := by
    rw [mem_ball,← sphereRotationD_dist g z northPole24,hgz,hg]
    exact hq
  obtain ⟨hu,hn,hphi⟩ := northPole24_ball_chart z r hr hz
  refine ⟨equalAreaInverseD (z : (AmbientD 24)),hu,hn,?_⟩
  rw [hphi]
  exact g.apply_symm_apply q

theorem sphere24_finite_small_chart_buffered_cores (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ k : Fin K → Set (SphereD 24), ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧
        ∀ q ∈ thickening ρ (k i), ∃ u ∈ equalAreaChartDomainD,
          ‖u‖ < a ∧ g i (equalAreaPhiD u) = (q : (AmbientD 24))) ∧
      1-b < (sphereProbabilityD 24).real (⋃ i, k i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  classical
  let r : ℝ := min (a/4) (1/4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrhalf : r ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hra : 2*r < a := by
    have h := min_le_left (a/4) (1/4)
    change r ≤ a/4 at h
    linarith
  obtain ⟨K,p,k,ρ,hρ,hk,hmass,hd⟩ := sphere24_finite_ball_buffered_cores_mass r b hr hb
  have h : ∀ i, ∃ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), sphereRotationD g northPole24 = p i ∧
      ∀ q ∈ ball (p i) r, ∃ u ∈ equalAreaChartDomainD, ‖u‖ ≤ 2*r ∧
        g (equalAreaPhiD u) = (q : (AmbientD 24)) :=
    fun i => sphere24_ball_rotated_chart (p i) r hrhalf
  choose g hg hchart using h
  refine ⟨K,g,k,ρ,hρ,?_,hmass,hd⟩
  intro i
  refine ⟨(hk i).1,(hk i).2.2.1,(hk i).2.2.2.1,?_⟩
  intro q hq
  obtain ⟨u,hu,hn,he⟩ := hchart i q ((hk i).2.2.2.2 hq)
  exact ⟨u,hu,hn.trans_lt hra,he⟩

end SphereSmallChartCores

section SphereGrid
open Set Metric MeasureTheory

/-! ### SphereGrid

Apply finite floor grids to the actual near-full rotated small-chart
cores. The unshrunk half-open cells cover those cores, with all closed
cells inside the physically disjoint open buffers. -/

theorem equalAreaRotatedHemisphere24_of_representation (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (q : (SphereD 24)) (u : Fin 24 → ℝ) (hu : u ∈ equalAreaChartDomainD)
    (he : g (equalAreaPhiD u) = (q : (AmbientD 24))) : q ∈ equalAreaRotatedHemisphere24 g := by
  change 0 < (g.symm (q : (AmbientD 24))) 0
  rw [← he,g.symm_apply_apply]
  exact equalAreaPhiD_first_pos u hu

theorem leechCoordinateBuffer24_mem (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (U : Set (SphereD 24))
    (x : Fin 24 → ℝ) (hx : x ∈ leechCoordinateInverse24 '' equalAreaCoordinateBuffer24 g U) :
    leechMap x ∈ equalAreaChartDomainD ∧ ∃ q ∈ U, g (equalAreaPhiD (leechMap x)) = (q : (AmbientD 24)) := by
  obtain ⟨u,hu,rfl⟩ := hx
  rw [leechMap_coordinateInverse8]
  exact equalAreaCoordinateBuffer24_mem g U u hu

theorem leechCoordinateBuffer24_norm_lt (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (U : Set (SphereD 24)) (a : ℝ)
    (hsmall : ∀ q ∈ U, ∃ u ∈ equalAreaChartDomainD, ‖u‖ < a ∧
      g (equalAreaPhiD u) = (q : (AmbientD 24)))
    (x : Fin 24 → ℝ) (hx : x ∈ leechCoordinateInverse24 '' equalAreaCoordinateBuffer24 g U) :
    ‖leechMap x‖ < a := by
  obtain ⟨hu,q,hq,he⟩ := leechCoordinateBuffer24_mem g U x hx
  obtain ⟨u,hu',hn,he'⟩ := hsmall q hq
  have hxu := equalAreaPhiD_injOn hu hu' (g.injective (he.trans he'.symm))
  simpa only [hxu] using hn

theorem leechGridSpherePatch24_subset_buffer (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (s : Set (Fin 24 → ℝ)) (U : Set (SphereD 24))
    (hs : s ⊆ leechCoordinateInverse24 '' equalAreaCoordinateBuffer24 g U) :
    equalAreaLeechSpherePatch24 g 0 0 1 s ⊆ U := by
  intro q hq
  obtain ⟨x,hx,he⟩ := hq
  obtain ⟨_,p,hp,he'⟩ := leechCoordinateBuffer24_mem g U x (hs hx)
  have he0 : g (equalAreaPhiD (leechMap x)) = (q : (AmbientD 24)) := by
    simpa only [equalAreaLeechPatch,equalAreaMovingLeechChart,sub_zero,one_smul,zero_add] using he
  have heq : (q : (AmbientD 24)) = (p : (AmbientD 24)) := by
    exact he0.symm.trans he'
  exact (Subtype.ext heq).symm ▸ hp

theorem sphere24_finite_small_chart_grid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ U : Fin K → Set (SphereD 24), ∃ h > 0, ∃ Z : Fin K → Finset (Fin 24 → ℤ),
      (∀ i, IsOpen (U i) ∧ ∀ z ∈ Z i,
        leechMap '' gridClosedCell24 h z ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridClosedCell24 h z, ‖leechMap x‖ < a) ∧
        equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridClosedCell24 h z) ⊆ U i) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, ⋃ z ∈ Z i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h z)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  obtain ⟨K,g,k,ρ,hρ,hk,hmass,hd⟩ := sphere24_finite_small_chart_buffered_cores a b ha hb
  let U : Fin K → Set (SphereD 24) := fun i => thickening ρ (k i)
  have hkh : ∀ i, k i ⊆ equalAreaRotatedHemisphere24 (g i) := by
    intro i q hq
    obtain ⟨u,hu,_,he⟩ := (hk i).2.2.2 q ((hk i).2.2.1 hq)
    exact equalAreaRotatedHemisphere24_of_representation (g i) q u hu he
  let c : Fin K → Set (Fin 24 → ℝ) := fun i =>
    leechCoordinateInverse24 '' (equalAreaRotatedInverse24 (g i) '' k i)
  let V : Fin K → Set (Fin 24 → ℝ) := fun i =>
    leechCoordinateInverse24 '' equalAreaCoordinateBuffer24 (g i) (U i)
  have hc : ∀ i, IsCompact (c i) := fun i =>
    leechCoordinateCore24_isCompact (g i) (k i) (hk i).1 (hkh i)
  have hV : ∀ i, IsOpen (V i) := fun i =>
    leechCoordinateBuffer24_isOpen (g i) (U i) (hk i).2.1
  have hsub : ∀ i, c i ⊆ V i := fun i => image_mono
    (equalAreaCoordinateCore24_subset_buffer (g i) (k i) (U i) (hkh i) (hk i).2.2.1)
  obtain ⟨h,hh,Z,hgrid⟩ := finite_compact_grid24 c V hc hV hsub
  refine ⟨K,g,U,h,hh,Z,?_,?_,hd⟩
  · intro i
    refine ⟨(hk i).2.1,?_⟩
    intro z hz
    have hcell := (hgrid i).2 z hz
    refine ⟨?_,?_,leechGridSpherePatch24_subset_buffer (g i) _ (U i) hcell⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact (leechCoordinateBuffer24_mem (g i) (U i) x (hcell hx)).1
    · intro x hx
      exact leechCoordinateBuffer24_norm_lt (g i) (U i) a (hk i).2.2.2 x (hcell hx)
  · apply hmass.trans_le
    apply measureReal_mono (μ := (sphereProbabilityD 24)) ?_ (measure_ne_top _ _)
    intro q hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    let x := leechCoordinateInverse24 (equalAreaRotatedInverse24 (g i) q)
    have hx : x ∈ c i := ⟨equalAreaRotatedInverse24 (g i) q,⟨q,hi,rfl⟩,rfl⟩
    obtain ⟨z,hz,hcell⟩ := mem_iUnion₂.mp ((hgrid i).1 hx)
    apply mem_iUnion.mpr
    refine ⟨i,mem_iUnion₂.mpr ⟨z,hz,?_⟩⟩
    refine ⟨x,hcell,?_⟩
    simpa [equalAreaLeechPatch,equalAreaMovingLeechChart,x,leechMap_coordinateInverse8] using
      equalAreaRotatedPhi24_inverse8 (g i) q (hkh i hi)

end SphereGrid

section SphereGridMass
open Set MeasureTheory
open scoped ENNReal

/-! ### SphereGridMass

Exact finite shrink accounting in the actual sphere probability measure.
Compactness and disjointness concern physical (SphereD 24) images, rather than
only their coordinates. These are interval cells; the affine unit-cube
parameterization and rational node counts are separate obligations. -/

theorem leechGridAffine24_eq_map : equalAreaLeechAffine24 0 0 1 = leechMap := by
  funext x
  simp only [equalAreaLeechAffine24,sub_zero,one_smul,zero_add]

theorem leechGridSpherePatch24_mono (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    {s t : Set (Fin 24 → ℝ)} (hst : s ⊆ t) :
    equalAreaLeechSpherePatch24 g 0 0 1 s ⊆ equalAreaLeechSpherePatch24 g 0 0 1 t :=
  preimage_mono (image_mono hst)

theorem leechGridSpherePatch24_isCompact (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (s : Set (Fin 24 → ℝ)) (hs : IsCompact s) :
    IsCompact (equalAreaLeechSpherePatch24 g 0 0 1 s) := by
  let : CompactSpace (SphereD 24) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (AmbientD 24)) 1)
  have hf : Continuous (equalAreaLeechPatch g 0 0 1) := by
    unfold equalAreaLeechPatch equalAreaMovingLeechChart
    exact g.continuous.comp (equalAreaPhiD_continuous.comp (by fun_prop))
  exact ((hs.image hf).isClosed.preimage continuous_subtype_val).isCompact

theorem leechGridSpherePatch24_probability (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (s : Set (Fin 24 → ℝ)) (hs : MeasurableSet s)
    (hdom : leechMap '' s ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 24) (equalAreaLeechSpherePatch24 g 0 0 1 s) =
      ENNReal.ofReal (1/(sphereAreaD 24).real univ)*volume s := by
  simpa only [leechGridAffine24_eq_map,equalAreaLeechPatchProbabilityDensity24,one_pow] using
    equalAreaLeechSpherePatch24_probability g 0 0 1 zero_lt_one s hs (by
      simpa only [leechGridAffine24_eq_map] using hdom)

theorem leechGridSpherePatch24_measurable (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (s : Set (Fin 24 → ℝ)) (hs : MeasurableSet s)
    (hdom : leechMap '' s ⊆ equalAreaChartDomainD) :
    MeasurableSet (equalAreaLeechSpherePatch24 g 0 0 1 s) :=
  equalAreaLeechSpherePatch24_measurable g 0 0 1 zero_lt_one s hs (by
    simpa only [leechGridAffine24_eq_map] using hdom)

theorem leechGridSpherePatch24_disjoint (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (s t : Set (Fin 24 → ℝ)) (hs : leechMap '' s ⊆ equalAreaChartDomainD)
    (ht : leechMap '' t ⊆ equalAreaChartDomainD) (hd : Disjoint s t) :
    Disjoint (equalAreaLeechSpherePatch24 g 0 0 1 s) (equalAreaLeechSpherePatch24 g 0 0 1 t) :=
  equalAreaLeechSpherePatch24_disjoint g 0 0 1 zero_lt_one s t
    (by simpa only [leechGridAffine24_eq_map] using hs)
    (by simpa only [leechGridAffine24_eq_map] using ht) hd

theorem leechGridShrunkSphereCell24_probability_factor (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (z : Fin 24 → ℤ)
    (hdom : leechMap '' gridClosedCell24 h z ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 24) (equalAreaLeechSpherePatch24 g 0 0 1 (gridShrunkCell24 h γ z)) =
      ENNReal.ofReal ((1-γ)^24)*
        (sphereProbabilityD 24) (equalAreaLeechSpherePatch24 g 0 0 1 (gridHalfOpenCell24 h z)) := by
  have hs := gridShrunkCell24_subset_halfOpen h γ hh hγ z
  have ht := gridHalfOpenCell24_subset_closed h z
  rw [leechGridSpherePatch24_probability g _
    (gridShrunkCell24_isCompact h γ z).isClosed.measurableSet ((image_mono (hs.trans ht)).trans hdom),
    leechGridSpherePatch24_probability g _ (gridHalfOpenCell24_measurable h z)
      ((image_mono ht).trans hdom),gridShrunkCell24_volume_factor h γ hh.le hγ1 z]
  ring

theorem leechGridShrunkSphereFamily24_disjoint {ι : Type*}
    (g : ι → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (z : ι → Fin 24 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i)))
      (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridHalfOpenCell24 h (z j))))) :
    Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)))
      (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridShrunkCell24 h γ (z j)))) := by
  intro i j hij
  exact (hd hij).mono
    (leechGridSpherePatch24_mono _ (gridShrunkCell24_subset_halfOpen h γ hh hγ (z i)))
    (leechGridSpherePatch24_mono _ (gridShrunkCell24_subset_halfOpen h γ hh hγ (z j)))

theorem leechGridShrunkSphereFamily24_probability_factor {ι : Type*} [Fintype ι]
    (g : ι → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (z : ι → Fin 24 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdom : ∀ i, leechMap '' gridClosedCell24 h (z i) ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i)))
      (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridHalfOpenCell24 h (z j))))) :
    (sphereProbabilityD 24) (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) =
      ENNReal.ofReal ((1-γ)^24)*
        (sphereProbabilityD 24) (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))) := by
  classical
  have hd' := leechGridShrunkSphereFamily24_disjoint g z h γ hh hγ hd
  have hsm : ∀ i, MeasurableSet
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) := fun i =>
    leechGridSpherePatch24_measurable _ _ (gridShrunkCell24_isCompact h γ (z i)).isClosed.measurableSet
      ((image_mono ((gridShrunkCell24_subset_halfOpen h γ hh hγ (z i)).trans
        (gridHalfOpenCell24_subset_closed h (z i)))).trans (hdom i))
  have hhm : ∀ i, MeasurableSet
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))) := fun i =>
    leechGridSpherePatch24_measurable _ _ (gridHalfOpenCell24_measurable h (z i))
      ((image_mono (gridHalfOpenCell24_subset_closed h (z i))).trans (hdom i))
  rw [measure_iUnion hd' hsm,measure_iUnion hd hhm,tsum_fintype,tsum_fintype,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    leechGridShrunkSphereCell24_probability_factor (g i) h γ hh hγ hγ1 (z i) (hdom i))

theorem leechGridShrunkSphereFamily24_probability_real_factor {ι : Type*} [Fintype ι]
    (g : ι → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (z : ι → Fin 24 → ℤ)
    (h γ : ℝ) (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hdom : ∀ i, leechMap '' gridClosedCell24 h (z i) ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i)))
      (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridHalfOpenCell24 h (z j))))) :
    (sphereProbabilityD 24).real (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) =
      (1-γ)^24*(sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))) := by
  rw [Measure.real,leechGridShrunkSphereFamily24_probability_factor g z h γ hh hγ hγ1 hdom hd,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr hγ1) 24)]
  rfl

end SphereGridMass

section SphereShrunkGrid
open Set MeasureTheory

/-! ### SphereShrunkGrid

Construct a near-full separated compact interval-cell family on the actual
unit sphere. A common shrink parameter gives exact physical mass accounting.
This does not yet identify the cells with the uniform affine unit-cube class. -/

theorem leechGridSphereSigma24_disjoint {K : ℕ}
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (U : Fin K → Set (SphereD 24))
    (h : ℝ) (hh : 0 < h) (Z : Fin K → Finset (Fin 24 → ℤ))
    (hdom : ∀ i z, z ∈ Z i → leechMap '' gridClosedCell24 h z ⊆ equalAreaChartDomainD)
    (hU : ∀ i z, z ∈ Z i → equalAreaLeechSpherePatch24 (g i) 0 0 1
      (gridClosedCell24 h z) ⊆ U i)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j))) :
    Pairwise (fun p q : (Σ i : Fin K, Z i) => Disjoint
      (equalAreaLeechSpherePatch24 (g p.1) 0 0 1 (gridHalfOpenCell24 h p.2.val))
      (equalAreaLeechSpherePatch24 (g q.1) 0 0 1 (gridHalfOpenCell24 h q.2.val))) := by
  classical
  rintro ⟨i,z⟩ ⟨j,w⟩ hpq
  by_cases hij : i = j
  · subst j
    have hzw : z.val ≠ w.val := by
      intro he
      exact hpq (by congr 1; exact Subtype.ext he)
    exact leechGridSpherePatch24_disjoint (g i) _ _
      ((image_mono (gridHalfOpenCell24_subset_closed h z.val)).trans (hdom i z.val z.property))
      ((image_mono (gridHalfOpenCell24_subset_closed h w.val)).trans (hdom i w.val w.property))
      (gridHalfOpenCell24_pairwise_disjoint h hh hzw)
  · exact (hd hij).mono
      ((leechGridSpherePatch24_mono _ (gridHalfOpenCell24_subset_closed h z.val)).trans
        (hU i z.val z.property))
      ((leechGridSpherePatch24_mono _ (gridHalfOpenCell24_subset_closed h w.val)).trans
        (hU j w.val w.property))

theorem sphere24_finite_small_chart_grid_flat (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ z : Fin L → Fin 24 → ℤ, ∃ h > 0,
      (∀ i, leechMap '' gridClosedCell24 h (z i) ⊆ equalAreaChartDomainD ∧
        ∀ x ∈ gridClosedCell24 h (z i), ‖leechMap x‖ < a) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i)))
        (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridHalfOpenCell24 h (z j)))) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))) := by
  classical
  obtain ⟨K,g,U,h,hh,Z,hcell,hmass,hd⟩ := sphere24_finite_small_chart_grid a b ha hb
  let I := Σ i : Fin K, Z i
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g' := fun j => g (e.symm j).1
  let z' := fun j => (e.symm j).2.val
  have hdI := leechGridSphereSigma24_disjoint g U h hh Z
    (fun i z hz => ((hcell i).2 z hz).1)
    (fun i z hz => ((hcell i).2 z hz).2.2) hd
  have heq : (⋃ j, equalAreaLeechSpherePatch24 (g' j) 0 0 1 (gridHalfOpenCell24 h (z' j))) =
      ⋃ i, ⋃ z ∈ Z i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h z) := by
    ext q
    constructor
    · intro hq
      obtain ⟨j,hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨(e.symm j).1,mem_iUnion₂.mpr
        ⟨(e.symm j).2.val,(e.symm j).2.property,hj⟩⟩
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      obtain ⟨z,hz,hzq⟩ := mem_iUnion₂.mp hi
      refine mem_iUnion.mpr ⟨e ⟨i,⟨z,hz⟩⟩,?_⟩
      change q ∈ equalAreaLeechSpherePatch24 (g (e.symm (e ⟨i,⟨z,hz⟩⟩)).1) 0 0 1
        (gridHalfOpenCell24 h (e.symm (e ⟨i,⟨z,hz⟩⟩)).2.val)
      rw [e.symm_apply_apply]
      exact hzq
  refine ⟨Fintype.card I,g',z',h,hh,?_,?_,?_⟩
  · intro j
    exact ⟨((hcell (e.symm j).1).2 _ (e.symm j).2.property).1,
      ((hcell (e.symm j).1).2 _ (e.symm j).2.property).2.1⟩
  · intro i j hij
    exact hdI (e.symm.injective.ne hij)
  · simpa only [heq] using hmass

theorem shrinkMass24_loss_budget (b m : ℝ) (hb : 0 < b)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hm : 1-min (b/4) (1/4) < m) :
    ∃ γ > 0, γ < 1 ∧ 1-b < (1-γ)^24*m ∧ (1-γ)^24*m < 1 := by
  let β := min (b/4) (1/4)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβb : β ≤ b/4 := min_le_left _ _
  have hβ1 : β ≤ 1/4 := min_le_right _ _
  let γ := β/48
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hf0 : 0 ≤ (1-γ)^24 := pow_nonneg (by linarith) _
  have hf1 : (1-γ)^24 < 1 := pow_lt_one₀ (by linarith) (by linarith) (by decide)
  have hber : 1-24*γ ≤ (1-γ)^24 := by
    have h := one_add_mul_le_pow (a := -γ) (by linarith : -2 ≤ -γ) 24
    simpa only [Nat.cast_ofNat,mul_neg,← sub_eq_add_neg] using h
  have hproduct := mul_le_mul_of_nonneg_right hber hm0
  have hmul := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 24*γ by positivity)
  have hm' : 1-β < m := hm
  refine ⟨γ,hγ,hγ1,?_,?_⟩
  · dsimp [γ] at hproduct hmul ⊢
    nlinarith
  · exact (mul_le_mul_of_nonneg_left hm1 hf0).trans_lt (by simpa using hf1)

theorem sphere24_near_full_separated_shrunk_grid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ z : Fin L → Fin 24 → ℤ, ∃ h > 0, ∃ γ > 0, γ < 1 ∧
      (∀ i, leechMap '' gridShrunkCell24 h γ (z i) ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridShrunkCell24 h γ (z i), ‖leechMap x‖ < a) ∧
        IsCompact (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)))
        (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridShrunkCell24 h γ (z j)))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)),
        ∀ y ∈ equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridShrunkCell24 h γ (z j)), δ < dist x y) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) ∧
      (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) < 1 := by
  classical
  obtain ⟨L,g,z,h,hh,hcell,hd,hm⟩ := sphere24_finite_small_chart_grid_flat a
    (min (b/4) (1/4)) ha (lt_min (by positivity) (by norm_num))
  let H := ⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))
  obtain ⟨γ,hγ,hγ1,hl,hu⟩ := shrinkMass24_loss_budget b ((sphereProbabilityD 24).real H) hb
    measureReal_nonneg measureReal_le_one hm
  have hs : ∀ i, gridShrunkCell24 h γ (z i) ⊆ gridClosedCell24 h (z i) := fun i =>
    (gridShrunkCell24_subset_halfOpen h γ hh hγ (z i)).trans
      (gridHalfOpenCell24_subset_closed h (z i))
  have hcompact : ∀ i, IsCompact
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) := fun i =>
    leechGridSpherePatch24_isCompact _ _ (gridShrunkCell24_isCompact h γ (z i))
  have hd' := leechGridShrunkSphereFamily24_disjoint g z h γ hh hγ hd
  have heq := leechGridShrunkSphereFamily24_probability_real_factor g z h γ hh hγ hγ1.le
    (fun i => (hcell i).1) hd
  refine ⟨L,g,z,h,hh,γ,hγ,hγ1,?_,hd',
    finite24_compact_disjoint_distance8 _ hcompact hd',?_,?_⟩
  · intro i
    exact ⟨(image_mono (hs i)).trans (hcell i).1,
      fun x hx => (hcell i).2 x (hs i hx),hcompact i⟩
  · rw [heq]; exact hl
  · rw [heq]; exact hu

end SphereShrunkGrid

section CappedSphereGrid
open Set Metric MeasureTheory

/-! ### CappedSphereGrid

The constructed sphere grid can use any prescribed positive mesh cap.
The cap is imposed before floor enumeration, while retaining actual near-full
mass, physical separation and the original closed-cell domain bounds. -/

theorem finite_compact_grid24_capped (η : ℝ) (hη : 0 < η) {ι : Type*} [Fintype ι]
    (k U : ι → Set (Fin 24 → ℝ)) (hk : ∀ i, IsCompact (k i))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, k i ⊆ U i) :
    ∃ h > 0, h < η ∧ ∃ Z : ι → Finset (Fin 24 → ℤ),
      ∀ i, k i ⊆ ⋃ z ∈ Z i, gridHalfOpenCell24 h z ∧
        ∀ z ∈ Z i, gridClosedCell24 h z ⊆ U i := by
  classical
  have hm : ∀ i, ∃ r > 0, thickening r (k i) ⊆ U i := fun i =>
    (hk i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hbuffer using hm
  obtain ⟨δ,hδ,hδr⟩ := finite24_positive_lower_bound8 r hr
  let h := min δ η/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Z : ι → Finset (Fin 24 → ℤ) := fun i => (gridLabel24_image_finite h hh (k i) (hk i)).toFinset
  refine ⟨h,hh,by dsimp [h]; linarith [min_le_right δ η],Z,?_⟩
  intro i
  have hZ : ∀ z, z ∈ Z i ↔ z ∈ gridLabel24 h '' k i := by
    intro z
    exact Set.Finite.mem_toFinset _
  constructor
  · simpa only [hZ] using gridCells24_cover h hh (k i)
  · intro z hz
    apply gridClosedCells24_subset_buffer h (r i) hh ?_ (k i) (U i) (hbuffer i) z ((hZ z).mp hz)
    dsimp [h]
    linarith [hδr i,min_le_left δ η]


theorem sphere24_finite_small_chart_grid_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ U : Fin K → Set (SphereD 24), ∃ h > 0, h < η ∧ ∃ Z : Fin K → Finset (Fin 24 → ℤ),
      (∀ i, IsOpen (U i) ∧ ∀ z ∈ Z i,
        leechMap '' gridClosedCell24 h z ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridClosedCell24 h z, ‖leechMap x‖ < a) ∧
        equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridClosedCell24 h z) ⊆ U i) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, ⋃ z ∈ Z i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h z)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  obtain ⟨K,g,k,ρ,hρ,hk,hmass,hd⟩ := sphere24_finite_small_chart_buffered_cores a b ha hb
  let U : Fin K → Set (SphereD 24) := fun i => thickening ρ (k i)
  have hkh : ∀ i, k i ⊆ equalAreaRotatedHemisphere24 (g i) := by
    intro i q hq
    obtain ⟨u,hu,_,he⟩ := (hk i).2.2.2 q ((hk i).2.2.1 hq)
    exact equalAreaRotatedHemisphere24_of_representation (g i) q u hu he
  let c : Fin K → Set (Fin 24 → ℝ) := fun i =>
    leechCoordinateInverse24 '' (equalAreaRotatedInverse24 (g i) '' k i)
  let V : Fin K → Set (Fin 24 → ℝ) := fun i =>
    leechCoordinateInverse24 '' equalAreaCoordinateBuffer24 (g i) (U i)
  have hc : ∀ i, IsCompact (c i) := fun i =>
    leechCoordinateCore24_isCompact (g i) (k i) (hk i).1 (hkh i)
  have hV : ∀ i, IsOpen (V i) := fun i =>
    leechCoordinateBuffer24_isOpen (g i) (U i) (hk i).2.1
  have hsub : ∀ i, c i ⊆ V i := fun i => image_mono
    (equalAreaCoordinateCore24_subset_buffer (g i) (k i) (U i) (hkh i) (hk i).2.2.1)
  obtain ⟨h,hh,hhη,Z,hgrid⟩ := finite_compact_grid24_capped η hη c V hc hV hsub
  refine ⟨K,g,U,h,hh,hhη,Z,?_,?_,hd⟩
  · intro i
    refine ⟨(hk i).2.1,?_⟩
    intro z hz
    have hcell := (hgrid i).2 z hz
    refine ⟨?_,?_,leechGridSpherePatch24_subset_buffer (g i) _ (U i) hcell⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact (leechCoordinateBuffer24_mem (g i) (U i) x (hcell hx)).1
    · intro x hx
      exact leechCoordinateBuffer24_norm_lt (g i) (U i) a (hk i).2.2.2 x (hcell hx)
  · apply hmass.trans_le
    apply measureReal_mono (μ := (sphereProbabilityD 24)) ?_ (measure_ne_top _ _)
    intro q hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    let x := leechCoordinateInverse24 (equalAreaRotatedInverse24 (g i) q)
    have hx : x ∈ c i := ⟨equalAreaRotatedInverse24 (g i) q,⟨q,hi,rfl⟩,rfl⟩
    obtain ⟨z,hz,hcell⟩ := mem_iUnion₂.mp ((hgrid i).1 hx)
    apply mem_iUnion.mpr
    refine ⟨i,mem_iUnion₂.mpr ⟨z,hz,?_⟩⟩
    refine ⟨x,hcell,?_⟩
    simpa [equalAreaLeechPatch,equalAreaMovingLeechChart,x,leechMap_coordinateInverse8] using
      equalAreaRotatedPhi24_inverse8 (g i) q (hkh i hi)


theorem sphere24_finite_small_chart_grid_flat_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ z : Fin L → Fin 24 → ℤ, ∃ h > 0, h < η ∧
      (∀ i, leechMap '' gridClosedCell24 h (z i) ⊆ equalAreaChartDomainD ∧
        ∀ x ∈ gridClosedCell24 h (z i), ‖leechMap x‖ < a) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i)))
        (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridHalfOpenCell24 h (z j)))) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))) := by
  classical
  obtain ⟨K,g,U,h,hh,hhη,Z,hcell,hmass,hd⟩ := sphere24_finite_small_chart_grid_capped a b η ha hb hη
  let I := Σ i : Fin K, Z i
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g' := fun j => g (e.symm j).1
  let z' := fun j => (e.symm j).2.val
  have hdI := leechGridSphereSigma24_disjoint g U h hh Z
    (fun i z hz => ((hcell i).2 z hz).1)
    (fun i z hz => ((hcell i).2 z hz).2.2) hd
  have heq : (⋃ j, equalAreaLeechSpherePatch24 (g' j) 0 0 1 (gridHalfOpenCell24 h (z' j))) =
      ⋃ i, ⋃ z ∈ Z i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h z) := by
    ext q
    constructor
    · intro hq
      obtain ⟨j,hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨(e.symm j).1,mem_iUnion₂.mpr
        ⟨(e.symm j).2.val,(e.symm j).2.property,hj⟩⟩
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      obtain ⟨z,hz,hzq⟩ := mem_iUnion₂.mp hi
      refine mem_iUnion.mpr ⟨e ⟨i,⟨z,hz⟩⟩,?_⟩
      change q ∈ equalAreaLeechSpherePatch24 (g (e.symm (e ⟨i,⟨z,hz⟩⟩)).1) 0 0 1
        (gridHalfOpenCell24 h (e.symm (e ⟨i,⟨z,hz⟩⟩)).2.val)
      rw [e.symm_apply_apply]
      exact hzq
  refine ⟨Fintype.card I,g',z',h,hh,hhη,?_,?_,?_⟩
  · intro j
    exact ⟨((hcell (e.symm j).1).2 _ (e.symm j).2.property).1,
      ((hcell (e.symm j).1).2 _ (e.symm j).2.property).2.1⟩
  · intro i j hij
    exact hdI (e.symm.injective.ne hij)
  · simpa only [heq] using hmass


theorem sphere24_near_full_separated_shrunk_grid_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ L : ℕ, ∃ g : Fin L → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ z : Fin L → Fin 24 → ℤ, ∃ h > 0, h < η ∧ ∃ γ > 0, γ < 1 ∧
      (∀ i, leechMap '' gridShrunkCell24 h γ (z i) ⊆ equalAreaChartDomainD ∧
        (∀ x ∈ gridShrunkCell24 h γ (z i), ‖leechMap x‖ < a) ∧
        IsCompact (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)))
        (equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridShrunkCell24 h γ (z j)))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)),
        ∀ y ∈ equalAreaLeechSpherePatch24 (g j) 0 0 1 (gridShrunkCell24 h γ (z j)), δ < dist x y) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) ∧
      (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) < 1 := by
  classical
  obtain ⟨L,g,z,h,hh,hhη,hcell,hd,hm⟩ := sphere24_finite_small_chart_grid_flat_capped a
    (min (b/4) (1/4)) η ha (lt_min (by positivity) (by norm_num)) hη
  let H := ⋃ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridHalfOpenCell24 h (z i))
  obtain ⟨γ,hγ,hγ1,hl,hu⟩ := shrinkMass24_loss_budget b ((sphereProbabilityD 24).real H) hb
    measureReal_nonneg measureReal_le_one hm
  have hs : ∀ i, gridShrunkCell24 h γ (z i) ⊆ gridClosedCell24 h (z i) := fun i =>
    (gridShrunkCell24_subset_halfOpen h γ hh hγ (z i)).trans
      (gridHalfOpenCell24_subset_closed h (z i))
  have hcompact : ∀ i, IsCompact
      (equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i))) := fun i =>
    leechGridSpherePatch24_isCompact _ _ (gridShrunkCell24_isCompact h γ (z i))
  have hd' := leechGridShrunkSphereFamily24_disjoint g z h γ hh hγ hd
  have heq := leechGridShrunkSphereFamily24_probability_real_factor g z h γ hh hγ hγ1.le
    (fun i => (hcell i).1) hd
  refine ⟨L,g,z,h,hh,hhη,γ,hγ,hγ1,?_,hd',
    finite24_compact_disjoint_distance8 _ hcompact hd',?_,?_⟩
  · intro i
    exact ⟨(image_mono (hs i)).trans (hcell i).1,
      fun x hx => (hcell i).2 x (hs i hx),hcompact i⟩
  · rw [heq]; exact hl
  · rw [heq]; exact hu

end CappedSphereGrid

section AffineGridCube
open Set MeasureTheory
open Boundary

/-! ### AffineGridCube

Identify the constructed interval cells with the actual common-scale
affine Leech unit-cube class. The original probability, compactness and physical
gap are retained. This constructs the small patch family, not a global node
configuration or its energy estimate. Rational node counts remain separate. -/

def cubeMidpoint24 : Fin 24 → ℝ := fun _ => 1/2

def gridCenter24 (h : ℝ) (z : Fin 24 → ℤ) : Fin 24 → ℝ :=
  fun i => h*((z i : ℝ)+1/2)

def gridCubeParam24 (h γ : ℝ) (z : Fin 24 → ℤ) (x : Fin 24 → ℝ) : Fin 24 → ℝ :=
  gridCenter24 h z+(h*(1-γ)) • (x-cubeMidpoint24)

theorem cubeMidpoint24_mem_unitCube : cubeMidpoint24 ∈ UnitCube 24 := by
  intro i
  norm_num [cubeMidpoint24]

theorem gridCenter24_mem_shrunk (h γ : ℝ) (hh : 0 ≤ h) (hγ : γ ≤ 1)
    (z : Fin 24 → ℤ) : gridCenter24 h z ∈ gridShrunkCell24 h γ z := by
  intro i
  dsimp [gridCenter24]
  have hg : h*γ ≤ h := by nlinarith
  constructor <;> nlinarith

theorem gridCubeParam24_image_unitCube (h γ : ℝ) (hh : 0 < h) (hγ : γ < 1)
    (z : Fin 24 → ℤ) : gridCubeParam24 h γ z '' UnitCube 24 = gridShrunkCell24 h γ z := by
  have hl : 0 < h*(1-γ) := by positivity
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ i
    change h*((z i : ℝ)+γ/2) ≤ h*((z i : ℝ)+1/2)+h*(1-γ)*(x i-1/2) ∧
      h*((z i : ℝ)+1/2)+h*(1-γ)*(x i-1/2) ≤ h*((z i : ℝ)+1-γ/2)
    have hi := hx i
    have hlo := mul_nonneg hl.le hi.1
    have hhi := mul_nonneg hl.le (sub_nonneg.mpr hi.2)
    constructor <;> nlinarith
  · intro hy
    let x : Fin 24 → ℝ := fun i => (y i-gridCenter24 h z i)/(h*(1-γ))+1/2
    have hx : x ∈ UnitCube 24 := by
      intro i
      have lo : -(1/2) ≤ (y i-gridCenter24 h z i)/(h*(1-γ)) :=
        (le_div_iff₀ hl).mpr (by dsimp [gridCenter24]; nlinarith [(hy i).1])
      have hi : (y i-gridCenter24 h z i)/(h*(1-γ)) ≤ 1/2 :=
        (div_le_iff₀ hl).mpr (by dsimp [gridCenter24]; nlinarith [(hy i).2])
      change 0 ≤ (y i-gridCenter24 h z i)/(h*(1-γ))+1/2 ∧
        (y i-gridCenter24 h z i)/(h*(1-γ))+1/2 ≤ 1
      constructor <;> linarith
    refine ⟨x,hx,?_⟩
    funext i
    change gridCenter24 h z i+h*(1-γ)*
      ((y i-gridCenter24 h z i)/(h*(1-γ))+1/2-1/2) = y i
    field_simp [hh.ne', (sub_pos.mpr hγ).ne']
    <;> ring

theorem equalAreaLeechGridCube24_affine_identity (h γ : ℝ) (z : Fin 24 → ℤ)
    (x : Fin 24 → ℝ) :
    leechMap (gridCubeParam24 h γ z x) =
      equalAreaLeechAffine24 (leechMap (gridCenter24 h z)) cubeMidpoint24 (h*(1-γ)) x := by
  simp [gridCubeParam24,equalAreaLeechAffine24]

theorem equalAreaLeechGridCube24_patch_identity (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (h γ : ℝ) (z : Fin 24 → ℤ) (x : Fin 24 → ℝ) :
    equalAreaLeechPatch g 0 0 1 (gridCubeParam24 h γ z x) =
      equalAreaLeechPatch g (leechMap (gridCenter24 h z)) cubeMidpoint24 (h*(1-γ)) x := by
  simp [equalAreaLeechPatch,equalAreaMovingLeechChart,gridCubeParam24]

theorem gridShrunkSphere24_eq_affineCube (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (h γ : ℝ) (hh : 0 < h) (hγ : γ < 1) (z : Fin 24 → ℤ) :
    equalAreaLeechSpherePatch24 g 0 0 1 (gridShrunkCell24 h γ z) =
      equalAreaLeechSpherePatch24 g (leechMap (gridCenter24 h z)) cubeMidpoint24
        (h*(1-γ)) (UnitCube 24) := by
  have hf : (fun x => equalAreaLeechPatch g 0 0 1 (gridCubeParam24 h γ z x)) =
      equalAreaLeechPatch g (leechMap (gridCenter24 h z)) cubeMidpoint24 (h*(1-γ)) := by
    funext x
    exact equalAreaLeechGridCube24_patch_identity g h γ z x
  simp only [equalAreaLeechSpherePatch24,← gridCubeParam24_image_unitCube h γ hh hγ z,
    image_image,hf]

theorem equalAreaLeechCubeUnion24_probability_real {K : ℕ}
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin K → Fin 24 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 24)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius24 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) (c i) ε (UnitCube 24))
      (equalAreaLeechSpherePatch24 (g j) (v j) (c j) ε (UnitCube 24)))) :
    (sphereProbabilityD 24).real
      (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) (c i) ε (UnitCube 24)) =
      (K : ℝ)*(ε^24/(sphereAreaD 24).real univ) := by
  change (sphereProbabilityD 24).real (equalAreaLeechPatchUnion24 g v c (fun _ => ε)
    (fun _ => UnitCube 24)) = _
  have hden : 0 ≤ ε^24/(sphereAreaD 24).real univ :=
    (equalAreaLeechPatchProbabilityDensity24_pos ε hε).le
  rw [Measure.real,equalAreaLeechCubeUnion24_probability g v c ε hε hc hsmall hd,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hden]

theorem sphere24_near_full_small_affine_cubes (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ v : Fin K → Fin 24 → ℝ, ∃ ε > 0, ε*equalAreaScaleRadius24 ≤ ρ ∧
      (∀ i, ‖v i‖ ≤ ρ ∧ ‖v i‖+ε*equalAreaScaleRadius24 ≤ 1/8 ∧
        IsCompact (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24))
        (equalAreaLeechSpherePatch24 (g j) (v j) cubeMidpoint24 ε (UnitCube 24))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24),
        ∀ y ∈ equalAreaLeechSpherePatch24 (g j) (v j) cubeMidpoint24 ε (UnitCube 24), δ < dist x y) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24)) ∧
      (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24)) < 1 ∧
      (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24)) =
        (K : ℝ)*(ε^24/(sphereAreaD 24).real univ) := by
  let a := min ρ (1/16)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have haρ : a ≤ ρ/2 := by
    dsimp [a]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have ha1 : a ≤ 1/32 := by dsimp [a]; linarith [min_le_right ρ (1/16)]
  have hR := equalAreaScaleRadius24_pos
  obtain ⟨K,g,z,h,hh,hhcap,γ,hγ,hγ1,hcell,hd,hgap,hl,hu⟩ :=
    sphere24_near_full_separated_shrunk_grid_capped a b (a/equalAreaScaleRadius24)
      ha hb (by positivity)
  let ε := h*(1-γ)
  let v : Fin K → Fin 24 → ℝ := fun i => leechMap (gridCenter24 h (z i))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : ε*equalAreaScaleRadius24 < a := by
    have heh : ε ≤ h := by dsimp [ε]; nlinarith
    exact (mul_le_mul_of_nonneg_right heh hR.le).trans_lt ((lt_div_iff₀ hR).mp hhcap)
  have hv : ∀ i, ‖v i‖ < a := fun i =>
    (hcell i).2.1 _ (gridCenter24_mem_shrunk h γ hh.le hγ1.le (z i))
  have hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius24 ≤ 1/8 := by
    intro i
    linarith [hv i]
  have heq : ∀ i, equalAreaLeechSpherePatch24 (g i) 0 0 1 (gridShrunkCell24 h γ (z i)) =
      equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24) := fun i =>
    gridShrunkSphere24_eq_affineCube (g i) h γ hh hγ1 (z i)
  have hd' : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24))
      (equalAreaLeechSpherePatch24 (g j) (v j) cubeMidpoint24 ε (UnitCube 24))) := by
    simpa only [heq] using hd
  refine ⟨K,g,v,ε,hε,by linarith,?_,hd',?_,?_,?_,
    equalAreaLeechCubeUnion24_probability_real g v (fun _ => cubeMidpoint24) ε hε
      (fun _ => cubeMidpoint24_mem_unitCube) hsmall hd'⟩
  · intro i
    exact ⟨by linarith [hv i],hsmall i,
      equalAreaLeechSpherePatch24_cube_isCompact (g i) (v i) cubeMidpoint24 ε hε
        cubeMidpoint24_mem_unitCube (hsmall i)⟩
  · simpa only [heq] using hgap
  · simpa only [heq] using hl
  · simpa only [heq] using hu

end AffineGridCube

section RationalScale
open Set MeasureTheory
open Boundary

/-! ### RationalScale

Normalize the common physical side length by the twenty-fourth root of the actual
sphere area. A positive rational normalized length gives exact rational patch
probabilities. Shrinking about the cube midpoint preserves physical inclusion;
no new covering or separation theorem is required. -/

def equalAreaLeechNormalizedScale24 (t : ℝ) : ℝ := leechUnitDensityRadius24*t

def centeredCubeRescale24 (t : ℝ) (x : Fin 24 → ℝ) : Fin 24 → ℝ :=
  cubeMidpoint24+t • (x-cubeMidpoint24)

theorem equalAreaLeechNormalizedScale24_density (t : ℝ) :
    (equalAreaLeechNormalizedScale24 t)^24/(sphereAreaD 24).real univ = t^24 := by
  have hA : (sphereAreaD 24).real univ ≠ 0 := (sphereAreaD_univ_pos 24).ne'
  rw [equalAreaLeechNormalizedScale24,mul_pow,leechUnitDensityRadius24_pow,mul_div_cancel_left₀ _ hA]

theorem exists_positive_nat_fraction_btwn24 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ a < (p : ℝ)/q ∧ (p : ℝ)/q < b := by
  obtain ⟨r,hrl,hru⟩ := exists_rat_btwn hab
  have hr : 0 < r := by exact_mod_cast (ha.trans hrl)
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have heq : (r : ℝ) = (r.num.natAbs : ℝ)/r.den := by
    rw [Rat.cast_def,← Int.natAbs_of_nonneg hn.le]
    simp
  exact ⟨r.num.natAbs,r.den,Int.natAbs_pos.mpr hn.ne',r.den_pos,
    by simpa only [heq] using hrl,by simpa only [heq] using hru⟩

theorem centeredCubeRescale24_mem_unitCube (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (x : Fin 24 → ℝ) (hx : x ∈ UnitCube 24) : centeredCubeRescale24 t x ∈ UnitCube 24 := by
  intro i
  change 0 ≤ 1/2+t*(x i-1/2) ∧ 1/2+t*(x i-1/2) ≤ 1
  have hlo := mul_nonneg ht (hx i).1
  have hhi := mul_nonneg ht (sub_nonneg.mpr (hx i).2)
  constructor <;> nlinarith

theorem equalAreaLeechPatch_smaller_scale_identity
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v : Fin 24 → ℝ)
    (ε ℓ : ℝ) (hε : ε ≠ 0) (x : Fin 24 → ℝ) :
    equalAreaLeechPatch g v cubeMidpoint24 ε (centeredCubeRescale24 (ℓ/ε) x) =
      equalAreaLeechPatch g v cubeMidpoint24 ℓ x := by
  have hx : centeredCubeRescale24 (ℓ/ε) x-cubeMidpoint24 =
      (ℓ/ε) • (x-cubeMidpoint24) := by simp [centeredCubeRescale24]
  simp only [equalAreaLeechPatch,equalAreaMovingLeechChart,hx,map_smul,smul_smul]
  rw [mul_div_cancel₀ ℓ hε]

theorem equalAreaLeechSphereCube24_scale_mono
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v : Fin 24 → ℝ)
    (ε ℓ : ℝ) (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hle : ℓ ≤ ε) :
    equalAreaLeechSpherePatch24 g v cubeMidpoint24 ℓ (UnitCube 24) ⊆
      equalAreaLeechSpherePatch24 g v cubeMidpoint24 ε (UnitCube 24) := by
  rintro y ⟨x,hx,hxy⟩
  refine ⟨centeredCubeRescale24 (ℓ/ε) x,
    centeredCubeRescale24_mem_unitCube _ (div_nonneg hℓ hε.le)
      ((div_le_one hε).mpr hle) x hx,?_⟩
  rw [equalAreaLeechPatch_smaller_scale_identity g v ε ℓ hε.ne']
  exact hxy

theorem normalizedCubeMass24_integer_budget (K p q : ℕ) (hq : 0 < q)
    (hm : (K : ℝ)*((p : ℝ)/q)^24 < 1) : K*p^24 < q^24 := by
  have hq24 : 0 < (q : ℝ)^24 := by positivity
  have h : (K : ℝ)*(p : ℝ)^24 < (q : ℝ)^24 := by
    apply (div_lt_one hq24).mp
    simpa only [div_pow,mul_div_assoc] using hm
  exact_mod_cast h

theorem equalAreaLeechSphereCube24_normalized_probability_real
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v : Fin 24 → ℝ) (t : ℝ) (ht : 0 < t)
    (hsmall : ‖v‖+equalAreaLeechNormalizedScale24 t*equalAreaScaleRadius24 ≤ 1/8) :
    (sphereProbabilityD 24).real
      (equalAreaLeechSpherePatch24 g v cubeMidpoint24 (equalAreaLeechNormalizedScale24 t) (UnitCube 24)) = t^24 := by
  have he : 0 < equalAreaLeechNormalizedScale24 t := mul_pos leechUnitDensityRadius24_pos ht
  rw [equalAreaLeechSpherePatch24_probability_real g v cubeMidpoint24 _ he _
    (unitCube_measurableSet 24)
    (equalAreaLeechAffine24_cube_domain v cubeMidpoint24 _ he cubeMidpoint24_mem_unitCube hsmall)]
  rw [Measure.real,unitCube_volume,ENNReal.toReal_one,mul_one]
  exact equalAreaLeechNormalizedScale24_density t

end RationalScale

section RationalCubeFamily
open Set MeasureTheory
open Boundary

/-! ### RationalCubeFamily

Construct the rationally normalized common-scale family of Leech cube patches on S²⁴,
retaining near-full sphere probability, uniform smallness and the original physical gap.
Every patch has probability exactly `(p/q)²⁴`, and `K p²⁴ < q²⁴`.  No residual points, global
configuration or energy bound is asserted. -/

theorem sphere24_near_full_rational_affine_cubes (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∃ v : Fin K → Fin 24 → ℝ, ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ∃ ℓ > 0, ℓ = equalAreaLeechNormalizedScale24 ((p : ℝ)/q) ∧
      ℓ*equalAreaScaleRadius24 ≤ ρ ∧
      (∀ i, ‖v i‖ ≤ ρ ∧ ‖v i‖+ℓ*equalAreaScaleRadius24 ≤ 1/8 ∧
        IsCompact (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24))
        (equalAreaLeechSpherePatch24 (g j) (v j) cubeMidpoint24 ℓ (UnitCube 24))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24),
        ∀ y ∈ equalAreaLeechSpherePatch24 (g j) (v j) cubeMidpoint24 ℓ (UnitCube 24), δ < dist x y) ∧
      1-b < (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) ∧
      (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) < 1 ∧
      (sphereProbabilityD 24).real
        (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) =
        (K : ℝ)*((p : ℝ)/q)^24 ∧
      (∀ i, (sphereProbabilityD 24).real
        (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) = ((p : ℝ)/q)^24) ∧
      K*p^24 < q^24 := by
  obtain ⟨K,g,v,ε,hε,hscale,hcell,hd,hgap,hl,hu,heq⟩ :=
    sphere24_near_full_small_affine_cubes ρ (min (b/4) (1/4)) hρ
      (lt_min (by positivity) (by norm_num))
  let H := ⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24)
  let w := (sphereProbabilityD 24).real H
  have hw : w = (K : ℝ)*(ε^24/(sphereAreaD 24).real univ) := heq
  obtain ⟨γ,hγ,hγ1,hkeep,_⟩ := shrinkMass24_loss_budget b w hb
    measureReal_nonneg hu.le hl
  have hR := leechUnitDensityRadius24_pos
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hlow : 0 < (1-γ)*ε/leechUnitDensityRadius24 := by positivity
  have hinterval : (1-γ)*ε/leechUnitDensityRadius24 < ε/leechUnitDensityRadius24 := by
    apply div_lt_div_of_pos_right _ hR
    nlinarith
  obtain ⟨p,q,hp,hq,hrl,hru⟩ := exists_positive_nat_fraction_btwn24 _ _ hlow hinterval
  let ℓ := equalAreaLeechNormalizedScale24 ((p : ℝ)/q)
  have ht : 0 < (p : ℝ)/q := by positivity
  have hℓ : 0 < ℓ := mul_pos hR ht
  have hℓε : ℓ < ε := by
    simpa only [ℓ,equalAreaLeechNormalizedScale24,mul_comm] using (lt_div_iff₀ hR).mp hru
  have hℓlo : (1-γ)*ε < ℓ := by
    simpa only [ℓ,equalAreaLeechNormalizedScale24,mul_comm] using (div_lt_iff₀ hR).mp hrl
  have hsmall : ∀ i, ‖v i‖+ℓ*equalAreaScaleRadius24 ≤ 1/8 := by
    intro i
    have he := mul_le_mul_of_nonneg_right hℓε.le equalAreaScaleRadius24_pos.le
    linarith [(hcell i).2.1]
  have hsub : ∀ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24) ⊆
      equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ε (UnitCube 24) := fun i =>
    equalAreaLeechSphereCube24_scale_mono (g i) (v i) ε ℓ hε hℓ.le hℓε.le
  have hd' : Pairwise (fun i j => Disjoint
      (equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24))
      (equalAreaLeechSpherePatch24 (g j) (v j) cubeMidpoint24 ℓ (UnitCube 24))) :=
    fun i j hij => (hd hij).mono (hsub i) (hsub j)
  have hmass := equalAreaLeechCubeUnion24_probability_real g v (fun _ => cubeMidpoint24) ℓ hℓ
    (fun _ => cubeMidpoint24_mem_unitCube) hsmall hd'
  have hmass' : (sphereProbabilityD 24).real
      (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) =
      (K : ℝ)*((p : ℝ)/q)^24 := by
    rw [hmass]
    change (K : ℝ)*((equalAreaLeechNormalizedScale24 ((p : ℝ)/q))^24/(sphereAreaD 24).real univ) = _
    rw [equalAreaLeechNormalizedScale24_density]
  have hupper : (sphereProbabilityD 24).real
      (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) < 1 :=
    (measureReal_mono (iUnion_mono hsub) (measure_ne_top _ _)).trans_lt hu
  have hlower : 1-b < (sphereProbabilityD 24).real
      (⋃ i, equalAreaLeechSpherePatch24 (g i) (v i) cubeMidpoint24 ℓ (UnitCube 24)) := by
    apply hkeep.trans_le
    calc
      (1-γ)^24*w = (K : ℝ)*(((1-γ)*ε)^24/(sphereAreaD 24).real univ) := by
        rw [hw,mul_pow]
        ring
      _ ≤ (K : ℝ)*(ℓ^24/(sphereAreaD 24).real univ) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hℓlo.le 24) hA.le) (Nat.cast_nonneg _)
      _ = _ := hmass.symm
  have hbudget : K*p^24 < q^24 := normalizedCubeMass24_integer_budget K p q hq
    (by simpa only [hmass'] using hupper)
  refine ⟨K,g,v,p,q,hp,hq,ℓ,hℓ,rfl,
    (mul_le_mul_of_nonneg_right hℓε.le equalAreaScaleRadius24_pos.le).trans hscale,
    ?_,hd',?_,hlower,hupper,hmass',?_,hbudget⟩
  · intro i
    exact ⟨(hcell i).1,hsmall i,
      equalAreaLeechSpherePatch24_cube_isCompact (g i) (v i) cubeMidpoint24 ℓ hℓ
        cubeMidpoint24_mem_unitCube (hsmall i)⟩
  · obtain ⟨δ,hδ,hsep⟩ := hgap
    exact ⟨δ,hδ,fun i j hij x hx y hy => hsep i j hij x (hsub i hx) y (hsub j hy)⟩
  · intro i
    exact equalAreaLeechSphereCube24_normalized_probability_real (g i) (v i) _ ht (hsmall i)

end RationalCubeFamily

end SphericalRiesz
