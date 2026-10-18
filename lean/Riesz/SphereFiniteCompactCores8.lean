import Riesz.EqualAreaFinitePatchGeometry8
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.Disjointed
import Mathlib.Data.Fintype.EquivFin

/-! Any supplied finite measurable sphere cover admits compact cores with
arbitrarily small lost probability. For an open cover, the cores have a
common positive buffer inside the original cover and disjoint buffers.
This is an actual probability-measure existence theorem, not yet an E8
chart atlas or a finite equal-scale cube extraction theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace SphericalRiesz

theorem sphereProbability8_compact_core (s : Set Sphere8) (hs : MeasurableSet s)
    (b : ℝ) (hb : 0 < b) :
    ∃ k ⊆ s, IsCompact k ∧ sphereProbability8 (s \ k) < ENNReal.ofReal b := by
  have hS : IsClosed (Sphere8 : Set Ambient9) := isClosed_sphere
  let : PolishSpace Sphere8 := hS.polishSpace
  exact hs.exists_isCompact_sdiff_lt (measure_ne_top sphereProbability8 s)
    (ENNReal.ofReal_pos.mpr hb).ne'

theorem sphereFiniteCover8_residual_le {K : ℕ} (s k : Fin K → Set Sphere8)
    (hcover : (⋃ i, s i) = univ) :
    sphereProbability8 (⋃ i, k i)ᶜ ≤ ∑ i : Fin K, sphereProbability8 (s i \ k i) := by
  have hsub : (⋃ i, k i)ᶜ ⊆ ⋃ i, s i \ k i := by
    intro x hx
    have hxcover : x ∈ ⋃ i, s i := hcover.symm ▸ mem_univ x
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxcover
    exact mem_iUnion.mpr ⟨i,hi,fun hki => hx (mem_iUnion.mpr ⟨i,hki⟩)⟩
  have hsum : sphereProbability8 (⋃ i, s i \ k i) ≤
      ∑ i : Fin K, sphereProbability8 (s i \ k i) := by
    simpa only [tsum_fintype] using
      (measure_iUnion_le (μ := sphereProbability8) (fun i : Fin K => s i \ k i))
  exact (measure_mono hsub).trans hsum

theorem sphereFiniteCover8_compact_cores {K : ℕ} (s : Fin K → Set Sphere8)
    (hs : ∀ i, MeasurableSet (s i)) (hcover : (⋃ i, s i) = univ)
    (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set Sphere8, (∀ i, k i ⊆ s i) ∧ (∀ i, IsCompact (k i)) ∧
      sphereProbability8 (⋃ i, k i)ᶜ < ENNReal.ofReal b := by
  classical
  let a : ℝ := b/((K : ℝ)+1)
  have ha : 0 < a := div_pos hb (by positivity)
  have h : ∀ i, ∃ k ⊆ s i, IsCompact k ∧ sphereProbability8 (s i \ k) < ENNReal.ofReal a :=
    fun i => sphereProbability8_compact_core (s i) (hs i) a ha
  choose k hsub hcompact hloss using h
  refine ⟨k,hsub,hcompact,?_⟩
  have hab : (K : ℝ)*a < b := by
    have he : ((K : ℝ)+1)*a = b := by
      dsimp [a]
      field_simp
    nlinarith
  calc
    sphereProbability8 (⋃ i, k i)ᶜ ≤ ∑ i, sphereProbability8 (s i \ k i) :=
      sphereFiniteCover8_residual_le s k hcover
    _ ≤ ∑ _i : Fin K, ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => (hloss i).le)
    _ = ENNReal.ofReal ((K : ℝ)*a) := by
      simp [ENNReal.ofReal_mul]
    _ < ENNReal.ofReal b := (ENNReal.ofReal_lt_ofReal_iff hb).mpr hab

theorem sphereFiniteCover8_disjoint_partition {K : ℕ} (U : Fin K → Set Sphere8)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : (⋃ i, U i) = univ) :
    ∃ s : Fin K → Set Sphere8, (∀ i, MeasurableSet (s i)) ∧ (∀ i, s i ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ := by
  refine ⟨disjointed U,?_,fun i => disjointed_subset U i,disjoint_disjointed U,?_⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hU i).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun (_h : j < i) => (hU j).compl)
  · rw [iUnion_disjointed,hcover]

theorem sphereFinitePartition8_separated_cores {K : ℕ} (s : Fin K → Set Sphere8)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) = univ) (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set Sphere8, ∃ δ > 0,
      (∀ i, k i ⊆ s i ∧ IsCompact (k i)) ∧
      sphereProbability8 (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      (∀ i j, i ≠ j → ∀ x ∈ k i, ∀ y ∈ k j, δ < dist x y) := by
  obtain ⟨k,hsub,hcomp,hloss⟩ := sphereFiniteCover8_compact_cores s hs hcover b hb
  have hkd : Pairwise (fun i j => Disjoint (k i) (k j)) :=
    fun i j hij => (hd hij).mono (hsub i) (hsub j)
  obtain ⟨δ,hδ,hsep⟩ := finite_compact_disjoint_distance8 k hcomp hkd
  exact ⟨k,δ,hδ,fun i => ⟨hsub i,hcomp i⟩,hloss,hsep⟩

theorem sphereFiniteOpenCover8_buffered_cores {K : ℕ} (U : Fin K → Set Sphere8)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) (b : ℝ) (hb : 0 < b) :
    ∃ k : Fin K → Set Sphere8, ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ U i ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ U i) ∧
      sphereProbability8 (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨s,hsm,hss,hsd,hscov⟩ := sphereFiniteCover8_disjoint_partition U
    (fun i => (hU i).measurableSet) hcover
  obtain ⟨k,hks,hcomp,hloss⟩ := sphereFiniteCover8_compact_cores s hsm hscov b hb
  have hkd : Pairwise (fun i j => Disjoint (k i) (k j)) :=
    fun i j hij => (hsd hij).mono (hks i) (hks j)
  have hkU : ∀ i, k i ⊆ U i := fun i => (hks i).trans (hss i)
  obtain ⟨ρ,hρ,hbuf,hdis⟩ := finite_compact_chart_buffers8 k U hcomp hkd hU hkU
  exact ⟨k,ρ,hρ,fun i => ⟨hcomp i,hkU i,hbuf i⟩,hloss,hdis⟩

theorem sphere8_finite_ball_cover (r : ℝ) (hr : 0 < r) :
    ∃ K : ℕ, ∃ p : Fin K → Sphere8, (⋃ i, ball (p i) r) = univ := by
  classical
  let : CompactSpace Sphere8 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient9) 1)
  obtain ⟨t,ht⟩ := (isCompact_univ : IsCompact (univ : Set Sphere8)).elim_finite_subcover
    (fun p : Sphere8 => ball p r) (fun _ => isOpen_ball)
    (fun p _ => mem_iUnion.mpr ⟨p,mem_ball_self hr⟩)
  let p : Fin t.card → Sphere8 := fun i => (t.equivFin.symm i).val
  refine ⟨t.card,p,?_⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨y,hy⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨t.equivFin ⟨y,hyt⟩,by simpa only [p,Equiv.symm_apply_apply] using hxy⟩

theorem sphere8_finite_ball_buffered_cores (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ K : ℕ, ∃ p : Fin K → Sphere8, ∃ k : Fin K → Set Sphere8, ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ ball (p i) r ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ ball (p i) r) ∧
      sphereProbability8 (⋃ i, k i)ᶜ < ENNReal.ofReal b ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨K,p,hcover⟩ := sphere8_finite_ball_cover r hr
  obtain ⟨k,ρ,hρ,hk,hloss,hd⟩ := sphereFiniteOpenCover8_buffered_cores
    (fun i => ball (p i) r) (fun _ => isOpen_ball) hcover b hb
  exact ⟨K,p,k,ρ,hρ,hk,hloss,hd⟩

theorem sphereProbability8_mass_of_residual (s : Set Sphere8) (hs : MeasurableSet s)
    (b : ℝ) (hb : 0 < b) (hloss : sphereProbability8 sᶜ < ENNReal.ofReal b) :
    1-b < sphereProbability8.real s := by
  have h := (ENNReal.toReal_lt_toReal (measure_ne_top sphereProbability8 sᶜ)
    ENNReal.ofReal_ne_top).mpr hloss
  rw [ENNReal.toReal_ofReal hb.le] at h
  change sphereProbability8.real sᶜ < b at h
  rw [measureReal_compl hs,probReal_univ] at h
  linarith

theorem sphere8_finite_ball_buffered_cores_mass (r b : ℝ) (hr : 0 < r) (hb : 0 < b) :
    ∃ K : ℕ, ∃ p : Fin K → Sphere8, ∃ k : Fin K → Set Sphere8, ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ k i ⊆ ball (p i) r ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧ thickening ρ (k i) ⊆ ball (p i) r) ∧
      1-b < sphereProbability8.real (⋃ i, k i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  obtain ⟨K,p,k,ρ,hρ,hk,hloss,hd⟩ := sphere8_finite_ball_buffered_cores r b hr hb
  exact ⟨K,p,k,ρ,hρ,hk,sphereProbability8_mass_of_residual _
    (MeasurableSet.iUnion fun i => (hk i).1.measurableSet) b hb hloss,hd⟩

end SphericalRiesz
