import Riesz.EqualAreaPatchTransport8
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Data.Finset.Lattice.Fold

/-! Compactness of actual physical patches and common positive separation
for a given finite disjoint compact family. The open buffers need not lie
inside the compact cores: cores can have empty interior. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem equalAreaE8SpherePatch8_cube_isCompact (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    IsCompact (equalAreaE8SpherePatch8 g v c ε (UnitCube 8)) := by
  let : CompactSpace (UnitCube 8) := isCompact_iff_compactSpace.mp (unitCube_isCompact 8)
  rw [← equalAreaE8CubeEmbedding8_range g v c ε hε hc hsmall]
  exact isCompact_range (equalAreaE8CubeEmbedding8_continuous g v c ε hε hc hsmall)

theorem equalAreaE8SpherePatch8_isCompact (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8)
    (s : Set (Fin 8 → ℝ)) (hs : IsCompact s) (hsc : s ⊆ UnitCube 8) :
    IsCompact (equalAreaE8SpherePatch8 g v c ε s) := by
  let : CompactSpace (UnitCube 8) := isCompact_iff_compactSpace.mp (unitCube_isCompact 8)
  have himage : Subtype.val '' (Subtype.val ⁻¹' s : Set (UnitCube 8)) = s := by
    rw [image_preimage_eq_inter_range,Subtype.range_coe,inter_eq_left.mpr hsc]
  rw [← himage,← equalAreaE8CubeEmbedding8_image g v c ε hε hc hsmall]
  exact (hs.isClosed.preimage continuous_subtype_val).isCompact.image
    (equalAreaE8CubeEmbedding8_continuous g v c ε hε hc hsmall)

theorem finite_positive_lower_bound8 {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ δ > 0, ∀ i, δ ≤ r i := by
  classical
  let f : Option ι → ℝ := fun i => i.elim 1 r
  have hne : (Finset.univ : Finset (Option ι)).Nonempty := ⟨none,Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f,?_,?_⟩
  · change (0 : ℝ) < Finset.univ.inf' hne f
    apply (Finset.lt_inf'_iff hne).mpr
    intro i _
    cases i with
    | none => exact zero_lt_one
    | some i => exact hr i
  · intro i
    exact Finset.inf'_le f (Finset.mem_univ (some i))

theorem compact_disjoint_distance8 (s t : Set Sphere8)
    (hs : IsCompact s) (ht : IsCompact t) (hd : Disjoint s t) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ t, δ < dist x y := by
  obtain ⟨r,hr,h⟩ := exists_pos_forall_lt_edist hs ht.isClosed hd
  refine ⟨r,NNReal.coe_pos.mpr hr,?_⟩
  intro x hx y hy
  have hn : r < nndist x y := by
    simpa only [edist_nndist,ENNReal.coe_lt_coe] using h x hx y hy
  exact hn

theorem finite_compact_disjoint_distance8 {K : ℕ} (s : Fin K → Set Sphere8)
    (hs : ∀ i, IsCompact (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ δ > 0, ∀ i j, i ≠ j → ∀ x ∈ s i, ∀ y ∈ s j, δ < dist x y := by
  classical
  have h : ∀ p : Fin K × Fin K, ∃ r > 0,
      p.1 ≠ p.2 → ∀ x ∈ s p.1, ∀ y ∈ s p.2, r < dist x y := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1,zero_lt_one,fun hne => (hne hp).elim⟩
    · obtain ⟨r,hr,hb⟩ := compact_disjoint_distance8 _ _ (hs p.1) (hs p.2) (hd hp)
      exact ⟨r,hr,fun _ => hb⟩
  choose r hr hb using h
  obtain ⟨δ,hδ,hle⟩ := finite_positive_lower_bound8 r hr
  exact ⟨δ,hδ,fun i j hij x hx y hy => (hle (i,j)).trans_lt (hb (i,j) hij x hx y hy)⟩

theorem finite_compact_disjoint_thickenings8 {K : ℕ} (s : Fin K → Set Sphere8)
    (hs : ∀ i, IsCompact (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ ρ > 0, Pairwise (fun i j => Disjoint (thickening ρ (s i)) (thickening ρ (s j))) := by
  obtain ⟨δ,hδ,hsep⟩ := finite_compact_disjoint_distance8 s hs hd
  refine ⟨δ/3,by positivity,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hz hzj
  obtain ⟨x,hx,hzx⟩ := mem_thickening_iff.mp hz
  obtain ⟨y,hy,hzy⟩ := mem_thickening_iff.mp hzj
  have hl := hsep i j hij x hx y hy
  have ht := dist_triangle_left x y z
  linarith

theorem finite_compact_chart_buffers8 {K : ℕ} (s U : Fin K → Set Sphere8)
    (hs : ∀ i, IsCompact (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, s i ⊆ U i) :
    ∃ ρ > 0, (∀ i, IsOpen (thickening ρ (s i)) ∧ s i ⊆ thickening ρ (s i) ∧
      thickening ρ (s i) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (s i)) (thickening ρ (s j))) := by
  classical
  obtain ⟨δ,hδ,hdis⟩ := finite_compact_disjoint_thickenings8 s hs hd
  have h : ∀ i, ∃ r > 0, thickening r (s i) ⊆ U i := fun i =>
    (hs i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hb using h
  obtain ⟨η,hη,hle⟩ := finite_positive_lower_bound8 r hr
  refine ⟨min δ η,lt_min hδ hη,?_,?_⟩
  · intro i
    exact ⟨isOpen_thickening,self_subset_thickening (lt_min hδ hη) _,
      (thickening_mono ((min_le_right δ η).trans (hle i)) _).trans (hb i)⟩
  · intro i j hij
    exact (hdis hij).mono (thickening_mono (min_le_left δ η) _)
      (thickening_mono (min_le_left δ η) _)

theorem equalAreaE8CubeFamily8_separated {K : ℕ}
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : Fin K → Fin 8 → ℝ)
    (e : Fin K → ℝ) (he : ∀ i, 0 < e i) (hc : ∀ i, c i ∈ UnitCube 8)
    (hsmall : ∀ i, ‖v i‖+e i*equalAreaScaleRadius ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) (c i) (e i) (UnitCube 8))
      (equalAreaE8SpherePatch8 (g j) (v j) (c j) (e j) (UnitCube 8)))) :
    ∃ δ > 0, ∀ i j, i ≠ j →
      ∀ x ∈ equalAreaE8SpherePatch8 (g i) (v i) (c i) (e i) (UnitCube 8),
      ∀ y ∈ equalAreaE8SpherePatch8 (g j) (v j) (c j) (e j) (UnitCube 8), δ < dist x y :=
  finite_compact_disjoint_distance8 _ (fun i =>
    equalAreaE8SpherePatch8_cube_isCompact (g i) (v i) (c i) (e i) (he i) (hc i) (hsmall i)) hd

end SphericalRiesz
