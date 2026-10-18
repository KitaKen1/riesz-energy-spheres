import Riesz.SphereShrunkGrid8

/-! The constructed sphere grid can use any prescribed positive mesh cap.
The cap is imposed before floor enumeration, while retaining actual near-full
mass, physical separation and the original closed-cell domain bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric MeasureTheory
namespace SphericalRiesz

theorem finite_compact_grid8_capped (η : ℝ) (hη : 0 < η) {ι : Type*} [Fintype ι]
    (k U : ι → Set (Fin 8 → ℝ)) (hk : ∀ i, IsCompact (k i))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, k i ⊆ U i) :
    ∃ h > 0, h < η ∧ ∃ Z : ι → Finset (Fin 8 → ℤ),
      ∀ i, k i ⊆ ⋃ z ∈ Z i, gridHalfOpenCell8 h z ∧
        ∀ z ∈ Z i, gridClosedCell8 h z ⊆ U i := by
  classical
  have hm : ∀ i, ∃ r > 0, thickening r (k i) ⊆ U i := fun i =>
    (hk i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hbuffer using hm
  obtain ⟨δ,hδ,hδr⟩ := finite_positive_lower_bound8 r hr
  let h := min δ η/2
  have hh : 0 < h := by dsimp [h]; positivity
  let Z : ι → Finset (Fin 8 → ℤ) := fun i => (gridLabel8_image_finite h hh (k i) (hk i)).toFinset
  refine ⟨h,hh,by dsimp [h]; linarith [min_le_right δ η],Z,?_⟩
  intro i
  have hZ : ∀ z, z ∈ Z i ↔ z ∈ gridLabel8 h '' k i := by
    intro z
    exact Set.Finite.mem_toFinset _
  constructor
  · simpa only [hZ] using gridCells8_cover h hh (k i)
  · intro z hz
    apply gridClosedCells8_subset_buffer h (r i) hh ?_ (k i) (U i) (hbuffer i) z ((hZ z).mp hz)
    dsimp [h]
    linarith [hδr i,min_le_left δ η]


theorem sphere8_finite_small_chart_grid_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ U : Fin K → Set Sphere8, ∃ h > 0, h < η ∧ ∃ Z : Fin K → Finset (Fin 8 → ℤ),
      (∀ i, IsOpen (U i) ∧ ∀ z ∈ Z i,
        e8Map '' gridClosedCell8 h z ⊆ equalAreaChartDomain ∧
        (∀ x ∈ gridClosedCell8 h z, ‖e8Map x‖ < a) ∧
        equalAreaE8SpherePatch8 (g i) 0 0 1 (gridClosedCell8 h z) ⊆ U i) ∧
      1-b < sphereProbability8.real
        (⋃ i, ⋃ z ∈ Z i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h z)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  obtain ⟨K,g,k,ρ,hρ,hk,hmass,hd⟩ := sphere8_finite_small_chart_buffered_cores a b ha hb
  let U : Fin K → Set Sphere8 := fun i => thickening ρ (k i)
  have hkh : ∀ i, k i ⊆ equalAreaRotatedHemisphere8 (g i) := by
    intro i q hq
    obtain ⟨u,hu,_,he⟩ := (hk i).2.2.2 q ((hk i).2.2.1 hq)
    exact equalAreaRotatedHemisphere8_of_representation (g i) q u hu he
  let c : Fin K → Set (Fin 8 → ℝ) := fun i =>
    e8CoordinateInverse8 '' (equalAreaRotatedInverse8 (g i) '' k i)
  let V : Fin K → Set (Fin 8 → ℝ) := fun i =>
    e8CoordinateInverse8 '' equalAreaCoordinateBuffer8 (g i) (U i)
  have hc : ∀ i, IsCompact (c i) := fun i =>
    e8CoordinateCore8_isCompact (g i) (k i) (hk i).1 (hkh i)
  have hV : ∀ i, IsOpen (V i) := fun i =>
    e8CoordinateBuffer8_isOpen (g i) (U i) (hk i).2.1
  have hsub : ∀ i, c i ⊆ V i := fun i => image_mono
    (equalAreaCoordinateCore8_subset_buffer (g i) (k i) (U i) (hkh i) (hk i).2.2.1)
  obtain ⟨h,hh,hhη,Z,hgrid⟩ := finite_compact_grid8_capped η hη c V hc hV hsub
  refine ⟨K,g,U,h,hh,hhη,Z,?_,?_,hd⟩
  · intro i
    refine ⟨(hk i).2.1,?_⟩
    intro z hz
    have hcell := (hgrid i).2 z hz
    refine ⟨?_,?_,e8GridSpherePatch8_subset_buffer (g i) _ (U i) hcell⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact (e8CoordinateBuffer8_mem (g i) (U i) x (hcell hx)).1
    · intro x hx
      exact e8CoordinateBuffer8_norm_lt (g i) (U i) a (hk i).2.2.2 x (hcell hx)
  · apply hmass.trans_le
    apply measureReal_mono (μ := sphereProbability8) ?_ (measure_ne_top _ _)
    intro q hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hq
    let x := e8CoordinateInverse8 (equalAreaRotatedInverse8 (g i) q)
    have hx : x ∈ c i := ⟨equalAreaRotatedInverse8 (g i) q,⟨q,hi,rfl⟩,rfl⟩
    obtain ⟨z,hz,hcell⟩ := mem_iUnion₂.mp ((hgrid i).1 hx)
    apply mem_iUnion.mpr
    refine ⟨i,mem_iUnion₂.mpr ⟨z,hz,?_⟩⟩
    refine ⟨x,hcell,?_⟩
    simpa [equalAreaE8Patch,equalAreaMovingE8Chart,x,e8Map_coordinateInverse8] using
      equalAreaRotatedPhi_inverse8 (g i) q (hkh i hi)


theorem sphere8_finite_small_chart_grid_flat_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ L : ℕ, ∃ g : Fin L → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ z : Fin L → Fin 8 → ℤ, ∃ h > 0, h < η ∧
      (∀ i, e8Map '' gridClosedCell8 h (z i) ⊆ equalAreaChartDomain ∧
        ∀ x ∈ gridClosedCell8 h (z i), ‖e8Map x‖ < a) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i)))
        (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridHalfOpenCell8 h (z j)))) ∧
      1-b < sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))) := by
  classical
  obtain ⟨K,g,U,h,hh,hhη,Z,hcell,hmass,hd⟩ := sphere8_finite_small_chart_grid_capped a b η ha hb hη
  let I := Σ i : Fin K, Z i
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g' := fun j => g (e.symm j).1
  let z' := fun j => (e.symm j).2.val
  have hdI := e8GridSphereSigma8_disjoint g U h hh Z
    (fun i z hz => ((hcell i).2 z hz).1)
    (fun i z hz => ((hcell i).2 z hz).2.2) hd
  have heq : (⋃ j, equalAreaE8SpherePatch8 (g' j) 0 0 1 (gridHalfOpenCell8 h (z' j))) =
      ⋃ i, ⋃ z ∈ Z i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h z) := by
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
      change q ∈ equalAreaE8SpherePatch8 (g (e.symm (e ⟨i,⟨z,hz⟩⟩)).1) 0 0 1
        (gridHalfOpenCell8 h (e.symm (e ⟨i,⟨z,hz⟩⟩)).2.val)
      rw [e.symm_apply_apply]
      exact hzq
  refine ⟨Fintype.card I,g',z',h,hh,hhη,?_,?_,?_⟩
  · intro j
    exact ⟨((hcell (e.symm j).1).2 _ (e.symm j).2.property).1,
      ((hcell (e.symm j).1).2 _ (e.symm j).2.property).2.1⟩
  · intro i j hij
    exact hdI (e.symm.injective.ne hij)
  · simpa only [heq] using hmass


theorem sphere8_near_full_separated_shrunk_grid_capped (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    ∃ L : ℕ, ∃ g : Fin L → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ z : Fin L → Fin 8 → ℤ, ∃ h > 0, h < η ∧ ∃ γ > 0, γ < 1 ∧
      (∀ i, e8Map '' gridShrunkCell8 h γ (z i) ⊆ equalAreaChartDomain ∧
        (∀ x ∈ gridShrunkCell8 h γ (z i), ‖e8Map x‖ < a) ∧
        IsCompact (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)))
        (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridShrunkCell8 h γ (z j)))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)),
        ∀ y ∈ equalAreaE8SpherePatch8 (g j) 0 0 1 (gridShrunkCell8 h γ (z j)), δ < dist x y) ∧
      1-b < sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) ∧
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) < 1 := by
  classical
  obtain ⟨L,g,z,h,hh,hhη,hcell,hd,hm⟩ := sphere8_finite_small_chart_grid_flat_capped a
    (min (b/4) (1/4)) η ha (lt_min (by positivity) (by norm_num)) hη
  let H := ⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))
  obtain ⟨γ,hγ,hγ1,hl,hu⟩ := shrinkMass8_loss_budget b (sphereProbability8.real H) hb
    measureReal_nonneg measureReal_le_one hm
  have hs : ∀ i, gridShrunkCell8 h γ (z i) ⊆ gridClosedCell8 h (z i) := fun i =>
    (gridShrunkCell8_subset_halfOpen h γ hh hγ (z i)).trans
      (gridHalfOpenCell8_subset_closed h (z i))
  have hcompact : ∀ i, IsCompact
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) := fun i =>
    e8GridSpherePatch8_isCompact _ _ (gridShrunkCell8_isCompact h γ (z i))
  have hd' := e8GridShrunkSphereFamily8_disjoint g z h γ hh hγ hd
  have heq := e8GridShrunkSphereFamily8_probability_real_factor g z h γ hh hγ hγ1.le
    (fun i => (hcell i).1) hd
  refine ⟨L,g,z,h,hh,hhη,γ,hγ,hγ1,?_,hd',
    finite_compact_disjoint_distance8 _ hcompact hd',?_,?_⟩
  · intro i
    exact ⟨(image_mono (hs i)).trans (hcell i).1,
      fun x hx => (hcell i).2 x (hs i hx),hcompact i⟩
  · rw [heq]; exact hl
  · rw [heq]; exact hu


end SphericalRiesz
