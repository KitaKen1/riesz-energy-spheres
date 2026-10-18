import Riesz.CompactGrid8
import Riesz.EqualAreaCoordinateBuffers8
import Riesz.SphereSmallChartCores8

/-! Apply finite floor grids to the actual near-full rotated small-chart
cores. The unshrunk half-open cells cover those cores, with all closed
cells inside the physically disjoint open buffers. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric MeasureTheory
namespace SphericalRiesz

theorem equalAreaRotatedHemisphere8_of_representation (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (q : Sphere8) (u : Fin 8 → ℝ) (hu : u ∈ equalAreaChartDomain)
    (he : g (equalAreaPhi u) = (q : Ambient9)) : q ∈ equalAreaRotatedHemisphere8 g := by
  change 0 < (g.symm (q : Ambient9)) 0
  rw [← he,g.symm_apply_apply]
  exact equalAreaPhi_first_pos u hu

theorem e8CoordinateBuffer8_mem (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (U : Set Sphere8)
    (x : Fin 8 → ℝ) (hx : x ∈ e8CoordinateInverse8 '' equalAreaCoordinateBuffer8 g U) :
    e8Map x ∈ equalAreaChartDomain ∧ ∃ q ∈ U, g (equalAreaPhi (e8Map x)) = (q : Ambient9) := by
  obtain ⟨u,hu,rfl⟩ := hx
  rw [e8Map_coordinateInverse8]
  exact equalAreaCoordinateBuffer8_mem g U u hu

theorem e8CoordinateBuffer8_norm_lt (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (U : Set Sphere8) (a : ℝ)
    (hsmall : ∀ q ∈ U, ∃ u ∈ equalAreaChartDomain, ‖u‖ < a ∧
      g (equalAreaPhi u) = (q : Ambient9))
    (x : Fin 8 → ℝ) (hx : x ∈ e8CoordinateInverse8 '' equalAreaCoordinateBuffer8 g U) :
    ‖e8Map x‖ < a := by
  obtain ⟨hu,q,hq,he⟩ := e8CoordinateBuffer8_mem g U x hx
  obtain ⟨u,hu',hn,he'⟩ := hsmall q hq
  have hxu := equalAreaPhi_injOn hu hu' (g.injective (he.trans he'.symm))
  simpa only [hxu] using hn

theorem e8GridSpherePatch8_subset_buffer (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (s : Set (Fin 8 → ℝ)) (U : Set Sphere8)
    (hs : s ⊆ e8CoordinateInverse8 '' equalAreaCoordinateBuffer8 g U) :
    equalAreaE8SpherePatch8 g 0 0 1 s ⊆ U := by
  intro q hq
  obtain ⟨x,hx,he⟩ := hq
  obtain ⟨_,p,hp,he'⟩ := e8CoordinateBuffer8_mem g U x (hs hx)
  have he0 : g (equalAreaPhi (e8Map x)) = (q : Ambient9) := by
    simpa only [equalAreaE8Patch,equalAreaMovingE8Chart,sub_zero,one_smul,zero_add] using he
  have heq : (q : Ambient9) = (p : Ambient9) := by
    exact he0.symm.trans he'
  exact (Subtype.ext heq).symm ▸ hp

theorem sphere8_finite_small_chart_grid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ U : Fin K → Set Sphere8, ∃ h > 0, ∃ Z : Fin K → Finset (Fin 8 → ℤ),
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
  obtain ⟨h,hh,Z,hgrid⟩ := finite_compact_grid8 c V hc hV hsub
  refine ⟨K,g,U,h,hh,Z,?_,?_,hd⟩
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

end SphericalRiesz
