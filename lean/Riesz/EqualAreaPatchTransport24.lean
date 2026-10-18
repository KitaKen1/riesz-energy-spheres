import Riesz.EqualAreaPatchMeasure24
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual sphere-valued cube embedding transports the scaled coordinate
measure to spherical probability restricted to the physical patch. The
Bochner formula is valid for arbitrary test functions; integrability is
transported separately, so singular kernels do not silently become integrable. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

def equalAreaLeechCubeEmbedding24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) : UnitCube 24 ↪ (SphereD 24) where
  toFun x := ⟨equalAreaLeechPatch g v c ε x, mem_sphere_zero_iff_norm.mpr
    (equalAreaLeechPatch_norm g v c ε x
      ((equalAreaLeechAffine24_cube_domain v c ε hε hc hsmall) ⟨x,x.property,rfl⟩).1)⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply equalAreaLeechAffine24_injective v c ε hε.ne'
    apply equalAreaPhiD_injOn
      ((equalAreaLeechAffine24_cube_domain v c ε hε hc hsmall) ⟨x,x.property,rfl⟩)
      ((equalAreaLeechAffine24_cube_domain v c ε hε hc hsmall) ⟨y,y.property,rfl⟩)
    exact g.injective (congrArg Subtype.val h)

theorem equalAreaLeechCubeEmbedding24_continuous (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    Continuous (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall) := by
  apply Continuous.subtype_mk
  exact g.continuous.comp (equalAreaPhiD_continuous.comp
    ((equalAreaLeechAffine24_continuous v c ε).comp continuous_subtype_val))

theorem equalAreaLeechCubeEmbedding24_measurableEmbedding (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    MeasurableEmbedding (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall) := by
  let : PolishSpace (UnitCube 24) := (unitCube_isCompact 24).isClosed.polishSpace
  exact (equalAreaLeechCubeEmbedding24_continuous g v c ε hε hc hsmall).measurableEmbedding
    (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall).injective

theorem equalAreaLeechCubeEmbedding24_image (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (s : Set (UnitCube 24)) :
    equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall '' s =
      equalAreaLeechSpherePatch24 g v c ε (Subtype.val '' s) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,⟨x,hx,rfl⟩,rfl⟩
  · rintro ⟨x,⟨z,hz,rfl⟩,h⟩
    exact ⟨z,hz,Subtype.ext h⟩

theorem equalAreaLeechCubeEmbedding24_range (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    range (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall) =
      equalAreaLeechSpherePatch24 g v c ε (UnitCube 24) := by
  rw [← image_univ, equalAreaLeechCubeEmbedding24_image, image_univ, Subtype.range_coe]

theorem equalAreaLeechCubeEmbedding24_comap_probability (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    (sphereProbabilityD 24).comap (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall) =
      ENNReal.ofReal (equalAreaLeechPatchProbabilityDensity24 ε) •
        (volume.comap (Subtype.val : UnitCube 24 → (Fin 24 → ℝ))) := by
  ext s hs
  rw [(equalAreaLeechCubeEmbedding24_measurableEmbedding g v c ε hε hc hsmall).comap_apply,
    equalAreaLeechCubeEmbedding24_image,
    equalAreaLeechSpherePatch24_subset_cube_probability g v c ε hε hc hsmall _
      ((MeasurableEmbedding.subtype_coe (unitCube_measurableSet 24)).measurableSet_image.2 hs)
      (Subtype.coe_image_subset _ _),
    Measure.smul_apply, comap_subtype_coe_apply (unitCube_measurableSet 24),smul_eq_mul]
  rfl

theorem equalAreaLeechCubeEmbedding24_map_probability (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    Measure.map (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall)
      (ENNReal.ofReal (equalAreaLeechPatchProbabilityDensity24 ε) •
        (volume.comap (Subtype.val : UnitCube 24 → (Fin 24 → ℝ)))) =
      (sphereProbabilityD 24).restrict (equalAreaLeechSpherePatch24 g v c ε (UnitCube 24)) := by
  rw [← equalAreaLeechCubeEmbedding24_comap_probability g v c ε hε hc hsmall,
    (equalAreaLeechCubeEmbedding24_measurableEmbedding g v c ε hε hc hsmall).map_comap,
    equalAreaLeechCubeEmbedding24_range]

theorem equalAreaLeechCubeEmbedding24_integral (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (f : (SphereD 24) → ℝ) :
    (∫ y in equalAreaLeechSpherePatch24 g v c ε (UnitCube 24), f y ∂(sphereProbabilityD 24)) =
      equalAreaLeechPatchProbabilityDensity24 ε *
        ∫ x : UnitCube 24, f (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall x)
          ∂(volume.comap (Subtype.val : UnitCube 24 → (Fin 24 → ℝ))) := by
  rw [← equalAreaLeechCubeEmbedding24_map_probability g v c ε hε hc hsmall,
    (equalAreaLeechCubeEmbedding24_measurableEmbedding g v c ε hε hc hsmall).integral_map,
    integral_smul_measure,
    ENNReal.toReal_ofReal (equalAreaLeechPatchProbabilityDensity24_pos ε hε).le,smul_eq_mul]

theorem equalAreaLeechSpherePatch24_integral (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (f : (AmbientD 24) → ℝ) :
    (∫ y in equalAreaLeechSpherePatch24 g v c ε (UnitCube 24), f y ∂(sphereProbabilityD 24)) =
      equalAreaLeechPatchProbabilityDensity24 ε *
        ∫ x in UnitCube 24, f (equalAreaLeechPatch g v c ε x) := by
  rw [equalAreaLeechCubeEmbedding24_integral g v c ε hε hc hsmall]
  congr 1
  exact integral_subtype_comap (unitCube_measurableSet 24)
    (fun x => f (equalAreaLeechPatch g v c ε x))

theorem equalAreaLeechCubeEmbedding24_integrable_iff (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (f : (SphereD 24) → ℝ) :
    IntegrableOn f (equalAreaLeechSpherePatch24 g v c ε (UnitCube 24)) (sphereProbabilityD 24) ↔
      Integrable (fun x : UnitCube 24 => f (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall x))
        (volume.comap (Subtype.val : UnitCube 24 → (Fin 24 → ℝ))) := by
  rw [← equalAreaLeechCubeEmbedding24_range g v c ε hε hc hsmall,
    (equalAreaLeechCubeEmbedding24_measurableEmbedding g v c ε hε hc hsmall).integrableOn_range_iff_comap,
    equalAreaLeechCubeEmbedding24_comap_probability,
    integrable_smul_measure (ENNReal.ofReal_pos.mpr
      (equalAreaLeechPatchProbabilityDensity24_pos ε hε)).ne' ENNReal.ofReal_ne_top]
  rfl

theorem equalAreaLeechSpherePatch24_integrable_iff (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (f : (AmbientD 24) → ℝ) :
    IntegrableOn (fun y : (SphereD 24) => f y)
      (equalAreaLeechSpherePatch24 g v c ε (UnitCube 24)) (sphereProbabilityD 24) ↔
      IntegrableOn (fun x => f (equalAreaLeechPatch g v c ε x)) (UnitCube 24) := by
  rw [equalAreaLeechCubeEmbedding24_integrable_iff g v c ε hε hc hsmall]
  exact (integrableOn_iff_comap_subtypeVal (μ := volume)
    (f := fun x => f (equalAreaLeechPatch g v c ε x)) (unitCube_measurableSet 24)).symm

end SphericalRiesz
