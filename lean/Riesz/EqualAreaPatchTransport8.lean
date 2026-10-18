import Riesz.EqualAreaPatchMeasure8
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual sphere-valued cube embedding transports the scaled coordinate
measure to spherical probability restricted to the physical patch. The
Bochner formula is valid for arbitrary test functions; integrability is
transported separately, so singular kernels do not silently become integrable. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

def equalAreaE8CubeEmbedding8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) : UnitCube 8 ↪ Sphere8 where
  toFun x := ⟨equalAreaE8Patch g v c ε x, mem_sphere_zero_iff_norm.mpr
    (equalAreaE8Patch_norm g v c ε x
      ((equalAreaE8Affine8_cube_domain v c ε hε hc hsmall) ⟨x,x.property,rfl⟩).1)⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply equalAreaE8Affine8_injective v c ε hε.ne'
    apply equalAreaPhi_injOn
      ((equalAreaE8Affine8_cube_domain v c ε hε hc hsmall) ⟨x,x.property,rfl⟩)
      ((equalAreaE8Affine8_cube_domain v c ε hε hc hsmall) ⟨y,y.property,rfl⟩)
    exact g.injective (congrArg Subtype.val h)

theorem equalAreaE8CubeEmbedding8_continuous (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    Continuous (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall) := by
  apply Continuous.subtype_mk
  exact g.continuous.comp (equalAreaPhi_continuous.comp
    ((equalAreaE8Affine8_continuous v c ε).comp continuous_subtype_val))

theorem equalAreaE8CubeEmbedding8_measurableEmbedding (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    MeasurableEmbedding (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall) := by
  let : PolishSpace (UnitCube 8) := (unitCube_isCompact 8).isClosed.polishSpace
  exact (equalAreaE8CubeEmbedding8_continuous g v c ε hε hc hsmall).measurableEmbedding
    (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall).injective

theorem equalAreaE8CubeEmbedding8_image (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (s : Set (UnitCube 8)) :
    equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall '' s =
      equalAreaE8SpherePatch8 g v c ε (Subtype.val '' s) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,⟨x,hx,rfl⟩,rfl⟩
  · rintro ⟨x,⟨z,hz,rfl⟩,h⟩
    exact ⟨z,hz,Subtype.ext h⟩

theorem equalAreaE8CubeEmbedding8_range (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    range (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall) =
      equalAreaE8SpherePatch8 g v c ε (UnitCube 8) := by
  rw [← image_univ, equalAreaE8CubeEmbedding8_image, image_univ, Subtype.range_coe]

theorem equalAreaE8CubeEmbedding8_comap_probability (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    sphereProbability8.comap (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall) =
      ENNReal.ofReal (equalAreaE8PatchProbabilityDensity8 ε) •
        (volume.comap (Subtype.val : UnitCube 8 → (Fin 8 → ℝ))) := by
  ext s hs
  rw [(equalAreaE8CubeEmbedding8_measurableEmbedding g v c ε hε hc hsmall).comap_apply,
    equalAreaE8CubeEmbedding8_image,
    equalAreaE8SpherePatch8_subset_cube_probability g v c ε hε hc hsmall _
      ((MeasurableEmbedding.subtype_coe (unitCube_measurableSet 8)).measurableSet_image.2 hs)
      (Subtype.coe_image_subset _ _),
    Measure.smul_apply, comap_subtype_coe_apply (unitCube_measurableSet 8),smul_eq_mul]
  rfl

theorem equalAreaE8CubeEmbedding8_map_probability (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    Measure.map (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall)
      (ENNReal.ofReal (equalAreaE8PatchProbabilityDensity8 ε) •
        (volume.comap (Subtype.val : UnitCube 8 → (Fin 8 → ℝ)))) =
      sphereProbability8.restrict (equalAreaE8SpherePatch8 g v c ε (UnitCube 8)) := by
  rw [← equalAreaE8CubeEmbedding8_comap_probability g v c ε hε hc hsmall,
    (equalAreaE8CubeEmbedding8_measurableEmbedding g v c ε hε hc hsmall).map_comap,
    equalAreaE8CubeEmbedding8_range]

theorem equalAreaE8CubeEmbedding8_integral (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (f : Sphere8 → ℝ) :
    (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8), f y ∂sphereProbability8) =
      equalAreaE8PatchProbabilityDensity8 ε *
        ∫ x : UnitCube 8, f (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall x)
          ∂(volume.comap (Subtype.val : UnitCube 8 → (Fin 8 → ℝ))) := by
  rw [← equalAreaE8CubeEmbedding8_map_probability g v c ε hε hc hsmall,
    (equalAreaE8CubeEmbedding8_measurableEmbedding g v c ε hε hc hsmall).integral_map,
    integral_smul_measure,
    ENNReal.toReal_ofReal (equalAreaE8PatchProbabilityDensity8_pos ε hε).le,smul_eq_mul]

theorem equalAreaE8SpherePatch8_integral (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (f : Ambient9 → ℝ) :
    (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8), f y ∂sphereProbability8) =
      equalAreaE8PatchProbabilityDensity8 ε *
        ∫ x in UnitCube 8, f (equalAreaE8Patch g v c ε x) := by
  rw [equalAreaE8CubeEmbedding8_integral g v c ε hε hc hsmall]
  congr 1
  exact integral_subtype_comap (unitCube_measurableSet 8)
    (fun x => f (equalAreaE8Patch g v c ε x))

theorem equalAreaE8CubeEmbedding8_integrable_iff (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (f : Sphere8 → ℝ) :
    IntegrableOn f (equalAreaE8SpherePatch8 g v c ε (UnitCube 8)) sphereProbability8 ↔
      Integrable (fun x : UnitCube 8 => f (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall x))
        (volume.comap (Subtype.val : UnitCube 8 → (Fin 8 → ℝ))) := by
  rw [← equalAreaE8CubeEmbedding8_range g v c ε hε hc hsmall,
    (equalAreaE8CubeEmbedding8_measurableEmbedding g v c ε hε hc hsmall).integrableOn_range_iff_comap,
    equalAreaE8CubeEmbedding8_comap_probability,
    integrable_smul_measure (ENNReal.ofReal_pos.mpr
      (equalAreaE8PatchProbabilityDensity8_pos ε hε)).ne' ENNReal.ofReal_ne_top]
  rfl

theorem equalAreaE8SpherePatch8_integrable_iff (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (f : Ambient9 → ℝ) :
    IntegrableOn (fun y : Sphere8 => f y)
      (equalAreaE8SpherePatch8 g v c ε (UnitCube 8)) sphereProbability8 ↔
      IntegrableOn (fun x => f (equalAreaE8Patch g v c ε x)) (UnitCube 8) := by
  rw [equalAreaE8CubeEmbedding8_integrable_iff g v c ε hε hc hsmall]
  exact (integrableOn_iff_comap_subtypeVal (μ := volume)
    (f := fun x => f (equalAreaE8Patch g v c ε x)) (unitCube_measurableSet 8)).symm

end SphericalRiesz
