import Riesz.EqualAreaPatchClass8
import Riesz.E8Volume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Compose translation, the already checked determinant-one E8 map,
and scalar dilation. This gives the actual coordinate-volume factor
without recomputing the spherical cone Jacobian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology Pointwise
namespace SphericalRiesz
open Boundary

def equalAreaE8Affine8 (v c : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  v+ε • e8Map (x-c)

theorem equalAreaE8Affine8_continuous (v c : Fin 8 → ℝ) (ε : ℝ) :
    Continuous (equalAreaE8Affine8 v c ε) := by
  unfold equalAreaE8Affine8
  fun_prop

theorem equalAreaE8Affine8_injective (v c : Fin 8 → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    Function.Injective (equalAreaE8Affine8 v c ε) := by
  intro x y hxy
  have he : ε • e8Map (x-c) = ε • e8Map (y-c) := add_left_cancel hxy
  have h := congrArg (fun z : Fin 8 → ℝ => ε⁻¹ • z) he
  simp only [smul_smul,inv_mul_cancel₀ hε,one_smul] at h
  simpa using e8Map_injective h

theorem equalAreaE8Affine8_image_measurable (v c : Fin 8 → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (s : Set (Fin 8 → ℝ)) (hs : MeasurableSet s) :
    MeasurableSet (equalAreaE8Affine8 v c ε '' s) :=
  hs.image_of_continuousOn_injOn (equalAreaE8Affine8_continuous v c ε).continuousOn
    (equalAreaE8Affine8_injective v c ε hε).injOn

theorem volume_image_preserving8 (f : (Fin 8 → ℝ) → (Fin 8 → ℝ))
    (hf : MeasurePreserving f volume volume) (he : MeasurableEmbedding f)
    (s : Set (Fin 8 → ℝ)) : volume (f '' s) = volume s := by
  rw [← hf.measure_preimage_emb he,he.injective.preimage_image]

theorem equalAreaE8Affine8_image_volume (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε)
    (s : Set (Fin 8 → ℝ)) :
    volume (equalAreaE8Affine8 v c ε '' s) = ENNReal.ofReal (ε^8)*volume s := by
  have himage : equalAreaE8Affine8 v c ε '' s =
      (fun z : Fin 8 → ℝ => v+z) ''
        ((fun z : Fin 8 → ℝ => ε • z) '' (e8Map '' ((fun x : Fin 8 → ℝ => x-c) '' s))) := by
    simp only [image_image]
    rfl
  rw [himage,volume_image_preserving8 _ (measurePreserving_add_left volume v)
    (Homeomorph.addLeft v).measurableEmbedding]
  change volume (ε • (e8Map '' ((fun x : Fin 8 → ℝ => x-c) '' s))) = _
  rw [Measure.addHaar_smul_of_nonneg volume hε.le,
    volume_image_preserving8 e8Map e8Map_measurePreserving e8Map_measurableEmbedding,
    volume_image_preserving8 _ (measurePreserving_sub_right volume c)
      (Homeomorph.subRight c).measurableEmbedding]
  simp

theorem equalArea_small_norm_chart_domain (p : Fin 8 → ℝ) (hp : ‖p‖ ≤ 1/8) :
    p ∈ equalAreaChartDomain := by
  refine ⟨equalArea_small_norm_domain p hp,?_⟩
  have hcoord : |p 0| ≤ 1/8 := (norm_le_pi_norm p 0).trans hp
  have hpi := Real.two_le_pi
  exact ⟨by linarith [(abs_le.mp hcoord).1],by linarith [(abs_le.mp hcoord).2]⟩

theorem equalAreaE8Affine8_cube_domain (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hc : c ∈ UnitCube 8) (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    equalAreaE8Affine8 v c ε '' UnitCube 8 ⊆ equalAreaChartDomain := by
  rintro _ ⟨x,hx,rfl⟩
  apply equalArea_small_norm_chart_domain
  exact (equalAreaMovingScaledE8_norm v ε (x-c) (unitCube8_sub_norm x c hx hc)).trans
    (by simpa only [abs_of_pos hε] using hsmall)

end SphericalRiesz
