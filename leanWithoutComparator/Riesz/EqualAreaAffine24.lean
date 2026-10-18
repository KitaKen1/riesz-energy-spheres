import Riesz.EqualAreaPatchClass24
import Riesz.PatchSupportD
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Compose translation, the already checked determinant-one E8 map,
and scalar dilation. This gives the actual coordinate-volume factor
without recomputing the spherical cone Jacobian. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology Pointwise
namespace SphericalRiesz
open Boundary

def equalAreaLeechAffine24 (v c : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) : Fin 24 → ℝ :=
  v+ε • leechMap (x-c)

theorem equalAreaLeechAffine24_continuous (v c : Fin 24 → ℝ) (ε : ℝ) :
    Continuous (equalAreaLeechAffine24 v c ε) := by
  unfold equalAreaLeechAffine24
  fun_prop

theorem equalAreaLeechAffine24_injective (v c : Fin 24 → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    Function.Injective (equalAreaLeechAffine24 v c ε) := by
  intro x y hxy
  have he : ε • leechMap (x-c) = ε • leechMap (y-c) := add_left_cancel hxy
  have h := congrArg (fun z : Fin 24 → ℝ => ε⁻¹ • z) he
  simp only [smul_smul,inv_mul_cancel₀ hε,one_smul] at h
  simpa using leechMap_injective h

theorem equalAreaLeechAffine24_image_measurable (v c : Fin 24 → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (s : Set (Fin 24 → ℝ)) (hs : MeasurableSet s) :
    MeasurableSet (equalAreaLeechAffine24 v c ε '' s) :=
  hs.image_of_continuousOn_injOn (equalAreaLeechAffine24_continuous v c ε).continuousOn
    (equalAreaLeechAffine24_injective v c ε hε).injOn

theorem volume24_image_preserving8 (f : (Fin 24 → ℝ) → (Fin 24 → ℝ))
    (hf : MeasurePreserving f volume volume) (he : MeasurableEmbedding f)
    (s : Set (Fin 24 → ℝ)) : volume (f '' s) = volume s := by
  rw [← hf.measure_preimage_emb he,he.injective.preimage_image]

theorem equalAreaLeechAffine24_image_volume (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε)
    (s : Set (Fin 24 → ℝ)) :
    volume (equalAreaLeechAffine24 v c ε '' s) = ENNReal.ofReal (ε^24)*volume s := by
  have himage : equalAreaLeechAffine24 v c ε '' s =
      (fun z : Fin 24 → ℝ => v+z) ''
        ((fun z : Fin 24 → ℝ => ε • z) '' (leechMap '' ((fun x : Fin 24 → ℝ => x-c) '' s))) := by
    simp only [image_image]
    rfl
  rw [himage,volume24_image_preserving8 _ (measurePreserving_add_left volume v)
    (Homeomorph.addLeft v).measurableEmbedding]
  change volume (ε • (leechMap '' ((fun x : Fin 24 → ℝ => x-c) '' s))) = _
  rw [Measure.addHaar_smul_of_nonneg volume hε.le,
    volume24_image_preserving8 leechMap leechMap_measurePreserving leechMap_measurableEmbedding,
    volume24_image_preserving8 _ (measurePreserving_sub_right volume c)
      (Homeomorph.subRight c).measurableEmbedding]
  simp

theorem equalArea24_small_norm_chart_domain (p : Fin 24 → ℝ) (hp : ‖p‖ ≤ 1/8) :
    p ∈ equalAreaChartDomainD := by
  refine ⟨equalArea24_small_norm_domain p hp,?_⟩
  have hcoord : |p 0| ≤ 1/8 := (norm_le_pi_norm p 0).trans hp
  have hpi := Real.two_le_pi
  exact ⟨by linarith [(abs_le.mp hcoord).1],by linarith [(abs_le.mp hcoord).2]⟩

theorem equalAreaLeechAffine24_cube_domain (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hc : c ∈ UnitCube 24) (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    equalAreaLeechAffine24 v c ε '' UnitCube 24 ⊆ equalAreaChartDomainD := by
  rintro _ ⟨x,hx,rfl⟩
  apply equalArea24_small_norm_chart_domain
  exact (equalAreaMovingScaledLeech_norm v ε (x-c) (unitCube24_sub_norm x c hx hc)).trans
    (by simpa only [abs_of_pos hε] using hsmall)

end SphericalRiesz
