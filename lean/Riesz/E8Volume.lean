import Riesz.E8Coordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Lebesgue volume of the concrete E8 basis map

The coordinate map uses the rows, hence its matrix is the transpose of
`e8Matrix`. The checked determinant one is connected to the actual
Lebesgue pushforward. This does not establish the sphere area formula
or the equality of the nested cube integral with a set integral.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz

theorem e8Map_eq_matrixTranspose (v : Fin 8 → ℝ) :
    e8Map v = Matrix.toLin' e8Matrix.transpose v := by
  rw [e8Map_eq_sum, Matrix.toLin'_apply]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row,
    Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem e8Map_det : LinearMap.det e8Map.toLinearMap = 1 := by
  have h : e8Map.toLinearMap = Matrix.toLin' e8Matrix.transpose :=
    LinearMap.ext e8Map_eq_matrixTranspose
  rw [h, LinearMap.det_toLin', Matrix.det_transpose, e8Matrix_det]

theorem e8Map_map_volume :
    Measure.map e8Map (volume : Measure (Fin 8 → ℝ)) = volume := by
  have hdet : LinearMap.det e8Map.toLinearMap ≠ 0 := by rw [e8Map_det]; norm_num
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  simpa only [ContinuousLinearMap.coe_coe, e8Map_det, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul] using h

theorem e8Map_measurePreserving :
    MeasurePreserving e8Map (volume : Measure (Fin 8 → ℝ)) volume :=
  ⟨e8Map.measurable, e8Map_map_volume⟩

theorem e8Map_volume_preimage (s : Set (Fin 8 → ℝ)) (hs : MeasurableSet s) :
    volume (e8Map ⁻¹' s) = volume s := by
  calc
    _ = Measure.map e8Map volume s := (Measure.map_apply e8Map.measurable hs).symm
    _ = _ := congrArg (fun μ : Measure (Fin 8 → ℝ) => μ s) e8Map_map_volume

theorem e8Map_measurableEmbedding : MeasurableEmbedding (e8Map : (Fin 8 → ℝ) → (Fin 8 → ℝ)) :=
  e8Basis.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- Actual Lebesgue set integrals, including on the image of the coordinate cube. -/
theorem e8Map_integral_image (f : (Fin 8 → ℝ) → ℝ) (s : Set (Fin 8 → ℝ)) :
    ∫ z in e8Map '' s, f z = ∫ v in s, f (e8Map v) :=
  e8Map_measurePreserving.setIntegral_image_emb e8Map_measurableEmbedding f s

#print axioms e8Map_eq_matrixTranspose
#print axioms e8Map_det
#print axioms e8Map_map_volume
#print axioms e8Map_measurePreserving
#print axioms e8Map_volume_preimage
#print axioms e8Map_measurableEmbedding
#print axioms e8Map_integral_image

end SphericalRiesz
