import Riesz.EqualAreaAffine8

/-! Actual area and probability of every measurable subset of a scaled,
translated and rotated E8 patch. This composes the checked local area
formula with exact affine volume and rotation invariance. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

def equalAreaE8SpherePatch8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (s : Set (Fin 8 → ℝ)) : Set Sphere8 :=
  Subtype.val ⁻¹' (equalAreaE8Patch g v c ε '' s)

theorem equalAreaE8SpherePatch8_rotation_preimage (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (s : Set (Fin 8 → ℝ)) :
    equalAreaE8SpherePatch8 g v c ε s = (sphereRotation8 g.symm) ⁻¹'
      equalAreaSpherePatch (equalAreaE8Affine8 v c ε '' s) := by
  ext x
  change (∃ y ∈ s, equalAreaE8Patch g v c ε y = (x : Ambient9)) ↔
    (∃ p ∈ equalAreaE8Affine8 v c ε '' s, equalAreaPhi p = g.symm (x : Ambient9))
  constructor
  · rintro ⟨y,hy,h⟩
    refine ⟨equalAreaE8Affine8 v c ε y,⟨y,hy,rfl⟩,?_⟩
    simpa only [equalAreaE8Patch,equalAreaMovingE8Chart,equalAreaE8Affine8,
      g.symm_apply_apply] using congrArg g.symm h
  · rintro ⟨p,⟨y,hy,rfl⟩,h⟩
    refine ⟨y,hy,?_⟩
    simpa only [equalAreaE8Patch,equalAreaMovingE8Chart,equalAreaE8Affine8,
      g.apply_symm_apply] using congrArg g h

theorem equalAreaE8SpherePatch8_measurable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaE8Affine8 v c ε '' s ⊆ equalAreaChartDomain) :
    MeasurableSet (equalAreaE8SpherePatch8 g v c ε s) := by
  rw [equalAreaE8SpherePatch8_rotation_preimage]
  exact (equalAreaSpherePatch_measurable _
    (equalAreaE8Affine8_image_measurable v c ε hε.ne' s hs) hsub).preimage
      (sphereRotation8 g.symm).measurable

theorem equalAreaE8SpherePatch8_area (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaE8Affine8 v c ε '' s ⊆ equalAreaChartDomain) :
    sphereArea8 (equalAreaE8SpherePatch8 g v c ε s) = ENNReal.ofReal (ε^8)*volume s := by
  rw [equalAreaE8SpherePatch8_rotation_preimage,
    (sphereArea8_rotation_preserving g.symm).measure_preimage_emb
      (sphereRotation8 g.symm).measurableEmbedding,
    sphereArea8_equalAreaSpherePatch _
      (equalAreaE8Affine8_image_measurable v c ε hε.ne' s hs) hsub,
    equalAreaE8Affine8_image_volume v c ε hε]

def equalAreaE8PatchProbabilityDensity8 (ε : ℝ) : ℝ :=
  ε^8/(sphereArea8.real univ)

theorem equalAreaE8PatchProbabilityDensity8_pos (ε : ℝ) (hε : 0 < ε) :
    0 < equalAreaE8PatchProbabilityDensity8 ε := by
  unfold equalAreaE8PatchProbabilityDensity8
  rw [sphereArea8_mass_real]
  positivity

theorem equalAreaE8PatchProbabilityDensity8_ofReal (ε : ℝ) :
    ENNReal.ofReal (equalAreaE8PatchProbabilityDensity8 ε) =
      (sphereArea8 univ)⁻¹*ENNReal.ofReal (ε^8) := by
  unfold equalAreaE8PatchProbabilityDensity8
  rw [sphereArea8_mass_real,sphereArea8_mass,ENNReal.ofReal_div_of_pos (by positivity)]
  rw [div_eq_mul_inv,mul_comm]

theorem equalAreaE8SpherePatch8_probability (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaE8Affine8 v c ε '' s ⊆ equalAreaChartDomain) :
    sphereProbability8 (equalAreaE8SpherePatch8 g v c ε s) =
      ENNReal.ofReal (equalAreaE8PatchProbabilityDensity8 ε)*volume s := by
  rw [sphereProbability8,Measure.smul_apply,equalAreaE8SpherePatch8_area g v c ε hε s hs hsub,
    smul_eq_mul,← mul_assoc,← equalAreaE8PatchProbabilityDensity8_ofReal]

theorem equalAreaE8SpherePatch8_probability_real (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaE8Affine8 v c ε '' s ⊆ equalAreaChartDomain) :
    sphereProbability8.real (equalAreaE8SpherePatch8 g v c ε s) =
      equalAreaE8PatchProbabilityDensity8 ε*(volume : Measure (Fin 8 → ℝ)).real s := by
  rw [Measure.real,equalAreaE8SpherePatch8_probability g v c ε hε s hs hsub,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (equalAreaE8PatchProbabilityDensity8_pos ε hε).le]
  rfl

theorem equalAreaE8SpherePatch8_subset_cube_probability (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8)
    (s : Set (Fin 8 → ℝ)) (hs : MeasurableSet s) (hsc : s ⊆ UnitCube 8) :
    sphereProbability8 (equalAreaE8SpherePatch8 g v c ε s) =
      ENNReal.ofReal (ε^8/(sphereArea8.real univ))*volume s :=
  equalAreaE8SpherePatch8_probability g v c ε hε s hs
    ((image_mono hsc).trans (equalAreaE8Affine8_cube_domain v c ε hε hc hsmall))

theorem equalAreaE8SpherePatch8_cube_probability (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    sphereProbability8 (equalAreaE8SpherePatch8 g v c ε (UnitCube 8)) =
      ENNReal.ofReal (ε^8/(sphereArea8.real univ)) := by
  rw [equalAreaE8SpherePatch8_subset_cube_probability g v c ε hε hc hsmall _
    (unitCube_measurableSet 8) Subset.rfl,unitCube_volume,mul_one]

end SphericalRiesz
