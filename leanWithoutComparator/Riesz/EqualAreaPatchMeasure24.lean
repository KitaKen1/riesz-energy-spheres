import Riesz.EqualAreaAffine24

/-! Actual area and probability of every measurable subset of a scaled,
translated and rotated E8 patch. This composes the checked local area
formula with exact affine volume and rotation invariance. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

def equalAreaLeechSpherePatch24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (s : Set (Fin 24 → ℝ)) : Set (SphereD 24) :=
  Subtype.val ⁻¹' (equalAreaLeechPatch g v c ε '' s)

theorem equalAreaLeechSpherePatch24_rotation_preimage (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (s : Set (Fin 24 → ℝ)) :
    equalAreaLeechSpherePatch24 g v c ε s = (sphereRotationD g.symm) ⁻¹'
      equalAreaSpherePatchD (equalAreaLeechAffine24 v c ε '' s) := by
  ext x
  change (∃ y ∈ s, equalAreaLeechPatch g v c ε y = (x : (AmbientD 24))) ↔
    (∃ p ∈ equalAreaLeechAffine24 v c ε '' s, equalAreaPhiD p = g.symm (x : (AmbientD 24)))
  constructor
  · rintro ⟨y,hy,h⟩
    refine ⟨equalAreaLeechAffine24 v c ε y,⟨y,hy,rfl⟩,?_⟩
    simpa only [equalAreaLeechPatch,equalAreaMovingLeechChart,equalAreaLeechAffine24,
      g.symm_apply_apply] using congrArg g.symm h
  · rintro ⟨p,⟨y,hy,rfl⟩,h⟩
    refine ⟨y,hy,?_⟩
    simpa only [equalAreaLeechPatch,equalAreaMovingLeechChart,equalAreaLeechAffine24,
      g.apply_symm_apply] using congrArg g h

theorem equalAreaLeechSpherePatch24_measurable (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 24 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaLeechAffine24 v c ε '' s ⊆ equalAreaChartDomainD) :
    MeasurableSet (equalAreaLeechSpherePatch24 g v c ε s) := by
  rw [equalAreaLeechSpherePatch24_rotation_preimage]
  exact (equalAreaSpherePatchD_measurable _
    (equalAreaLeechAffine24_image_measurable v c ε hε.ne' s hs) hsub).preimage
      (sphereRotationD g.symm).measurable

theorem equalAreaLeechSpherePatch24_area (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 24 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaLeechAffine24 v c ε '' s ⊆ equalAreaChartDomainD) :
    (sphereAreaD 24) (equalAreaLeechSpherePatch24 g v c ε s) = ENNReal.ofReal (ε^24)*volume s := by
  rw [equalAreaLeechSpherePatch24_rotation_preimage,
    (sphereAreaD_rotation_preserving g.symm).measure_preimage_emb
      (sphereRotationD g.symm).measurableEmbedding,
    sphereAreaD_equalAreaSpherePatch _
      (equalAreaLeechAffine24_image_measurable v c ε hε.ne' s hs) hsub,
    equalAreaLeechAffine24_image_volume v c ε hε]

def equalAreaLeechPatchProbabilityDensity24 (ε : ℝ) : ℝ :=
  ε^24/((sphereAreaD 24).real univ)

theorem equalAreaLeechPatchProbabilityDensity24_pos (ε : ℝ) (hε : 0 < ε) :
    0 < equalAreaLeechPatchProbabilityDensity24 ε := by
  unfold equalAreaLeechPatchProbabilityDensity24
  exact div_pos (pow_pos hε 24) (sphereAreaD_univ_pos 24)

theorem equalAreaLeechPatchProbabilityDensity24_ofReal (ε : ℝ) :
    ENNReal.ofReal (equalAreaLeechPatchProbabilityDensity24 ε) =
      ((sphereAreaD 24) univ)⁻¹*ENNReal.ofReal (ε^24) := by
  unfold equalAreaLeechPatchProbabilityDensity24
  rw [ENNReal.ofReal_div_of_pos (sphereAreaD_univ_pos 24), ofReal_measureReal (measure_ne_top _ _)]
  rw [div_eq_mul_inv,mul_comm]

theorem equalAreaLeechSpherePatch24_probability (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 24 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaLeechAffine24 v c ε '' s ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 24) (equalAreaLeechSpherePatch24 g v c ε s) =
      ENNReal.ofReal (equalAreaLeechPatchProbabilityDensity24 ε)*volume s := by
  rw [sphereProbabilityD,Measure.smul_apply,equalAreaLeechSpherePatch24_area g v c ε hε s hs hsub,
    smul_eq_mul,← mul_assoc,← equalAreaLeechPatchProbabilityDensity24_ofReal]

theorem equalAreaLeechSpherePatch24_probability_real (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 24 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaLeechAffine24 v c ε '' s ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 24).real (equalAreaLeechSpherePatch24 g v c ε s) =
      equalAreaLeechPatchProbabilityDensity24 ε*(volume : Measure (Fin 24 → ℝ)).real s := by
  rw [Measure.real,equalAreaLeechSpherePatch24_probability g v c ε hε s hs hsub,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (equalAreaLeechPatchProbabilityDensity24_pos ε hε).le]
  rfl

theorem equalAreaLeechSpherePatch24_subset_cube_probability (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8)
    (s : Set (Fin 24 → ℝ)) (hs : MeasurableSet s) (hsc : s ⊆ UnitCube 24) :
    (sphereProbabilityD 24) (equalAreaLeechSpherePatch24 g v c ε s) =
      ENNReal.ofReal (ε^24/((sphereAreaD 24).real univ))*volume s :=
  equalAreaLeechSpherePatch24_probability g v c ε hε s hs
    ((image_mono hsc).trans (equalAreaLeechAffine24_cube_domain v c ε hε hc hsmall))

theorem equalAreaLeechSpherePatch24_cube_probability (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c : Fin 24 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 24)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    (sphereProbabilityD 24) (equalAreaLeechSpherePatch24 g v c ε (UnitCube 24)) =
      ENNReal.ofReal (ε^24/((sphereAreaD 24).real univ)) := by
  rw [equalAreaLeechSpherePatch24_subset_cube_probability g v c ε hε hc hsmall _
    (unitCube_measurableSet 24) Subset.rfl,unitCube_volume,mul_one]

end SphericalRiesz
