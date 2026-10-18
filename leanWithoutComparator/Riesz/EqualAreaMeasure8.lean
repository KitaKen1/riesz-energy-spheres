import Riesz.EqualAreaConeJacobian8
import Riesz.CubeLebesgue
import Riesz.SpherePoleAngle8
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Exact coordinate-area formula for the actual spherical chart.
The actual toSphere measure is reduced to actual cone volume, whose
Jacobian is t^8. No abstract surface-area equality is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise ENNReal
namespace SphericalRiesz

def equalAreaConeOver (s : Set (Fin 8 → ℝ)) : Set (Fin 9 → ℝ) :=
  {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ s}

def equalAreaSpherePatch (s : Set (Fin 8 → ℝ)) : Set Sphere8 :=
  Subtype.val ⁻¹' (equalAreaPhi '' s)

theorem equalAreaConeOver_measurable (s : Set (Fin 8 → ℝ)) (hs : MeasurableSet s) :
    MeasurableSet (equalAreaConeOver s) :=
  (measurableSet_Ioo.preimage (continuous_apply 0).measurable).inter
    (hs.preimage (equalAreaTailProjection9.continuous.measurable))

theorem equalAreaConeOver_subset (s : Set (Fin 8 → ℝ)) (hs : s ⊆ equalAreaChartDomain) :
    equalAreaConeOver s ⊆ equalAreaConeDomain :=
  fun _ hz => ⟨hz.1,hs hz.2⟩

theorem equalAreaSpherePatch_measurable (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomain) :
    MeasurableSet (equalAreaSpherePatch s) :=
  (hs.image_of_continuousOn_injOn equalAreaPhi_continuous.continuousOn
    (equalAreaPhi_injOn.mono hsub)).preimage measurable_subtype_coe

theorem equalAreaSpherePatch_coe_image (s : Set (Fin 8 → ℝ))
    (hsub : s ⊆ equalAreaChartDomain) :
    Subtype.val '' equalAreaSpherePatch s = equalAreaPhi '' s := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨equalAreaPhi p,equalAreaPhi_mem_sphere p (hsub hp).1⟩,⟨p,hp,rfl⟩,rfl⟩

theorem equalAreaConeCoordinates_injOn (s : Set (Fin 8 → ℝ))
    (hsub : s ⊆ equalAreaChartDomain) :
    InjOn equalAreaConeCoordinates (equalAreaConeOver s) := by
  intro z hz w hw h
  apply equalAreaCone_injOn (equalAreaConeOver_subset s hsub hz)
    (equalAreaConeOver_subset s hsub hw)
  have he := congrArg (WithLp.toLp 2) h
  simpa [equalAreaConeCoordinates] using he

theorem equalAreaConeCoordinates_image_measurable (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomain) :
    MeasurableSet (equalAreaConeCoordinates '' equalAreaConeOver s) := by
  apply measurable_image_of_fderivWithin (equalAreaConeOver_measurable s hs)
    (fun z hz => (equalAreaConeCoordinates_hasFDerivAt z (hsub hz.2).1).hasFDerivWithinAt)
    (equalAreaConeCoordinates_injOn s hsub)

theorem equalAreaConeCoordinates_volume_jacobian (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomain) :
    (volume : Measure (Fin 9 → ℝ)) (equalAreaConeCoordinates '' equalAreaConeOver s) =
      ∫⁻ z in equalAreaConeOver s, ENNReal.ofReal ((z 0)^8) := by
  rw [←lintegral_abs_det_fderiv_eq_addHaar_image volume (equalAreaConeOver_measurable s hs)
    (fun z hz => (equalAreaConeCoordinates_hasFDerivAt z (hsub hz.2).1).hasFDerivWithinAt)
    (equalAreaConeCoordinates_injOn s hsub)]
  apply setLIntegral_congr_fun (equalAreaConeOver_measurable s hs)
  intro z hz
  dsimp only
  rw [equalAreaConeCoordinateDerivative_abs_det z (hsub hz.2).1]

theorem equalAreaCone_actual_volume (s : Set (Fin 8 → ℝ)) :
    (volume : Measure Ambient9) (equalAreaCone '' equalAreaConeOver s) =
      (volume : Measure (Fin 9 → ℝ)) (equalAreaConeCoordinates '' equalAreaConeOver s) := by
  have h := (PiLp.volume_preserving_toLp (Fin 9)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 9 → ℝ)).measurableEmbedding
    (equalAreaCone '' equalAreaConeOver s)
  have he : WithLp.toLp 2 ⁻¹' (equalAreaCone '' equalAreaConeOver s) =
      equalAreaConeCoordinates '' equalAreaConeOver s := by
    ext x
    constructor
    · rintro ⟨z,hz,h⟩
      exact ⟨z,hz,congrArg (WithLp.ofLp) h⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,by simp [equalAreaConeCoordinates]⟩
  rw [he] at h
  exact h.symm

theorem equalAreaConeOver_cons_image (s : Set (Fin 8 → ℝ)) :
    Boundary.cubeConsEquiv 8 '' ((Ioo (0:ℝ) 1).prod s) = equalAreaConeOver s := by
  ext z
  constructor
  · rintro ⟨⟨t,p⟩,⟨ht,hp⟩,rfl⟩
    simpa [equalAreaConeOver,Boundary.cubeConsEquiv_apply] using And.intro ht hp
  · intro hz
    exact ⟨(z 0,Fin.tail z),⟨hz.1,hz.2⟩,by rw [Boundary.cubeConsEquiv_apply]; exact Fin.cons_self_tail z⟩

theorem equalArea_radial_lintegral :
    (∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (t^8)) = ENNReal.ofReal (1/9:ℝ) := by
  have hi : IntegrableOn (fun t : ℝ => t^8) (Ioo 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => t^8)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => by positivity)),
    poleRadialPower8_setIntegral]

theorem equalAreaConeOver_weighted_volume (s : Set (Fin 8 → ℝ)) :
    (∫⁻ z in equalAreaConeOver s, ENNReal.ofReal ((z 0)^8)) =
      ENNReal.ofReal (1/9:ℝ)*(volume : Measure (Fin 8 → ℝ)) s := by
  have h := (Boundary.cubeConsEquiv_measurePreserving 8).setLIntegral_comp_emb
    (Boundary.cubeConsEquiv 8).measurableEmbedding
    (fun z : Fin 9 → ℝ => ENNReal.ofReal ((z 0)^8)) ((Ioo (0:ℝ) 1).prod s)
  rw [equalAreaConeOver_cons_image] at h
  rw [←h,Measure.volume_eq_prod]
  simp only [Boundary.cubeConsEquiv_apply,Fin.cons_zero]
  erw [setLIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 8 → ℝ)))
    (s := Ioo (0:ℝ) 1) (t := s)
    (fun p : ℝ × (Fin 8 → ℝ) => ENNReal.ofReal (p.1^8)) (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ (by fun_prop),equalArea_radial_lintegral]

theorem equalAreaCone_volume (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomain) :
    (volume : Measure Ambient9) (equalAreaCone '' equalAreaConeOver s) =
      ENNReal.ofReal (1/9:ℝ)*(volume : Measure (Fin 8 → ℝ)) s := by
  rw [equalAreaCone_actual_volume,equalAreaConeCoordinates_volume_jacobian s hs hsub,
    equalAreaConeOver_weighted_volume]

/-- The actual sphere-area measure equals ordinary coordinate Lebesgue
volume on every measurable subset of the explicit local chart domain. -/
theorem sphereArea8_equalAreaSpherePatch (s : Set (Fin 8 → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomain) :
    sphereArea8 (equalAreaSpherePatch s) = (volume : Measure (Fin 8 → ℝ)) s := by
  have ha : sphereArea8 (equalAreaSpherePatch s) =
      (9:ℝ≥0∞)*(volume : Measure Ambient9) (equalAreaCone '' equalAreaConeOver s) := by
    rw [sphereArea8,Measure.toSphere_apply' _ (equalAreaSpherePatch_measurable s hs hsub),
      equalAreaSpherePatch_coe_image s hsub,←equalAreaCone_image]
    congr 1
    norm_num [Ambient9]
  rw [ha,equalAreaCone_volume s hs hsub,←mul_assoc]
  have h : (9:ℝ≥0∞)*ENNReal.ofReal (1/9:ℝ) = 1 := by
    rw [show (9:ℝ≥0∞) = ENNReal.ofReal (9:ℝ) by norm_num,
      ←ENNReal.ofReal_mul (by positivity)]
    norm_num
  rw [h,one_mul]

end SphericalRiesz
