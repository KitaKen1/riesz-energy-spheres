import Riesz.EqualAreaConeJacobianD
import Riesz.CubeLebesgue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Exact coordinate-area formula for the actual spherical chart.
The actual toSphere measure is reduced to actual cone volume, whose
Jacobian is t^(n+1). No abstract surface-area equality is assumed. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise ENNReal
namespace SphericalRiesz

variable {n : ℕ}

def equalAreaConeOverD (s : Set (Fin (n+1) → ℝ)) : Set (Fin (n+1+1) → ℝ) :=
  {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ s}

def equalAreaSpherePatchD (s : Set (Fin (n+1) → ℝ)) : Set (SphereD (n+1)) :=
  Subtype.val ⁻¹' (equalAreaPhiD '' s)

theorem equalAreaConeOverD_measurable (s : Set (Fin (n+1) → ℝ)) (hs : MeasurableSet s) :
    MeasurableSet (equalAreaConeOverD s) :=
  (measurableSet_Ioo.preimage (continuous_apply 0).measurable).inter
    (hs.preimage (equalAreaTailProjection9D.continuous.measurable))

theorem equalAreaConeOverD_subset (s : Set (Fin (n+1) → ℝ)) (hs : s ⊆ equalAreaChartDomainD) :
    equalAreaConeOverD s ⊆ equalAreaConeDomainD :=
  fun _ hz => ⟨hz.1,hs hz.2⟩

theorem equalAreaSpherePatchD_measurable (s : Set (Fin (n+1) → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomainD) :
    MeasurableSet (equalAreaSpherePatchD s) :=
  (hs.image_of_continuousOn_injOn equalAreaPhiD_continuous.continuousOn
    (equalAreaPhiD_injOn.mono hsub)).preimage measurable_subtype_coe

theorem equalAreaSpherePatchD_coe_image (s : Set (Fin (n+1) → ℝ))
    (hsub : s ⊆ equalAreaChartDomainD) :
    Subtype.val '' equalAreaSpherePatchD s = equalAreaPhiD '' s := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨equalAreaPhiD p,equalAreaPhiD_mem_sphere p (hsub hp).1⟩,⟨p,hp,rfl⟩,rfl⟩

theorem equalAreaConeCoordinatesD_injOn (s : Set (Fin (n+1) → ℝ))
    (hsub : s ⊆ equalAreaChartDomainD) :
    InjOn equalAreaConeCoordinatesD (equalAreaConeOverD s) := by
  intro z hz w hw h
  apply equalAreaConeD_injOn (equalAreaConeOverD_subset s hsub hz)
    (equalAreaConeOverD_subset s hsub hw)
  have he := congrArg (WithLp.toLp 2) h
  simpa [equalAreaConeCoordinatesD] using he

theorem equalAreaConeCoordinatesD_image_measurable (s : Set (Fin (n+1) → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomainD) :
    MeasurableSet (equalAreaConeCoordinatesD '' equalAreaConeOverD s) := by
  apply measurable_image_of_fderivWithin (equalAreaConeOverD_measurable s hs)
    (fun z hz => (equalAreaConeCoordinatesD_hasFDerivAt z (hsub hz.2).1).hasFDerivWithinAt)
    (equalAreaConeCoordinatesD_injOn s hsub)

theorem equalAreaConeCoordinatesD_volume_jacobian (s : Set (Fin (n+1) → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomainD) :
    (volume : Measure (Fin (n+1+1) → ℝ)) (equalAreaConeCoordinatesD '' equalAreaConeOverD s) =
      ∫⁻ z in equalAreaConeOverD s, ENNReal.ofReal (|z 0|^(n+1)) := by
  rw [←lintegral_abs_det_fderiv_eq_addHaar_image volume (equalAreaConeOverD_measurable s hs)
    (fun z hz => (equalAreaConeCoordinatesD_hasFDerivAt z (hsub hz.2).1).hasFDerivWithinAt)
    (equalAreaConeCoordinatesD_injOn s hsub)]
  apply setLIntegral_congr_fun (equalAreaConeOverD_measurable s hs)
  intro z hz
  dsimp only
  rw [equalAreaConeCoordinateDerivativeD_abs_det z (hsub hz.2).1]

theorem equalAreaConeD_actual_volume (s : Set (Fin (n+1) → ℝ)) :
    (volume : Measure (AmbientD (n+1))) (equalAreaConeD '' equalAreaConeOverD s) =
      (volume : Measure (Fin (n+1+1) → ℝ)) (equalAreaConeCoordinatesD '' equalAreaConeOverD s) := by
  have h := (PiLp.volume_preserving_toLp (Fin (n+1+1))).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin (n+1+1) → ℝ)).measurableEmbedding
    (equalAreaConeD '' equalAreaConeOverD s)
  have he : WithLp.toLp 2 ⁻¹' (equalAreaConeD '' equalAreaConeOverD s) =
      equalAreaConeCoordinatesD '' equalAreaConeOverD s := by
    ext x
    constructor
    · rintro ⟨z,hz,h⟩
      exact ⟨z,hz,congrArg (WithLp.ofLp) h⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,by simp [equalAreaConeCoordinatesD]⟩
  rw [he] at h
  exact h.symm

theorem equalAreaConeOverD_cons_image (s : Set (Fin (n+1) → ℝ)) :
    Boundary.cubeConsEquiv (n+1) '' ((Ioo (0:ℝ) 1).prod s) = equalAreaConeOverD s := by
  ext z
  constructor
  · rintro ⟨⟨t,p⟩,⟨ht,hp⟩,rfl⟩
    simpa [equalAreaConeOverD,Boundary.cubeConsEquiv_apply] using And.intro ht hp
  · intro hz
    exact ⟨(z 0,Fin.tail z),⟨hz.1,hz.2⟩,by rw [Boundary.cubeConsEquiv_apply]; exact Fin.cons_self_tail z⟩

theorem equalAreaD_radial_lintegral :
    (∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (|t|^(n+1))) = ENNReal.ofReal (1/(n+2):ℝ) := by
  have hc : (∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (|t|^(n+1))) =
      ∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (t^(n+1)) :=
    setLIntegral_congr_fun measurableSet_Ioo (fun t ht => by rw [abs_of_pos ht.1])
  have hi : IntegrableOn (fun t : ℝ => t^(n+1)) (Ioo 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => t^(n+1))).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hv : (∫ t in Ioo (0:ℝ) 1, t^(n+1)) = 1/(n+2) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
    push_cast
    norm_num
    ring
  rw [hc, ← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => pow_nonneg ht.1.le _)),
    hv]

theorem equalAreaConeOverD_weighted_volume (s : Set (Fin (n+1) → ℝ)) :
    (∫⁻ z in equalAreaConeOverD s, ENNReal.ofReal (|z 0|^(n+1))) =
      ENNReal.ofReal (1/(n+2):ℝ)*(volume : Measure (Fin (n+1) → ℝ)) s := by
  have h := (Boundary.cubeConsEquiv_measurePreserving (n+1)).setLIntegral_comp_emb
    (Boundary.cubeConsEquiv (n+1)).measurableEmbedding
    (fun z : Fin (n+1+1) → ℝ => ENNReal.ofReal (|z 0|^(n+1))) ((Ioo (0:ℝ) 1).prod s)
  rw [equalAreaConeOverD_cons_image] at h
  rw [←h,Measure.volume_eq_prod]
  simp only [Boundary.cubeConsEquiv_apply,Fin.cons_zero]
  erw [setLIntegral_prod (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin (n+1) → ℝ)))
    (s := Ioo (0:ℝ) 1) (t := s)
    (fun p : ℝ × (Fin (n+1) → ℝ) => ENNReal.ofReal (|p.1|^(n+1))) (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ (by fun_prop),equalAreaD_radial_lintegral]

theorem equalAreaConeD_volume (s : Set (Fin (n+1) → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomainD) :
    (volume : Measure (AmbientD (n+1))) (equalAreaConeD '' equalAreaConeOverD s) =
      ENNReal.ofReal (1/(n+2):ℝ)*(volume : Measure (Fin (n+1) → ℝ)) s := by
  rw [equalAreaConeD_actual_volume,equalAreaConeCoordinatesD_volume_jacobian s hs hsub,
    equalAreaConeOverD_weighted_volume]

/-- The actual sphere-area measure equals ordinary coordinate Lebesgue
volume on every measurable subset of the explicit local chart domain. -/
theorem sphereAreaD_equalAreaSpherePatch (s : Set (Fin (n+1) → ℝ))
    (hs : MeasurableSet s) (hsub : s ⊆ equalAreaChartDomainD) :
    (sphereAreaD (n+1)) (equalAreaSpherePatchD s) = (volume : Measure (Fin (n+1) → ℝ)) s := by
  have ha : (sphereAreaD (n+1)) (equalAreaSpherePatchD s) =
      ((n+1+1:ℕ):ℝ≥0∞)*(volume : Measure (AmbientD (n+1))) (equalAreaConeD '' equalAreaConeOverD s) := by
    rw [sphereAreaD,Measure.toSphere_apply' _ (equalAreaSpherePatchD_measurable s hs hsub),
      equalAreaSpherePatchD_coe_image s hsub,←equalAreaConeD_image]
    congr 1
    simp [AmbientD]
  rw [ha,equalAreaConeD_volume s hs hsub,←mul_assoc]
  have h : ((n+1+1:ℕ):ℝ≥0∞)*ENNReal.ofReal (1/(n+2):ℝ) = 1 := by
    rw [← ENNReal.ofReal_natCast, ←ENNReal.ofReal_mul (by positivity)]
    push_cast
    rw [show ((n:ℝ)+1+1)*(1/(n+2)) = 1 by field_simp; ring]
    simp
  rw [h,one_mul]

end SphericalRiesz
