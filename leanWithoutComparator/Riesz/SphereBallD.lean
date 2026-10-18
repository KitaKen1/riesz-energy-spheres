import Riesz.SphereMeasureD

/-!
Dimension-generic actual direction pushforward of the normalized ambient unit ball. The domain
omits the ambient origin, a Lebesgue null point. This reduces the singular
spherical integral to an ambient integral. The construction uses the ambient origin only through a null-set removal and
requires no coordinate marginal formula or integrability witness.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped Pointwise
namespace SphericalRiesz

variable (d : ℕ)

abbrev NonzeroD (d : ℕ) := ({0}ᶜ : Set (AmbientD d))

def sphereDirectionD (z : NonzeroD d) : SphereD d :=
  (homeomorphUnitSphereProd (AmbientD d) z).1

theorem sphereDirectionD_coe (z : NonzeroD d) :
    (sphereDirectionD d z : AmbientD d) = ‖(z : AmbientD d)‖⁻¹ • (z : AmbientD d) := by
  simp [sphereDirectionD]

theorem sphereDirectionD_measurable : Measurable (sphereDirectionD d) :=
  measurable_fst.comp (homeomorphUnitSphereProd (AmbientD d)).measurable

def unitBallNonzeroD : Set (NonzeroD d) := {z | ‖(z : AmbientD d)‖ < 1}

theorem unitBallNonzeroD_measurable : MeasurableSet (unitBallNonzeroD d) :=
  (continuous_norm.comp continuous_subtype_val).measurable measurableSet_Iio

def sphereBallMeasureD : Measure (NonzeroD d) :=
  (d+1 : ENNReal) • ((volume : Measure (AmbientD d)).comap Subtype.val).restrict (unitBallNonzeroD d)

theorem sphereBallMeasureD_direction_preserving :
    MeasurePreserving (sphereDirectionD d) (sphereBallMeasureD d) (sphereAreaD d) := by
  refine ⟨sphereDirectionD_measurable d, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereDirectionD_measurable d) hs, sphereBallMeasureD, Measure.smul_apply,
    Measure.restrict_apply (hs.preimage (sphereDirectionD_measurable d))]
  have hemb : MeasurableEmbedding (Subtype.val : NonzeroD d → AmbientD d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  rw [hemb.comap_apply]
  have hset : sphereDirectionD d ⁻¹' s ∩ unitBallNonzeroD d =
      (homeomorphUnitSphereProd (AmbientD d)) ⁻¹' (s ×ˢ Iio (⟨1, mem_Ioi.mpr zero_lt_one⟩ : Ioi (0 : ℝ))) := by
    ext z
    simp only [mem_inter_iff, mem_preimage, sphereDirectionD, unitBallNonzeroD,
      mem_ofPred_eq, mem_prod, mem_Iio]
    apply and_congr_right
    intro _
    change ‖(z : AmbientD d)‖ < 1 ↔ ((homeomorphUnitSphereProd (AmbientD d) z).2 : ℝ) < 1
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [hset, Measure.toSphere_apply_aux]
  rw [sphereAreaD, Measure.toSphere_apply' _ hs]
  simp [AmbientD]

def sphereBallProbabilityD : Measure (NonzeroD d) :=
  (sphereAreaD d univ)⁻¹ • sphereBallMeasureD d

theorem sphereBallProbabilityD_direction_preserving :
    MeasurePreserving (sphereDirectionD d) (sphereBallProbabilityD d) (sphereProbabilityD d) :=
  (sphereBallMeasureD_direction_preserving d).smul_measure (sphereAreaD d univ)⁻¹

instance sphereBallProbabilityD_probability : IsProbabilityMeasure (sphereBallProbabilityD d) := by
  haveI : IsProbabilityMeasure ((sphereBallProbabilityD d).map (sphereDirectionD d)) := by
    rw [(sphereBallProbabilityD_direction_preserving d).map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map
    (sphereBallProbabilityD_direction_preserving d).measurable.aemeasurable

theorem sphereBallProbabilityD_mass : sphereBallProbabilityD d univ = 1 := measure_univ


#print axioms sphereDirectionD_coe
#print axioms sphereDirectionD_measurable
#print axioms unitBallNonzeroD_measurable
#print axioms sphereBallMeasureD_direction_preserving
#print axioms sphereBallProbabilityD_direction_preserving
#print axioms sphereBallProbabilityD_mass

end SphericalRiesz
