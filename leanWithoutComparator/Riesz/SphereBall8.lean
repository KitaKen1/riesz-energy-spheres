import Riesz.SphereArea8

/-!
Actual direction pushforward of the normalized ambient unit ball. The domain
omits the ambient origin, a Lebesgue null point. This reduces the singular
spherical integral to an ambient integral. Integrability is proved downstream
in SphereIntegrable8; the numerical evaluation remains separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped Pointwise
namespace SphericalRiesz

abbrev Nonzero9 := ({0}ᶜ : Set Ambient9)

def sphereDirection8 (z : Nonzero9) : Sphere8 :=
  (homeomorphUnitSphereProd Ambient9 z).1

theorem sphereDirection8_coe (z : Nonzero9) :
    (sphereDirection8 z : Ambient9) = ‖(z : Ambient9)‖⁻¹ • (z : Ambient9) := by
  simp [sphereDirection8]

theorem sphereDirection8_measurable : Measurable sphereDirection8 :=
  measurable_fst.comp (homeomorphUnitSphereProd Ambient9).measurable

def unitBallNonzero9 : Set Nonzero9 := {z | ‖(z : Ambient9)‖ < 1}

theorem unitBallNonzero9_measurable : MeasurableSet unitBallNonzero9 :=
  (continuous_norm.comp continuous_subtype_val).measurable measurableSet_Iio

def sphereBallMeasure8 : Measure Nonzero9 :=
  (9 : ENNReal) • ((volume : Measure Ambient9).comap Subtype.val).restrict unitBallNonzero9

theorem sphereBallMeasure8_direction_preserving :
    MeasurePreserving sphereDirection8 sphereBallMeasure8 sphereArea8 := by
  refine ⟨sphereDirection8_measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply sphereDirection8_measurable hs, sphereBallMeasure8, Measure.smul_apply,
    Measure.restrict_apply (hs.preimage sphereDirection8_measurable)]
  have hemb : MeasurableEmbedding (Subtype.val : Nonzero9 → Ambient9) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  rw [hemb.comap_apply]
  have hset : sphereDirection8 ⁻¹' s ∩ unitBallNonzero9 =
      (homeomorphUnitSphereProd Ambient9) ⁻¹' (s ×ˢ Iio (⟨1, mem_Ioi.mpr zero_lt_one⟩ : Ioi (0 : ℝ))) := by
    ext z
    simp only [mem_inter_iff, mem_preimage, sphereDirection8, unitBallNonzero9,
      mem_ofPred_eq, mem_prod, mem_Iio]
    apply and_congr_right
    intro _
    change ‖(z : Ambient9)‖ < 1 ↔ ((homeomorphUnitSphereProd Ambient9 z).2 : ℝ) < 1
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [hset, Measure.toSphere_apply_aux]
  rw [sphereArea8, Measure.toSphere_apply' _ hs]
  simp [Ambient9]

def sphereBallProbability8 : Measure Nonzero9 :=
  (sphereArea8 univ)⁻¹ • sphereBallMeasure8

theorem sphereBallProbability8_direction_preserving :
    MeasurePreserving sphereDirection8 sphereBallProbability8 sphereProbability8 :=
  sphereBallMeasure8_direction_preserving.smul_measure (sphereArea8 univ)⁻¹

instance sphereBallProbability8_probability : IsProbabilityMeasure sphereBallProbability8 := by
  haveI : IsProbabilityMeasure (sphereBallProbability8.map sphereDirection8) := by
    rw [sphereBallProbability8_direction_preserving.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map
    sphereBallProbability8_direction_preserving.measurable.aemeasurable

theorem sphereBallProbability8_mass : sphereBallProbability8 univ = 1 := measure_univ

theorem sphereKernel4_measurable (p : Sphere8) : Measurable (sphereKernel4 p) := by
  unfold sphereKernel4
  fun_prop

theorem sphereKernel4_ball_integrable_iff (p : Sphere8) :
    Integrable (sphereKernel4 p) sphereProbability8 ↔
      Integrable (fun z => sphereKernel4 p (sphereDirection8 z)) sphereBallProbability8 :=
  sphereBallProbability8_direction_preserving.integrable_comp
    (sphereKernel4_measurable p).aestronglyMeasurable |>.symm

theorem spherePotential4_ball_integral (p : Sphere8) :
    spherePotential4 p =
      ∫ z, sphereKernel4 p (sphereDirection8 z) ∂sphereBallProbability8 := by
  unfold spherePotential4
  rw [← sphereBallProbability8_direction_preserving.map_eq]
  exact integral_map sphereDirection8_measurable.aemeasurable
    (sphereKernel4_measurable p).aestronglyMeasurable

#print axioms sphereDirection8_coe
#print axioms sphereDirection8_measurable
#print axioms unitBallNonzero9_measurable
#print axioms sphereBallMeasure8_direction_preserving
#print axioms sphereBallProbability8_direction_preserving
#print axioms sphereBallProbability8_mass
#print axioms sphereKernel4_measurable
#print axioms sphereKernel4_ball_integrable_iff
#print axioms spherePotential4_ball_integral

end SphericalRiesz
