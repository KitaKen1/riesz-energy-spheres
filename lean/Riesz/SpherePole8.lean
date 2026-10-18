import Riesz.SphereIntegrable8

/-!
Actual pole kernel and actual ambient-ball integral. These identities do not
assume a coordinate marginal or the numerical value of the sphere potential.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace
namespace SphericalRiesz

theorem northPole8_dist_sq (q : Sphere8) :
    dist northPole8 q ^ 2 = 2 - 2 * (q : Ambient9) 0 := by
  change ‖(northPole8 : Ambient9) - (q : Ambient9)‖ ^ 2 = _
  rw [norm_sub_sq_real]
  have hp : ‖(northPole8 : Ambient9)‖ = 1 := mem_sphere_zero_iff_norm.mp northPole8.property
  have hq : ‖(q : Ambient9)‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  have hi : ⟪(northPole8 : Ambient9), (q : Ambient9)⟫ = (q : Ambient9) 0 := by
    simp [northPole8, EuclideanSpace.inner_single_left]
  rw [hp, hq, hi]
  ring

theorem northPole8_kernel_coordinate (q : Sphere8) :
    sphereKernel4 northPole8 q = (2 - 2 * (q : Ambient9) 0)⁻¹ ^ 2 := by
  rw [← northPole8_dist_sq]
  unfold sphereKernel4
  rw [← inv_pow, ← pow_mul]

def ambientPoleKernel4 (v : Ambient9) : ℝ := (2 - 2 * v 0 / ‖v‖)⁻¹ ^ 2

theorem ambientPoleKernel4_measurable : Measurable ambientPoleKernel4 := by
  unfold ambientPoleKernel4
  fun_prop

theorem northPole8_direction_kernel (z : Nonzero9) :
    sphereKernel4 northPole8 (sphereDirection8 z) = ambientPoleKernel4 z := by
  rw [northPole8_kernel_coordinate, sphereDirection8_coe]
  unfold ambientPoleKernel4
  simp only [PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv]
  congr 3
  ring

private theorem unitBallNonzero9_preimage :
    (Subtype.val : Nonzero9 → Ambient9) ⁻¹' ball 0 1 = unitBallNonzero9 := by
  ext z
  simp [unitBallNonzero9]

theorem ambientPoleKernel4_unitBall_integrable :
    IntegrableOn ambientPoleKernel4 (ball (0 : Ambient9) 1) := by
  have hi := (sphereKernel4_ball_integrable_iff northPole8).mp sphereKernel4_northPole_integrable
  have hk : (fun z : Nonzero9 => sphereKernel4 northPole8 (sphereDirection8 z)) =
      fun z : Nonzero9 => ambientPoleKernel4 z := funext northPole8_direction_kernel
  rw [hk] at hi
  unfold sphereBallProbability8 sphereBallMeasure8 at hi
  have hi' := (integrable_inv_smul_measure (NeZero.ne (sphereArea8 univ))
    (by finiteness : sphereArea8 univ ≠ ⊤)).mp hi
  have hi'' := (integrable_smul_measure (by norm_num : (9 : ENNReal) ≠ 0)
    (by norm_num : (9 : ENNReal) ≠ ⊤)).mp hi'
  have he : MeasurableEmbedding (Subtype.val : Nonzero9 → Ambient9) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  rw [← unitBallNonzero9_preimage, ← he.comap_restrict] at hi''
  have hin : IntegrableOn ambientPoleKernel4 Nonzero9 (volume.restrict (ball 0 1)) := by
    apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Ambient9)).compl).mpr
    simpa only [Function.comp_def] using hi''
  change Integrable ambientPoleKernel4 ((volume.restrict (ball 0 1)).restrict {0}ᶜ) at hin
  rw [restrict_compl_singleton] at hin
  exact hin

theorem spherePotential4_northPole_ball :
    spherePotential4 northPole8 =
      (sphereArea8.real univ)⁻¹ * 9 * ∫ v in ball (0 : Ambient9) 1, ambientPoleKernel4 v := by
  rw [spherePotential4_ball_integral]
  simp_rw [northPole8_direction_kernel]
  unfold sphereBallProbability8 sphereBallMeasure8
  rw [integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  have he : MeasurableEmbedding (Subtype.val : Nonzero9 → Ambient9) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  have hint : (∫ z : Nonzero9, ambientPoleKernel4 z
      ∂((volume : Measure Ambient9).comap Subtype.val).restrict unitBallNonzero9) =
      ∫ v in ball (0 : Ambient9) 1, ambientPoleKernel4 v := by
    rw [← unitBallNonzero9_preimage, ← he.comap_restrict,
      integral_subtype_comap (measurableSet_singleton (0 : Ambient9)).compl ambientPoleKernel4]
    change (∫ v, ambientPoleKernel4 v ∂(volume.restrict (ball 0 1)).restrict {0}ᶜ) = _
    rw [restrict_compl_singleton]
  rw [hint]
  change (sphereArea8.real univ)⁻¹ * (9 * _) = _
  ring

def ambientPoleBallKernel4 : Ambient9 → ℝ := (ball 0 1).indicator ambientPoleKernel4

theorem ambientPoleBallKernel4_integrable : Integrable ambientPoleBallKernel4 :=
  (integrable_indicator_iff measurableSet_ball).mpr ambientPoleKernel4_unitBall_integrable

theorem ambientPoleBallKernel4_integral :
    (∫ v, ambientPoleBallKernel4 v) = ∫ v in ball (0 : Ambient9) 1, ambientPoleKernel4 v :=
  integral_indicator measurableSet_ball

#print axioms northPole8_dist_sq
#print axioms northPole8_kernel_coordinate
#print axioms northPole8_direction_kernel
#print axioms ambientPoleKernel4_unitBall_integrable
#print axioms spherePotential4_northPole_ball
#print axioms ambientPoleBallKernel4_integrable
#print axioms ambientPoleBallKernel4_integral

end SphericalRiesz
