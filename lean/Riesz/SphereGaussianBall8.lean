import Riesz.SphereGaussianBackground8
import Riesz.SpherePole8

/-! The actual Gaussian sphere background as an actual ambient-ball integral.
The direction map is the previously checked measure-preserving map. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

theorem northPole8_gaussian_coordinate (t : ℝ) (q : Sphere8) :
    sphereGaussianKernel8 t northPole8 q =
      Real.exp (-(t*(2-2*(q:Ambient9) 0))) := by
  unfold sphereGaussianKernel8
  rw [northPole8_dist_sq]

def ambientPoleGaussian8 (t : ℝ) (v : Ambient9) : ℝ :=
  Real.exp (-(t*(2-2*v 0/‖v‖)))

theorem ambientPoleGaussian8_measurable (t : ℝ) : Measurable (ambientPoleGaussian8 t) := by
  unfold ambientPoleGaussian8
  fun_prop

theorem northPole8_direction_gaussian (t : ℝ) (z : Nonzero9) :
    sphereGaussianKernel8 t northPole8 (sphereDirection8 z) = ambientPoleGaussian8 t z := by
  rw [northPole8_gaussian_coordinate, sphereDirection8_coe]
  unfold ambientPoleGaussian8
  simp only [PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv]
  congr 2
  ring

theorem sphereGaussianPotential8_ball_integral (t : ℝ) (p : Sphere8) :
    sphereGaussianPotential8 t p =
      ∫ z, sphereGaussianKernel8 t p (sphereDirection8 z) ∂sphereBallProbability8 := by
  unfold sphereGaussianPotential8
  rw [← sphereBallProbability8_direction_preserving.map_eq]
  exact integral_map sphereDirection8_measurable.aemeasurable (by unfold sphereGaussianKernel8; fun_prop)

theorem gaussian_unitBallNonzero9_preimage :
    (Subtype.val : Nonzero9 → Ambient9) ⁻¹' ball 0 1 = unitBallNonzero9 := by
  ext z
  simp [unitBallNonzero9]

theorem ambientPoleGaussian8_unitBall_integrable {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (ambientPoleGaussian8 t) (ball (0:Ambient9) 1) := by
  have hi := sphereBallProbability8_direction_preserving.integrable_comp
    (by unfold sphereGaussianKernel8; fun_prop : AEStronglyMeasurable
      (sphereGaussianKernel8 t northPole8) sphereProbability8)
  have h := hi.mpr (sphereGaussianKernel8_integrable ht northPole8)
  change Integrable (fun z : Nonzero9 => sphereGaussianKernel8 t northPole8 (sphereDirection8 z))
    sphereBallProbability8 at h
  simp_rw [northPole8_direction_gaussian] at h
  unfold sphereBallProbability8 sphereBallMeasure8 at h
  have h' := (integrable_inv_smul_measure (NeZero.ne (sphereArea8 univ))
    (by finiteness : sphereArea8 univ ≠ ⊤)).mp h
  have h'' := (integrable_smul_measure (by norm_num : (9:ENNReal) ≠ 0)
    (by norm_num : (9:ENNReal) ≠ ⊤)).mp h'
  have he : MeasurableEmbedding (Subtype.val : Nonzero9 → Ambient9) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  rw [← gaussian_unitBallNonzero9_preimage, ← he.comap_restrict] at h''
  have hin : IntegrableOn (ambientPoleGaussian8 t) Nonzero9 (volume.restrict (ball 0 1)) := by
    apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:Ambient9)).compl).mpr
    simpa only [Function.comp_def] using h''
  change Integrable (ambientPoleGaussian8 t) ((volume.restrict (ball 0 1)).restrict {0}ᶜ) at hin
  rw [restrict_compl_singleton] at hin
  exact hin

theorem sphereGaussianBackground8_ball {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground8 t =
      (sphereArea8.real univ)⁻¹*9*∫ v in ball (0:Ambient9) 1, ambientPoleGaussian8 t v := by
  rw [sphereGaussianBackground8_eq_potential ht northPole8,
    sphereGaussianPotential8_ball_integral]
  simp_rw [northPole8_direction_gaussian]
  unfold sphereBallProbability8 sphereBallMeasure8
  rw [integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  have he : MeasurableEmbedding (Subtype.val : Nonzero9 → Ambient9) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  have hint : (∫ z : Nonzero9, ambientPoleGaussian8 t z
      ∂((volume:Measure Ambient9).comap Subtype.val).restrict unitBallNonzero9) =
      ∫ v in ball (0:Ambient9) 1, ambientPoleGaussian8 t v := by
    rw [← gaussian_unitBallNonzero9_preimage, ← he.comap_restrict,
      integral_subtype_comap (measurableSet_singleton (0:Ambient9)).compl (ambientPoleGaussian8 t)]
    change (∫ v, ambientPoleGaussian8 t v ∂(volume.restrict (ball 0 1)).restrict {0}ᶜ) = _
    rw [restrict_compl_singleton]
  rw [hint]
  change (sphereArea8.real univ)⁻¹*(9*_) = _
  ring

def ambientPoleGaussianBall8 (t : ℝ) : Ambient9 → ℝ :=
  (ball 0 1).indicator (ambientPoleGaussian8 t)

theorem ambientPoleGaussianBall8_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (ambientPoleGaussianBall8 t) :=
  (integrable_indicator_iff measurableSet_ball).mpr (ambientPoleGaussian8_unitBall_integrable ht)

theorem ambientPoleGaussianBall8_integral (t : ℝ) :
    (∫ v, ambientPoleGaussianBall8 t v) = ∫ v in ball (0:Ambient9) 1, ambientPoleGaussian8 t v :=
  integral_indicator measurableSet_ball

end SphericalRiesz
