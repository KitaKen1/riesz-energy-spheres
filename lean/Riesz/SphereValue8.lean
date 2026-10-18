import Riesz.SpherePole8
import Riesz.SpherePolePolar8

/-!
Exact value of the actual normalized inverse-fourth spherical potential.
All coordinate, radial and polar integrations use the actual Lebesgue
measures. The sharp regularized E8 lattice coefficient remains separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

abbrev PoleTransverse8 := EuclideanSpace ℝ (Fin 8)

theorem ambientCons9_norm_sq (p : ℝ × (Fin 8 → ℝ)) :
    ‖ambientCons9 p‖ ^ 2 = p.1 ^ 2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse8)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [ambientCons9_apply, Fin.sum_univ_succ]

theorem ambientCons9_norm (p : ℝ × (Fin 8 → ℝ)) :
    ‖ambientCons9 p‖ = Real.sqrt (p.1^2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse8)‖^2) := by
  rw [← ambientCons9_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem ambientPoleBallKernel4_split (p : ℝ × (Fin 8 → ℝ)) :
    ambientPoleBallKernel4 (ambientCons9 p) =
      poleRadialKernel4 p.1 ‖(WithLp.toLp 2 p.2 : PoleTransverse8)‖ := by
  have hi : ‖ambientCons9 p‖ < 1 ↔
      p.1^2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse8)‖^2 < 1 := by
    rw [← ambientCons9_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (ambientCons9 p)]
  have hz : ambientCons9 p 0 = p.1 := by simp [ambientCons9_apply]
  unfold ambientPoleBallKernel4 ambientPoleKernel4 poleRadialKernel4
  simp only [indicator, mem_ball, dist_zero_right]
  simp only [hi]
  rw [hz, ambientCons9_norm]

theorem poleTransverse8_unit_ball_volume :
    (volume : Measure PoleTransverse8).real (ball 0 1) = Real.pi^4 / 24 := by
  have hv : volume (ball (0 : PoleTransverse8) 1) = ENNReal.ofReal (Real.pi^4 / 24) := by
    rw [InnerProductSpace.volume_ball_of_dim_even (k := 4) (by simp [PoleTransverse8])]
    norm_num [PoleTransverse8]
  rw [Measure.real, hv, ENNReal.toReal_ofReal]
  positivity

theorem poleRadialKernel4_transverse_integral (a : ℝ) :
    (∫ u : Fin 8 → ℝ, poleRadialKernel4 a ‖(WithLp.toLp 2 u : PoleTransverse8)‖) =
      (Real.pi^4 / 3) * ∫ r : ℝ, poleHalfPlane4 (a,r) := by
  calc
    _ = ∫ u : PoleTransverse8, poleRadialKernel4 a ‖u‖ :=
      (PiLp.volume_preserving_toLp (Fin 8)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)).measurableEmbedding _
    _ = (Real.pi^4 / 3) * ∫ r : ℝ, poleHalfPlane4 (a,r) := by
      rw [integral_fun_norm_addHaar (volume : Measure PoleTransverse8)]
      simp only [PoleTransverse8, finrank_euclideanSpace_fin, Nat.reduceSub,
        smul_eq_mul, poleTransverse8_unit_ball_volume]
      rw [poleHalfPlane4_radial_integral]
      ring

theorem ambientPoleBallKernel4_integral_value :
    (∫ v : Ambient9, ambientPoleBallKernel4 v) = 2 * Real.pi^4 / 135 := by
  have hi : Integrable (ambientPoleBallKernel4 ∘ ambientCons9) :=
    ambientCons9_measurePreserving.integrable_comp_of_integrable ambientPoleBallKernel4_integrable
  calc
    _ = ∫ p : ℝ × (Fin 8 → ℝ), ambientPoleBallKernel4 (ambientCons9 p) :=
      (ambientCons9_measurePreserving.integral_comp' ambientPoleBallKernel4).symm
    _ = ∫ a : ℝ, ∫ u : Fin 8 → ℝ, ambientPoleBallKernel4 (ambientCons9 (a,u)) :=
      integral_prod _ hi
    _ = ∫ a : ℝ, (Real.pi^4 / 3) * ∫ r : ℝ, poleHalfPlane4 (a,r) := by
      simp_rw [ambientPoleBallKernel4_split, poleRadialKernel4_transverse_integral]
    _ = _ := by
      rw [integral_const_mul, poleHalfPlane4_iterated_integral]
      ring

theorem spherePotential4_northPole_value : spherePotential4 northPole8 = 7 / 16 := by
  rw [spherePotential4_northPole_ball, ← ambientPoleBallKernel4_integral,
    ambientPoleBallKernel4_integral_value, sphereArea8_mass_real]
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

theorem spherePotential4_value (p : Sphere8) : spherePotential4 p = 7 / 16 := by
  rw [spherePotential4_constant p northPole8]
  exact spherePotential4_northPole_value

theorem sphereKernel4_pair_integral_value :
    (∫ p : Sphere8 × Sphere8, sphereKernel4 p.1 p.2
      ∂sphereProbability8.prod sphereProbability8) = 7 / 16 := by
  rw [integral_prod _ sphereKernel4_pair_integrable]
  change (∫ p : Sphere8, spherePotential4 p ∂sphereProbability8) = _
  simp_rw [spherePotential4_value]
  simp

#print axioms ambientCons9_norm_sq
#print axioms ambientCons9_norm
#print axioms ambientPoleBallKernel4_split
#print axioms poleTransverse8_unit_ball_volume
#print axioms poleRadialKernel4_transverse_integral
#print axioms ambientPoleBallKernel4_integral_value
#print axioms spherePotential4_northPole_value
#print axioms spherePotential4_value
#print axioms sphereKernel4_pair_integral_value

end SphericalRiesz
