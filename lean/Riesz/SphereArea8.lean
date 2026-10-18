import Riesz.SphereMeasure8
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
Numerical mass of the actual sphere measure and the normalization of the
predicted coefficient. The regularized E8 constant is not evaluated here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
namespace SphericalRiesz

theorem ambient9_unit_ball_volume :
    volume (ball (0 : Ambient9) 1) = ENNReal.ofReal (32 * Real.pi ^ 4 / 945) := by
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 4) (by simp [Ambient9])]
  norm_num [Ambient9]
  congr 1
  ring

theorem sphereArea8_mass :
    sphereArea8 univ = ENNReal.ofReal (32 * Real.pi ^ 4 / 105) := by
  rw [sphereArea8, Measure.toSphere_apply_univ, ambient9_unit_ball_volume]
  simp only [Ambient9, finrank_euclideanSpace_fin]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (9 : ℕ))]
  congr 1
  ring

theorem sphereArea8_mass_real :
    sphereArea8.real univ = 32 * Real.pi ^ 4 / 105 := by
  rw [Measure.real, sphereArea8_mass, ENNReal.toReal_ofReal]
  positivity

theorem sphereProbability8_normalization :
    sphereProbability8 = ENNReal.ofReal (105 / (32 * Real.pi ^ 4)) • sphereArea8 := by
  unfold sphereProbability8
  rw [sphereArea8_mass, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 2
  field_simp

/-- Only the area factor is identified: the E8 value -5*pi^2/6 is still an analytic gate. -/
theorem predictedCoefficient_area_normalization :
    predictedCoefficient = (-5 * Real.pi ^ 2 / 6) / Real.sqrt (sphereArea8.real univ) := by
  have hs : Real.sqrt (210 : ℝ) ^ 2 = 210 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (210 : ℝ) := by positivity
  have harea : Real.sqrt (sphereArea8.real univ) =
      8 * Real.pi ^ 2 / Real.sqrt (210 : ℝ) := by
    rw [sphereArea8_mass_real]
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    field_simp
    rw [hs]
    ring
  rw [harea, predictedCoefficient]
  field_simp
  ring

#print axioms ambient9_unit_ball_volume
#print axioms sphereArea8_mass
#print axioms sphereArea8_mass_real
#print axioms sphereProbability8_normalization
#print axioms predictedCoefficient_area_normalization

end SphericalRiesz
