import Riesz.E8HeatBackground
import Riesz.E8NearIntegral

/-! The checked actual heat background in the original basis coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
namespace SphericalRiesz

def e8CoordinateGaussian (ε : ℝ) (y : Fin 8 → ℝ) : ℝ :=
  Real.exp (-Real.pi*ε*‖(WithLp.toLp 2 (e8Map y) : E8Ambient)‖^2)

def e8CoordinateHeatKernel (ε : ℝ) (y : Fin 8 → ℝ) : ℝ :=
  obliqueRieszFour 8 e8Map 0 y * e8CoordinateGaussian ε y

theorem e8CoordinateGaussian_continuous (ε : ℝ) : Continuous (e8CoordinateGaussian ε) := by
  unfold e8CoordinateGaussian
  fun_prop

theorem e8CoordinateGaussian_zero (y : Fin 8 → ℝ) : e8CoordinateGaussian 0 y = 1 := by
  simp [e8CoordinateGaussian]

theorem e8CoordinateGaussian_bounds {ε : ℝ} (hε : 0 ≤ ε) (y : Fin 8 → ℝ) :
    0 ≤ e8CoordinateGaussian ε y ∧ e8CoordinateGaussian ε y ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    dsimp only [e8CoordinateGaussian]
    have h := mul_nonneg (mul_nonneg Real.pi_pos.le hε) (sq_nonneg
      ‖(WithLp.toLp 2 (e8Map y) : E8Ambient)‖)
    nlinarith

theorem e8CoordinateHeatKernel_eq (ε : ℝ) (y : Fin 8 → ℝ) :
    e8CoordinateHeatKernel ε y = e8HeatBackgroundKernel ε (WithLp.toLp 2 (e8Map y)) := by
  unfold e8CoordinateHeatKernel e8CoordinateGaussian e8HeatBackgroundKernel
  rw [obliqueRieszFour_eq_dist]
  simp only [map_zero, WithLp.toLp_zero, dist_zero_left, inv_pow]
  ring

theorem e8CoordinateHeatKernel_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ y : Fin 8 → ℝ, e8CoordinateHeatKernel ε y) = Real.pi^2/(6*ε^2) := by
  simp_rw [e8CoordinateHeatKernel_eq]
  calc
    _ = ∫ y : Fin 8 → ℝ, e8HeatBackgroundKernel ε (WithLp.toLp 2 y) :=
      e8Map_measurePreserving.integral_comp e8Map_measurableEmbedding _
    _ = ∫ v : E8Ambient, e8HeatBackgroundKernel ε v :=
      (PiLp.volume_preserving_toLp (Fin 8)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)).measurableEmbedding _
    _ = _ := e8HeatBackgroundKernel_integral hε

theorem e8CoordinateHeatKernel_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (e8CoordinateHeatKernel ε) := by
  apply Integrable.of_integral_ne_zero
  rw [e8CoordinateHeatKernel_integral hε]
  positivity

theorem e8CoordinateHeatKernel_integer (ε : ℝ) (z : Fin 8 → ℤ) :
    e8CoordinateHeatKernel ε (fun i => (z i : ℝ)) = e8HeatTerm ε z := by
  rw [e8CoordinateHeatKernel_eq]
  change e8HeatBackgroundKernel ε (e8EuclideanPoint z) = _
  by_cases hz : z = 0
  · subst z
    simp [e8HeatTerm, e8HeatBackgroundKernel]
  · simp only [e8HeatTerm, if_neg hz, e8HeatBackgroundKernel]

theorem e8CoordinateHeatKernel_tsum (ε : ℝ) :
    (∑' z : Fin 8 → ℤ, e8CoordinateHeatKernel ε (fun i => (z i : ℝ))) = e8HeatEnergy ε := by
  simp only [e8CoordinateHeatKernel_integer, e8HeatEnergy]

#print axioms e8CoordinateGaussian_continuous
#print axioms e8CoordinateGaussian_zero
#print axioms e8CoordinateGaussian_bounds
#print axioms e8CoordinateHeatKernel_eq
#print axioms e8CoordinateHeatKernel_integral
#print axioms e8CoordinateHeatKernel_integrable
#print axioms e8CoordinateHeatKernel_integer
#print axioms e8CoordinateHeatKernel_tsum

end SphericalRiesz
