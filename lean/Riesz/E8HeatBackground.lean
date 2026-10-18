import Riesz.E8HeatRegularized
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The continuous R8 background of the actual Gaussian-damped Riesz sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem gaussian_radial_cubic_integral {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi 0, r^3*Real.exp (-a*r^2)) = 1/(2*a^2) := by
  have h := integral_comp_rpow_Ioi (fun u : ℝ => u*Real.exp (-a*u)) (p := 2) (by norm_num)
  have hm := gaussianTailMoment_integral ha 0
  simp only [sub_zero, mul_zero, Real.exp_zero] at hm
  have he : (fun r : ℝ => (|(2 : ℝ)| * r^((2 : ℝ)-1)) •
      ((r^(2 : ℝ))*Real.exp (-a*(r^(2 : ℝ))))) =
      (fun r : ℝ => 2*(r^3*Real.exp (-a*r^2))) := by
    funext r
    norm_num [Real.rpow_two, smul_eq_mul]
    ring
  rw [he, integral_const_mul, hm] at h
  calc
    _ = (1/a^2)/2 := by linarith
    _ = _ := by ring

theorem e8Ambient_unit_ball_volume_real :
    volume.real (Metric.ball (0 : E8Ambient) 1) = Real.pi^4/24 := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 4) (by simp [E8Ambient])]
  norm_num [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^4/24)]

def e8HeatBackgroundKernel (ε : ℝ) (v : E8Ambient) : ℝ :=
  Real.exp (-Real.pi*ε*‖v‖^2)/‖v‖^4

theorem e8HeatBackgroundKernel_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ v : E8Ambient, e8HeatBackgroundKernel ε v) = Real.pi^2/(6*ε^2) := by
  unfold e8HeatBackgroundKernel
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => Real.exp (-Real.pi*ε*r^2)/r^4)]
  simp only [E8Ambient, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  rw [e8Ambient_unit_ball_volume_real]
  have hr : (∫ r : ℝ in Ioi 0, r^7*(Real.exp (-Real.pi*ε*r^2)/r^4)) =
      ∫ r : ℝ in Ioi 0, r^3*Real.exp (-(Real.pi*ε)*r^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change r^7*(Real.exp (-Real.pi*ε*r^2)/r^4) = r^3*Real.exp (-(Real.pi*ε)*r^2)
    rw [show -Real.pi*ε*r^2 = -(Real.pi*ε)*r^2 by ring]
    field_simp
  rw [hr, gaussian_radial_cubic_integral (mul_pos Real.pi_pos hε)]
  field_simp [Real.pi_ne_zero, hε.ne']
  ring

theorem e8HeatBackgroundKernel_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (e8HeatBackgroundKernel ε) := by
  apply Integrable.of_integral_ne_zero
  rw [e8HeatBackgroundKernel_integral hε]
  positivity

def e8HeatDefect (ε : ℝ) : ℝ := e8HeatEnergy ε - ∫ v : E8Ambient, e8HeatBackgroundKernel ε v

theorem e8HeatDefect_eq {ε : ℝ} (hε : 0 < ε) :
    e8HeatDefect ε = e8HeatRegularizedEnergy ε := by
  unfold e8HeatDefect e8HeatRegularizedEnergy
  rw [e8HeatBackgroundKernel_integral hε]

theorem e8HeatDefect_limit :
    Tendsto e8HeatDefect (𝓝[>] (0 : ℝ)) (𝓝 (-5*Real.pi^2/6)) := by
  apply e8HeatRegularizedEnergy_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (e8HeatDefect_eq hε).symm

#print axioms gaussian_radial_cubic_integral
#print axioms e8Ambient_unit_ball_volume_real
#print axioms e8HeatBackgroundKernel_integral
#print axioms e8HeatBackgroundKernel_integrable
#print axioms e8HeatDefect_eq
#print axioms e8HeatDefect_limit

end SphericalRiesz
