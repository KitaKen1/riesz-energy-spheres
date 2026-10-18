import Riesz.EqualAreaRescalingGeometry8
import Riesz.E8SphereGraphEnergy

/-! The actual exact-area chart now supplies the relative-distance
input to the original-node near-potential comparison. The limit allows
any positive scale sequence tending to zero, with all original nodes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem equalAreaNormalizedE8Chart_continuous (ε : ℝ) :
    Continuous (equalAreaNormalizedE8Chart ε) := by
  unfold equalAreaNormalizedE8Chart equalAreaE8Chart
  exact (equalAreaPhi_continuous.comp (by fun_prop)).sub continuous_const |>.const_smul ε⁻¹

def equalAreaNearBackgroundDifference (ε R : ℝ) (m : ℕ) : ℝ :=
  (m:ℝ)^4*((cubeQuadrature 8 m (curvedNearPotential (equalAreaNormalizedE8Chart ε) (R/(m:ℝ)))-
      ∫ x in UnitCube 8, curvedNearPotential (equalAreaNormalizedE8Chart ε) (R/(m:ℝ)) x)-
    (cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
      ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))

theorem equalAreaNearBackgroundDifference_eventual_bound (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1/2) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ R : ℝ, 0 < R → ∀ m : ℕ, 8 ≤ m →
      |equalAreaNearBackgroundDifference ε R m| ≤ 128*η*e8NearIntegralConstant*R^4 := by
  filter_upwards [equalAreaNormalizedE8Chart_relative_distance_eventually η hη] with ε hdist R hR m hm
  exact curvedNearPotential_scaled_background_error (equalAreaNormalizedE8Chart ε)
    (equalAreaNormalizedE8Chart_continuous ε).measurable R hR η hη.le hη1 hdist m hm

theorem equalAreaNearBackgroundDifference_limit_along (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hp : ∀ᶠ m : ℕ in atTop, 0 < e m)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => equalAreaNearBackgroundDifference (e m) R m) atTop (𝓝 0) := by
  have hew : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ he hp
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let K : ℝ := 128*e8NearIntegralConstant*R^4
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (by norm_num) e8NearIntegralConstant_nonneg) (pow_nonneg hR.le 4)
  let η : ℝ := min (1/2) (δ/(2*(K+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/2 := min_le_left _ _
  have hbound := hew.eventually (equalAreaNearBackgroundDifference_eventual_bound η hη hη1)
  filter_upwards [hbound,eventually_ge_atTop (8:ℕ)] with m hb hm
  have h := hb R hR m hm
  rw [dist_zero_right]
  calc
    _ ≤ η*K := by simpa [K,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using h
    _ ≤ (δ/(2*(K+1)))*K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK
    _ < δ := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < 2*(K+1))).mpr
      nlinarith

def equalAreaNearBackground (ε R : ℝ) (m : ℕ) : ℝ :=
  (m:ℝ)^4*(cubeQuadrature 8 m (curvedNearPotential (equalAreaNormalizedE8Chart ε) (R/(m:ℝ)))-
    ∫ x in UnitCube 8, curvedNearPotential (equalAreaNormalizedE8Chart ε) (R/(m:ℝ)) x)

theorem equalAreaNearBackground_limit_along (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hp : ∀ᶠ m : ℕ in atTop, 0 < e m)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => equalAreaNearBackground (e m) R m) atTop (𝓝 0) := by
  have hflat : Tendsto (fun m : ℕ => (m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
      ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x)) atTop (𝓝 0) := by
    simpa only [e8ScaledNearBackground_eq] using e8ScaledNearPotential_background_limit R hR
  have h := (equalAreaNearBackgroundDifference_limit_along e he hp R hR).add hflat
  convert h using 1
  · funext m
    unfold equalAreaNearBackgroundDifference equalAreaNearBackground
    ring
  · simp

end SphericalRiesz
