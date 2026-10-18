import Riesz.E8PotentialApprox
import Riesz.CubeLebesgue
import Riesz.SingularQuadrature
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual regularized E8 potentials and removal of regularization

The cutoff kernel is smooth on the whole coordinate space. To prove
smoothness of its actual cube potential, multiply the kernel by one
large compact window and convolve with the actual cube indicator.
The window is one throughout a neighborhood of every point of the cube.
This reuses mathlib's smooth convolution theorem instead of building
high-order differentiation under an integral from scratch.

Uniform near removal also proves continuity of the actual singular
potential and transfers a quadrature estimate from all cutoff radii.
The uniform sixth derivative bound is still a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Topology ContDiff

namespace SphericalRiesz
open Boundary

def e8FarProfile (r : ℝ) (v : Fin 8 → ℝ) : ℝ :=
  farObliqueRieszFour 8 e8Map r 0 v

theorem e8FarProfile_contDiff (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (e8FarProfile r) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst v
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Fin 8 → ℝ) (by positivity : 0 < r/2)] with v hv
    have hn : ‖v‖ < r/2 := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    exact farObliqueRieszFour_zero_inside 8 e8Map r hr 0 v (by
      simpa only [sub_zero] using hn.le)
  · have hAv : e8Map v ≠ 0 := fun h => hv (e8Map_injective (by simpa only [map_zero] using h))
    have hq : squaredDistance 8 0 (e8Map v) ≠ 0 :=
      fun h => hAv ((squaredDistance_zero_iff 8 (e8Map v)).mp h)
    have hk : ContDiffAt ℝ ∞ (fun z => obliqueRieszFour 8 e8Map 0 z) v := by
      unfold obliqueRieszFour flatRieszFour
      simp only [sub_zero]
      apply ContDiffAt.div contDiffAt_const
      · unfold squaredDistance
        fun_prop
      · exact pow_ne_zero 2 hq
    exact hk.sub (hk.mul ((outerUnitBump 8).contDiff.comp (by fun_prop)).contDiffAt)

theorem e8Far_translation (r : ℝ) (x y : Fin 8 → ℝ) :
    farObliqueRieszFour 8 e8Map r x y = e8FarProfile r (y-x) := by
  simp only [e8FarProfile, farObliqueRieszFour, nearObliqueRieszFour, obliqueRieszFour,
    sub_zero]

theorem e8Far_joint_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (fun p : (Fin 8 → ℝ) × (Fin 8 → ℝ) =>
      farObliqueRieszFour 8 e8Map r p.1 p.2) := by
  simp_rw [e8Far_translation]
  exact (e8FarProfile_contDiff r hr).comp (contDiff_snd.sub contDiff_fst)

theorem e8FarPotential_continuous (r : ℝ) (hr : 0 < r) : Continuous (e8FarPotential r) := by
  have h := continuous_cubeIntegral_param 8
    (F := fun x y => farObliqueRieszFour 8 e8Map r x y) (e8Far_joint_contDiff r hr).continuous
  have heq : (fun x => cubeIntegral 8 (farObliqueRieszFour 8 e8Map r x)) = e8FarPotential r := by
    funext x
    have hc : Continuous (farObliqueRieszFour 8 e8Map r x) := by
      change Continuous (fun y => farObliqueRieszFour 8 e8Map r x y)
      simp_rw [e8Far_translation]
      exact (e8FarProfile_contDiff r hr).continuous.comp (continuous_id.sub continuous_const)
    change cubeIntegral 8 (farObliqueRieszFour 8 e8Map r x) =
      ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r x y
    exact cubeIntegral_eq_setIntegral 8 _ hc
  rw [heq] at h
  exact h

def e8WindowedFarProfile (r : ℝ) (v : Fin 8 → ℝ) : ℝ :=
  e8FarProfile r (-v)*outerUnitBump 8 ((4:ℝ)⁻¹ • v)

theorem e8WindowedFarProfile_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (e8WindowedFarProfile r) :=
  ((e8FarProfile_contDiff r hr).comp contDiff_neg).mul
    ((outerUnitBump 8).contDiff.comp (by fun_prop))

theorem e8WindowedFarProfile_hasCompactSupport (r : ℝ) :
    HasCompactSupport (e8WindowedFarProfile r) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Fin 8 → ℝ) 8)
    Metric.isClosed_closedBall
  intro v hv
  have hn : 8 < ‖v‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hv
  have hb : outerUnitBump 8 ((4:ℝ)⁻¹ • v) = 0 := by
    apply (outerUnitBump 8).zero_of_le_dist
    change 2 ≤ dist ((4:ℝ)⁻¹ • v) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  simp only [e8WindowedFarProfile, hb, mul_zero]

def e8WindowedPotential (r : ℝ) : (Fin 8 → ℝ) → ℝ :=
  convolution ((UnitCube 8).indicator (fun _ => (1:ℝ))) (e8WindowedFarProfile r)
    (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem e8WindowedPotential_contDiff (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (e8WindowedPotential r) := by
  have hi : Integrable ((UnitCube 8).indicator (fun _ => (1:ℝ))) := by
    rw [integrable_indicator_iff (unitCube_measurableSet 8)]
    exact continuousOn_const.integrableOn_compact (unitCube_isCompact 8)
  exact (e8WindowedFarProfile_hasCompactSupport r).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hi.locallyIntegrable (e8WindowedFarProfile_contDiff r hr)

theorem e8WindowedPotential_eq_near_cube (r : ℝ) (x₀ : Fin 8 → ℝ) (hx₀ : x₀ ∈ UnitCube 8)
    (x : Fin 8 → ℝ) (hx : x ∈ Metric.ball x₀ 1) :
    e8WindowedPotential r x = e8FarPotential r x := by
  have hx0 : ‖x-x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hxn : ‖x‖ ≤ ‖x-x₀‖+‖x₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-x₀) x₀
  have heq : e8WindowedPotential r x = ∫ y in UnitCube 8, e8WindowedFarProfile r (x-y) := by
    unfold e8WindowedPotential convolution
    rw [← integral_indicator (unitCube_measurableSet 8)]
    congr 1
    funext y
    by_cases hy : y ∈ UnitCube 8 <;>
      simp [hy, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [heq]
  change (∫ y in UnitCube 8, e8WindowedFarProfile r (x-y)) =
    ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r x y
  apply setIntegral_congr_fun (unitCube_measurableSet 8)
  intro y hy
  have hxy : ‖x-y‖ ≤ 4 := by
    have h1 := norm_sub_le x y
    have h2 := unitCube_norm_le_one 8 x₀ hx₀
    have h3 := unitCube_norm_le_one 8 y hy
    linarith
  have hb : outerUnitBump 8 ((4:ℝ)⁻¹ • (x-y)) = 1 := by
    apply (outerUnitBump 8).one_of_mem_closedBall
    change ((4:ℝ)⁻¹ • (x-y)) ∈ Metric.closedBall 0 1
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  change e8FarProfile r (-(x-y))*outerUnitBump 8 ((4:ℝ)⁻¹ • (x-y)) =
    farObliqueRieszFour 8 e8Map r x y
  rw [hb, mul_one, neg_sub, ← e8Far_translation]

theorem e8FarPotential_contDiffOn_cube (r : ℝ) (hr : 0 < r) :
    ContDiffOn ℝ ∞ (e8FarPotential r) (UnitCube 8) := by
  intro x hx
  have heq : e8FarPotential r =ᶠ[𝓝 x] e8WindowedPotential r := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1)] with y hy
    exact (e8WindowedPotential_eq_near_cube r x hx y hy).symm
  exact ((e8WindowedPotential_contDiff r hr).contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

theorem e8Potential_continuous : Continuous e8Potential := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr, hb⟩ := e8Potential_far_uniform (ε/4) (by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (e8FarPotential_continuous r hr).continuousAt (ε/4) (by positivity)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h1 := dist_triangle (e8Potential y) (e8FarPotential r y) (e8Potential x)
  have h2 := dist_triangle (e8FarPotential r y) (e8FarPotential r x) (e8Potential x)
  have h3 := hb y
  have h4 := hb x
  have h5 := hd hy
  simp only [Real.dist_eq] at h1 h2 h5 ⊢
  rw [abs_sub_comm (e8FarPotential r x) (e8Potential x)] at h2
  linarith

theorem e8Potential_far_integral_error (r : ℝ) (hr : 0 < r) :
    |(∫ x in UnitCube 8, e8Potential x)-(∫ x in UnitCube 8, e8FarPotential r x)| ≤
      e8NearIntegralConstant*(r/2)^4 := by
  rw [← cubeIntegral_eq_setIntegral 8 _ e8Potential_continuous,
    ← cubeIntegral_eq_setIntegral 8 _ (e8FarPotential_continuous r hr),
    ← cubeIntegral_sub 8 _ _ e8Potential_continuous (e8FarPotential_continuous r hr)]
  exact cubeIntegral_abs_le 8 _ _ (fun x _ => e8Potential_far_error r hr x)

theorem e8Potential_quadrature_error_transfer {m : ℕ} (hm : 8 ≤ m) (r : ℝ) (hr : 0 < r) :
    |cubeQuadrature 8 m e8Potential-∫ x in UnitCube 8, e8Potential x| ≤
      |cubeQuadrature 8 m (e8FarPotential r)-∫ x in UnitCube 8, e8FarPotential r x|+
        2*e8NearIntegralConstant*(r/2)^4 := by
  have h1 := abs_sub_le (cubeQuadrature 8 m e8Potential)
    (cubeQuadrature 8 m (e8FarPotential r)) (∫ x in UnitCube 8, e8Potential x)
  have h2 := abs_sub_le (cubeQuadrature 8 m (e8FarPotential r))
    (∫ x in UnitCube 8, e8FarPotential r x) (∫ x in UnitCube 8, e8Potential x)
  have h3 := e8Potential_far_quadrature_error hm r hr
  have h4 := e8Potential_far_integral_error r hr
  rw [abs_sub_comm (∫ x in UnitCube 8, e8FarPotential r x) (∫ x in UnitCube 8, e8Potential x)] at h2
  linarith

/-- Only a bound uniform in the actual cutoff radius is an admissible input. -/
theorem e8Potential_background_bound_of_far (C : ℝ)
    (hb : ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r →
      |cubeQuadrature 8 m (e8FarPotential r)-∫ x in UnitCube 8, e8FarPotential r x|
        ≤ C/(m:ℝ)^5) (m : ℕ) (hm : 8 ≤ m) :
    |cubeQuadrature 8 m e8Potential-∫ x in UnitCube 8, e8Potential x| ≤ C/(m:ℝ)^5 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, ha⟩ := e8Potential_far_uniform (ε/4) (by positivity)
  have hq : |cubeQuadrature 8 m e8Potential-cubeQuadrature 8 m (e8FarPotential r)| ≤ ε/4 := by
    rw [← cubeQuadrature_sub]
    exact cubeQuadrature_abs_le 8 m hm _ _ (fun x _ => ha x)
  have hi : |(∫ x in UnitCube 8, e8Potential x)-(∫ x in UnitCube 8, e8FarPotential r x)| ≤ ε/4 := by
    rw [← cubeIntegral_eq_setIntegral 8 _ e8Potential_continuous,
      ← cubeIntegral_eq_setIntegral 8 _ (e8FarPotential_continuous r hr),
      ← cubeIntegral_sub 8 _ _ e8Potential_continuous (e8FarPotential_continuous r hr)]
    exact cubeIntegral_abs_le 8 _ _ (fun x _ => ha x)
  have h1 := abs_sub_le (cubeQuadrature 8 m e8Potential)
    (cubeQuadrature 8 m (e8FarPotential r)) (∫ x in UnitCube 8, e8Potential x)
  have h2 := abs_sub_le (cubeQuadrature 8 m (e8FarPotential r))
    (∫ x in UnitCube 8, e8FarPotential r x) (∫ x in UnitCube 8, e8Potential x)
  rw [abs_sub_comm (∫ x in UnitCube 8, e8FarPotential r x) (∫ x in UnitCube 8, e8Potential x)] at h2
  have h3 := hb m hm r hr
  linarith

theorem e8FarPotential_slice_contDiffOn (r : ℝ) (hr : 0 < r) (i : Fin 8)
    (v : Fin 8 → ℝ) (hv : v ∈ UnitCube 8) :
    ContDiffOn ℝ 6 (fun t => e8FarPotential r (Function.update v i t)) (Set.Icc (0:ℝ) 1) := by
  have hf : ContDiffOn ℝ 6 (e8FarPotential r) (UnitCube 8) :=
    (e8FarPotential_contDiffOn_cube r hr).of_le (by simp)
  have hu : ContDiffOn ℝ 6 (fun t : ℝ => Function.update v i t) (Set.Icc (0:ℝ) 1) :=
    (contDiff_update 6 v i).contDiffOn
  exact hf.comp hu (fun t ht => update_mem_unitCube hv i ht)

/-- The remaining analytic input is the uniform pure sixth derivative bound. -/
theorem e8Potential_background_bound_of_derivative (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ r : ℝ, 0 < r → ∀ i v, v ∈ UnitCube 8 → ∀ t ∈ Set.Ioo (0:ℝ) 1,
      |iteratedDerivWithin 6 (fun u => e8FarPotential r (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t| ≤ A*(t⁻¹^2+(1-t)⁻¹^2))
    (m : ℕ) (hm : 8 ≤ m) :
    |cubeQuadrature 8 m e8Potential-∫ x in UnitCube 8, e8Potential x| ≤ (16777216*A)/(m:ℝ)^5 := by
  apply e8Potential_background_bound_of_far (16777216*A) _ m hm
  intro m hm r hr
  have h := cubeQuadrature_singular_sixth_order_bound_on 8 hm
    (e8FarPotential_continuous r hr).continuousOn
    (fun i v hv => e8FarPotential_slice_contDiffOn r hr i v hv)
    (fun _ => A) (fun _ => hA) (hb r hr)
  calc
    _ ≤ (2097152/(m:ℝ)^5)*(∑ _ : Fin 8, A) := h
    _ = _ := by simp; ring

#print axioms e8FarProfile_contDiff
#print axioms e8Far_translation
#print axioms e8Far_joint_contDiff
#print axioms e8FarPotential_continuous
#print axioms e8WindowedFarProfile_contDiff
#print axioms e8WindowedFarProfile_hasCompactSupport
#print axioms e8WindowedPotential_contDiff
#print axioms e8WindowedPotential_eq_near_cube
#print axioms e8FarPotential_contDiffOn_cube
#print axioms e8Potential_continuous
#print axioms e8Potential_far_integral_error
#print axioms e8Potential_quadrature_error_transfer
#print axioms e8Potential_background_bound_of_far
#print axioms e8FarPotential_slice_contDiffOn
#print axioms e8Potential_background_bound_of_derivative

end SphericalRiesz
