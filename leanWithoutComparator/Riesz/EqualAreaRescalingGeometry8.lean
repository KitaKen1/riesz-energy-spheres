import Riesz.EqualAreaRescalingLimit8

/-! The actual rescaled exact-area chart approaches the flat E8 map
also in order zero.  The mean value theorem transfers first derivative
control to two-point increments, including the boundary of the cube. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem unitCube8_convex : Convex ℝ (UnitCube 8) := by
  rw [unitCube_eq_pi]
  exact convex_pi (fun _ _ => convex_Icc (0:ℝ) 1)

theorem equalAreaNormalizedE8Chart_zero (ε : ℝ) :
    equalAreaNormalizedE8Chart ε 0 = 0 := by
  simp [equalAreaNormalizedE8Chart,equalAreaE8Chart]

theorem equalAreaNormalizedE8Chart_increment_error (ε : ℝ) (hε : 0 < ε)
    (hs : ε*equalAreaScaleRadius ≤ 1/8) (C : ℝ)
    (hb : ∀ x ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Chart ε) x-equalAreaFlatDerivative8‖ ≤ C)
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    ‖(equalAreaNormalizedE8Chart ε y-equalAreaFlatDerivative8 y)-
      (equalAreaNormalizedE8Chart ε x-equalAreaFlatDerivative8 x)‖ ≤ C*‖y-x‖ := by
  apply unitCube8_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ (equalAreaNormalizedE8Chart ε) z-equalAreaFlatDerivative8) _ hb hx hy
  intro z hz
  have hn : ‖ε • e8Map z‖ ≤ 1/8 := (equalAreaScaledE8_cube_norm ε z hz).trans
    (by simpa only [abs_of_pos hε] using hs)
  have hg := equalAreaNormalizedE8Chart_hasFDerivAt ε hε.ne' z (equalArea_small_norm_domain _ hn)
  rw [hg.fderiv]
  exact (hg.sub equalAreaFlatDerivative8.hasFDerivAt).hasFDerivWithinAt

theorem equalAreaNormalizedE8Chart_uniform_limit :
    TendstoUniformlyOn equalAreaNormalizedE8Chart (fun x => ambientCons9 (0,e8Map x))
      (𝓝[>] (0:ℝ)) (UnitCube 8) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hfirst := (Metric.tendstoUniformlyOn_iff.mp equalAreaNormalizedE8Chart_first_uniform_limit)
    (η/2) (by positivity)
  have ht : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hfirst] with ε hε hs hb x hx
  have hC : ∀ z ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Chart ε) z-equalAreaFlatDerivative8‖ ≤ η/2 := by
    intro z hz
    simpa only [dist_eq_norm, norm_sub_rev] using (hb z hz).le
  have h := equalAreaNormalizedE8Chart_increment_error ε hε hs.le (η/2) hC 0 x
    (fun _ => by constructor <;> norm_num) hx
  simp only [equalAreaNormalizedE8Chart_zero,map_zero,sub_zero] at h
  have hn := unitCube_norm_le_one 8 x hx
  rw [←equalAreaFlatDerivative8_apply,dist_eq_norm,norm_sub_rev]
  -- Use a smaller derivative tolerance to retain a strict final bound.
  exact (h.trans (mul_le_of_le_one_right (by positivity) hn)).trans_lt (by linarith)

theorem equalAreaFlatDerivative8_dist (x y : Fin 8 → ℝ) :
    dist (equalAreaFlatDerivative8 x) (equalAreaFlatDerivative8 y) =
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  rw [equalAreaFlatDerivative8_apply,equalAreaFlatDerivative8_apply]
  have h := ambientCons9_dist_sq (0,e8Map x) (0,e8Map y)
  simp only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] at h
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h

theorem equalAreaE8_distance_controls_coordinates (x y : Fin 8 → ℝ) :
    ‖x-y‖ ≤ (1+‖e8InverseMap‖)*
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  have h : ‖x-y‖ ≤ ‖e8InverseMap‖*‖e8Map (x-y)‖ := by
    conv_lhs => rw [←e8InverseMap_e8Map (x-y)]
    exact e8InverseMap.le_opNorm _
  calc
    _ ≤ (1+‖e8InverseMap‖)*‖e8Map (x-y)‖ := h.trans (by gcongr; linarith)
    _ ≤ (1+‖e8InverseMap‖)*‖(WithLp.toLp 2 (e8Map (x-y)) : EuclideanSpace ℝ (Fin 8))‖ := by
      gcongr
      exact pi_norm_le_euclidean _
    _ = _ := by rw [map_sub,WithLp.toLp_sub,dist_eq_norm]

theorem equalAreaNormalizedE8Chart_relative_distance_of_derivative (ε : ℝ) (hε : 0 < ε)
    (hs : ε*equalAreaScaleRadius ≤ 1/8) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Chart ε) z-equalAreaFlatDerivative8‖ ≤ C)
    (x y : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) (hy : y ∈ UnitCube 8) :
    |dist (equalAreaNormalizedE8Chart ε x) (equalAreaNormalizedE8Chart ε y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
      (C*(1+‖e8InverseMap‖))*
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  rw [←equalAreaFlatDerivative8_dist,dist_eq_norm,dist_eq_norm]
  have he : (equalAreaNormalizedE8Chart ε x-equalAreaNormalizedE8Chart ε y)-
      (equalAreaFlatDerivative8 x-equalAreaFlatDerivative8 y) =
      (equalAreaNormalizedE8Chart ε x-equalAreaFlatDerivative8 x)-
        (equalAreaNormalizedE8Chart ε y-equalAreaFlatDerivative8 y) := by abel
  calc
    _ ≤ ‖(equalAreaNormalizedE8Chart ε x-equalAreaNormalizedE8Chart ε y)-
        (equalAreaFlatDerivative8 x-equalAreaFlatDerivative8 y)‖ := abs_norm_sub_norm_le _ _
    _ ≤ C*‖x-y‖ := by
      rw [he]
      exact equalAreaNormalizedE8Chart_increment_error ε hε hs C hb y x hy hx
    _ ≤ C*((1+‖e8InverseMap‖)*
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))) :=
      mul_le_mul_of_nonneg_left (equalAreaE8_distance_controls_coordinates x y) hC
    _ = _ := by rw [←equalAreaFlatDerivative8_dist,dist_eq_norm]; ring

theorem equalAreaNormalizedE8Chart_relative_distance_eventually (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
      |dist (equalAreaNormalizedE8Chart ε x) (equalAreaNormalizedE8Chart ε y)-
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
      η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  have hd : 0 < 1+‖e8InverseMap‖ := by positivity
  let C : ℝ := η/(1+‖e8InverseMap‖)
  have hfirst := (Metric.tendstoUniformlyOn_iff.mp equalAreaNormalizedE8Chart_first_uniform_limit)
    C (by dsimp [C]; positivity)
  have ht : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hfirst] with ε hε hs hb x hx y hy
  have h := equalAreaNormalizedE8Chart_relative_distance_of_derivative ε hε hs.le C
    (by dsimp [C]; positivity) (fun z hz => by
      simpa only [dist_eq_norm,norm_sub_rev] using (hb z hz).le) x y hx hy
  simpa only [C,div_mul_cancel₀ _ hd.ne'] using h

end SphericalRiesz
