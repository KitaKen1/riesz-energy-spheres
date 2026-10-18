import Riesz.EqualAreaRescalingLimit24

/-! The actual rescaled exact-area chart approaches the flat E8 map
also in order zero.  The mean value theorem transfers first derivative
control to two-point increments, including the boundary of the cube. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem unitCube24_convex : Convex ℝ (UnitCube 24) := by
  rw [unitCube_eq_pi]
  exact convex_pi (fun _ _ => convex_Icc (0:ℝ) 1)

theorem equalAreaNormalizedLeechChart_zero (ε : ℝ) :
    equalAreaNormalizedLeechChart ε 0 = 0 := by
  simp [equalAreaNormalizedLeechChart,equalAreaLeechChart]

theorem equalAreaNormalizedLeechChart_increment_error (ε : ℝ) (hε : 0 < ε)
    (hs : ε*equalAreaScaleRadius24 ≤ 1/8) (C : ℝ)
    (hb : ∀ x ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechChart ε) x-equalAreaFlatDerivative24‖ ≤ C)
    (x y : Fin 24 → ℝ) (hx : x ∈ UnitCube 24) (hy : y ∈ UnitCube 24) :
    ‖(equalAreaNormalizedLeechChart ε y-equalAreaFlatDerivative24 y)-
      (equalAreaNormalizedLeechChart ε x-equalAreaFlatDerivative24 x)‖ ≤ C*‖y-x‖ := by
  apply unitCube24_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ (equalAreaNormalizedLeechChart ε) z-equalAreaFlatDerivative24) _ hb hx hy
  intro z hz
  have hn : ‖ε • leechMap z‖ ≤ 1/8 := (equalAreaScaledLeech_cube_norm ε z hz).trans
    (by simpa only [abs_of_pos hε] using hs)
  have hg := equalAreaNormalizedLeechChart_hasFDerivAt ε hε.ne' z (equalArea24_small_norm_domain _ hn)
  rw [hg.fderiv]
  exact (hg.sub equalAreaFlatDerivative24.hasFDerivAt).hasFDerivWithinAt

theorem equalAreaNormalizedLeechChart_uniform_limit :
    TendstoUniformlyOn equalAreaNormalizedLeechChart (fun x => (ambientConsD 23) (0,leechMap x))
      (𝓝[>] (0:ℝ)) (UnitCube 24) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hfirst := (Metric.tendstoUniformlyOn_iff.mp equalAreaNormalizedLeechChart_first_uniform_limit)
    (η/2) (by positivity)
  have ht : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius24) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius24) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius24
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hfirst] with ε hε hs hb x hx
  have hC : ∀ z ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechChart ε) z-equalAreaFlatDerivative24‖ ≤ η/2 := by
    intro z hz
    simpa only [dist_eq_norm, norm_sub_rev] using (hb z hz).le
  have h := equalAreaNormalizedLeechChart_increment_error ε hε hs.le (η/2) hC 0 x
    (fun _ => by constructor <;> norm_num) hx
  simp only [equalAreaNormalizedLeechChart_zero,map_zero,sub_zero] at h
  have hn := unitCube_norm_le_one 24 x hx
  rw [←equalAreaFlatDerivative24_apply,dist_eq_norm,norm_sub_rev]
  -- Use a smaller derivative tolerance to retain a strict final bound.
  exact (h.trans (mul_le_of_le_one_right (by positivity) hn)).trans_lt (by linarith)

theorem equalAreaFlatDerivative24_dist (x y : Fin 24 → ℝ) :
    dist (equalAreaFlatDerivative24 x) (equalAreaFlatDerivative24 y) =
      dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  rw [equalAreaFlatDerivative24_apply,equalAreaFlatDerivative24_apply]
  have h := ambientConsD_dist_sq (0,leechMap x) (0,leechMap y)
  simp only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] at h
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h

theorem equalAreaLeech_distance_controls_coordinates (x y : Fin 24 → ℝ) :
    ‖x-y‖ ≤ (1+‖leechInverseMap‖)*
      dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  have h : ‖x-y‖ ≤ ‖leechInverseMap‖*‖leechMap (x-y)‖ := by
    conv_lhs => rw [←leechInverseMap_leechMap (x-y)]
    exact leechInverseMap.le_opNorm _
  calc
    _ ≤ (1+‖leechInverseMap‖)*‖leechMap (x-y)‖ := h.trans (by gcongr; linarith)
    _ ≤ (1+‖leechInverseMap‖)*‖(WithLp.toLp 2 (leechMap (x-y)) : EuclideanSpace ℝ (Fin 24))‖ := by
      gcongr
      exact pi_norm_le_euclideanD _
    _ = _ := by rw [map_sub,WithLp.toLp_sub,dist_eq_norm]

theorem equalAreaNormalizedLeechChart_relative_distance_of_derivative (ε : ℝ) (hε : 0 < ε)
    (hs : ε*equalAreaScaleRadius24 ≤ 1/8) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z ∈ UnitCube 24,
      ‖fderiv ℝ (equalAreaNormalizedLeechChart ε) z-equalAreaFlatDerivative24‖ ≤ C)
    (x y : Fin 24 → ℝ) (hx : x ∈ UnitCube 24) (hy : y ∈ UnitCube 24) :
    |dist (equalAreaNormalizedLeechChart ε x) (equalAreaNormalizedLeechChart ε y)-
      dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y))| ≤
      (C*(1+‖leechInverseMap‖))*
        dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  rw [←equalAreaFlatDerivative24_dist,dist_eq_norm,dist_eq_norm]
  have he : (equalAreaNormalizedLeechChart ε x-equalAreaNormalizedLeechChart ε y)-
      (equalAreaFlatDerivative24 x-equalAreaFlatDerivative24 y) =
      (equalAreaNormalizedLeechChart ε x-equalAreaFlatDerivative24 x)-
        (equalAreaNormalizedLeechChart ε y-equalAreaFlatDerivative24 y) := by abel
  calc
    _ ≤ ‖(equalAreaNormalizedLeechChart ε x-equalAreaNormalizedLeechChart ε y)-
        (equalAreaFlatDerivative24 x-equalAreaFlatDerivative24 y)‖ := abs_norm_sub_norm_le _ _
    _ ≤ C*‖x-y‖ := by
      rw [he]
      exact equalAreaNormalizedLeechChart_increment_error ε hε hs C hb y x hy hx
    _ ≤ C*((1+‖leechInverseMap‖)*
        dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y))) :=
      mul_le_mul_of_nonneg_left (equalAreaLeech_distance_controls_coordinates x y) hC
    _ = _ := by rw [←equalAreaFlatDerivative24_dist,dist_eq_norm]; ring

theorem equalAreaNormalizedLeechChart_relative_distance_eventually (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
      |dist (equalAreaNormalizedLeechChart ε x) (equalAreaNormalizedLeechChart ε y)-
        dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y))| ≤
      η*dist (WithLp.toLp 2 (leechMap x) : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 (leechMap y)) := by
  have hd : 0 < 1+‖leechInverseMap‖ := by positivity
  let C : ℝ := η/(1+‖leechInverseMap‖)
  have hfirst := (Metric.tendstoUniformlyOn_iff.mp equalAreaNormalizedLeechChart_first_uniform_limit)
    C (by dsimp [C]; positivity)
  have ht : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius24) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius24) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius24
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hfirst] with ε hε hs hb x hx y hy
  have h := equalAreaNormalizedLeechChart_relative_distance_of_derivative ε hε hs.le C
    (by dsimp [C]; positivity) (fun z hz => by
      simpa only [dist_eq_norm,norm_sub_rev] using (hb z hz).le) x y hx hy
  simpa only [C,div_mul_cancel₀ _ hd.ne'] using h

end SphericalRiesz
