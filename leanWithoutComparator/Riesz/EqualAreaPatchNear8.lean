import Riesz.EqualAreaPatchClass8
import Riesz.EqualAreaNearBackground8

/-! Near-background transfer for moving sphere patches. Rotations and
cube centers may vary arbitrarily with m; the coordinate center and
positive patch scale tend to zero. All original corrected nodes remain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem equalAreaNormalizedE8Patch_continuous (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) : Continuous (equalAreaNormalizedE8Patch g v c ε) := by
  unfold equalAreaNormalizedE8Patch equalAreaMovingNormalizedE8Chart equalAreaMovingE8Chart
  exact g.continuous.comp (((equalAreaPhi_continuous.comp (by fun_prop)).sub continuous_const).const_smul ε⁻¹)

theorem equalAreaNormalizedE8Patch_relative_distance_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
      |dist (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m) x)
          (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m) y)-
        dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
        η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)) := by
  obtain ⟨ρ,hρ,_hρ1,hb⟩ := equalAreaNormalizedE8Patch_relative_distance_uniform η hη
  have hnv : Tendsto (fun m => ‖v m‖) atTop (𝓝 0) := by simpa using hv.norm
  have hne : Tendsto (fun m => e m*equalAreaScaleRadius) atTop (𝓝 0) := by
    simpa using he.mul_const equalAreaScaleRadius
  filter_upwards [hnv.eventually (gt_mem_nhds hρ),hne.eventually (gt_mem_nhds hρ),hp,hc]
    with m hvm hem hpm hcm
  exact hb (v m) hvm.le (e m) hpm hem.le (g m) (c m) hcm

def equalAreaPatchNearBackgroundDifference (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε R : ℝ) (m : ℕ) : ℝ :=
  (m:ℝ)^4*((cubeQuadrature 8 m (curvedNearPotential (equalAreaNormalizedE8Patch g v c ε) (R/(m:ℝ)))-
      ∫ x in UnitCube 8, curvedNearPotential (equalAreaNormalizedE8Patch g v c ε) (R/(m:ℝ)) x)-
    (cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
      ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))

/-- A bound for fixed small patches, uniform in m as well as all patch
parameters. This also supports the order m→∞ followed by patch size→0. -/
theorem equalAreaPatchNearBackgroundDifference_uniform (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1/2) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ R : ℝ, 0 < R → ∀ m : ℕ, 8 ≤ m →
      |equalAreaPatchNearBackgroundDifference g v c ε R m| ≤
        128*η*e8NearIntegralConstant*R^4 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedE8Patch_relative_distance_uniform η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc R hR m hm
  exact curvedNearPotential_scaled_background_error (equalAreaNormalizedE8Patch g v c ε)
    (equalAreaNormalizedE8Patch_continuous _ _ _ _).measurable R hR η hη.le hη1
    (hb v hv ε hε hs g c hc) m hm

theorem equalAreaPatchNearBackgroundDifference_bound_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1/2) :
    ∀ᶠ m : ℕ in atTop, ∀ R : ℝ, 0 < R → 8 ≤ m →
      |equalAreaPatchNearBackgroundDifference (g m) (v m) (c m) (e m) R m| ≤
        128*η*e8NearIntegralConstant*R^4 := by
  filter_upwards [equalAreaNormalizedE8Patch_relative_distance_along g v c e hv he hp hc η hη]
    with m hdist R hR hm
  exact curvedNearPotential_scaled_background_error
    (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m))
    (equalAreaNormalizedE8Patch_continuous _ _ _ _).measurable R hR η hη.le hη1 hdist m hm

theorem equalAreaPatchNearBackgroundDifference_limit_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => equalAreaPatchNearBackgroundDifference (g m) (v m) (c m) (e m) R m)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let K : ℝ := 128*e8NearIntegralConstant*R^4
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (by norm_num) e8NearIntegralConstant_nonneg) (pow_nonneg hR.le 4)
  let η : ℝ := min (1/2) (δ/(2*(K+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hbound := equalAreaPatchNearBackgroundDifference_bound_along g v c e hv he hp hc
    η hη (min_le_left _ _)
  filter_upwards [hbound,eventually_ge_atTop (8:ℕ)] with m hb hm
  have h := hb R hR hm
  rw [dist_zero_right]
  calc
    _ ≤ η*K := by simpa [K,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using h
    _ ≤ (δ/(2*(K+1)))*K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK
    _ < δ := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < 2*(K+1))).mpr
      nlinarith

def equalAreaPatchNearBackground (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε R : ℝ) (m : ℕ) : ℝ :=
  (m:ℝ)^4*(cubeQuadrature 8 m (curvedNearPotential (equalAreaNormalizedE8Patch g v c ε) (R/(m:ℝ)))-
    ∫ x in UnitCube 8, curvedNearPotential (equalAreaNormalizedE8Patch g v c ε) (R/(m:ℝ)) x)

theorem equalAreaPatchNearBackground_limit_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => equalAreaPatchNearBackground (g m) (v m) (c m) (e m) R m)
      atTop (𝓝 0) := by
  have hflat : Tendsto (fun m : ℕ => (m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
      ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x)) atTop (𝓝 0) := by
    simpa only [e8ScaledNearBackground_eq] using e8ScaledNearPotential_background_limit R hR
  have h := (equalAreaPatchNearBackgroundDifference_limit_along g v c e hv he hp hc R hR).add hflat
  convert h using 1
  · funext m
    unfold equalAreaPatchNearBackgroundDifference equalAreaPatchNearBackground
    ring
  · simp

end SphericalRiesz
