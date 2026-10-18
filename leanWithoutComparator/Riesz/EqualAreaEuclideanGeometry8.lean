import Riesz.EqualAreaRescalingLimit8
import Riesz.SupportedChartCutoff8
import Riesz.SphereValue8
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The original equal-area chart with the actual Euclidean norm in its domain.
Its derivative at zero is the isometric inclusion v -> (0,v). Strict
Fréchet differentiability therefore gives an arbitrarily close-to-one
Lipschitz constant on an actual small ball. No Pi/Euclidean norm equality
is assumed. The resulting chord bound applies to the actual supported
Sphere8 cutoff and is the geometric input for Gaussian localization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace SphericalRiesz

def equalAreaPhiEuclidean8 (u : EuclideanSpace ℝ (Fin 8)) : Ambient9 :=
  equalAreaPhi (WithLp.ofLp u)

def equalAreaEuclideanDerivative8 : EuclideanSpace ℝ (Fin 8) →L[ℝ] Ambient9 :=
  (equalAreaPhiDerivative 0).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).toContinuousLinearMap

theorem equalAreaPhiEuclidean8_continuous : Continuous equalAreaPhiEuclidean8 :=
  equalAreaPhi_continuous.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).continuous

theorem equalAreaEuclideanDerivative8_apply (v : EuclideanSpace ℝ (Fin 8)) :
    equalAreaEuclideanDerivative8 v = ambientCons9 (0,WithLp.ofLp v) :=
  equalAreaPhiDerivative_zero_apply _

theorem equalAreaEuclideanDerivative8_norm (v : EuclideanSpace ℝ (Fin 8)) :
    ‖equalAreaEuclideanDerivative8 v‖ = ‖v‖ := by
  have h := ambientCons9_norm_sq (0,WithLp.ofLp v)
  rw [← equalAreaEuclideanDerivative8_apply] at h
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, WithLp.toLp_ofLp] at h
  nlinarith [norm_nonneg (equalAreaEuclideanDerivative8 v), norm_nonneg v]

theorem equalAreaEuclideanDerivative8_opNorm_le : ‖equalAreaEuclideanDerivative8‖ ≤ 1 := by
  apply equalAreaEuclideanDerivative8.opNorm_le_bound zero_le_one
  intro v
  rw [equalAreaEuclideanDerivative8_norm, one_mul]

theorem equalAreaPhiEuclidean8_hasStrictFDerivAt_zero :
    HasStrictFDerivAt equalAreaPhiEuclidean8 equalAreaEuclideanDerivative8 0 := by
  have h0 : equalAreaSquaredNorm (0 : Fin 8 → ℝ) < 1 := by simp [equalAreaSquaredNorm]
  have hs := (equalAreaPhi_contDiffAt 0 h0).hasStrictFDerivAt'
    (equalAreaPhi_hasFDerivAt 0 h0) (by simp : (∞ : ℕ∞ω) ≠ 0)
  have he := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).hasStrictFDerivAt
    (x := (0 : EuclideanSpace ℝ (Fin 8)))
  convert! hs.comp 0 he using 1

theorem equalAreaEuclidean8_small_norm_domain (u : EuclideanSpace ℝ (Fin 8))
    (hu : ‖u‖ ≤ 1/8) : WithLp.ofLp u ∈ equalAreaChartDomain := by
  have hp : ‖WithLp.ofLp u‖ ≤ ‖u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro i
    exact PiLp.norm_apply_le u i
  refine ⟨equalArea_small_norm_domain _ (hp.trans hu),?_⟩
  have hi : |(WithLp.ofLp u) 0| ≤ 1/8 := by
    exact (show |(WithLp.ofLp u) 0| ≤ ‖u‖ from PiLp.norm_apply_le u 0).trans hu
  have hpi := Real.pi_gt_three
  exact ⟨by linarith [(abs_le.mp hi).1],by linarith [(abs_le.mp hi).2]⟩

theorem equalAreaPhiEuclidean8_inverse (x : Sphere8) (hx : 0 < (x : Ambient9) 0) :
    equalAreaPhiEuclidean8 (sphereEqualAreaCoordinates8 x) = (x : Ambient9) := by
  simpa only [equalAreaPhiEuclidean8, sphereEqualAreaCoordinates8, WithLp.ofLp_toLp] using
    equalAreaPhi_inverse8 x hx

theorem equalAreaPhiEuclidean8_near_isometry (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ρ ≤ 1/8 ∧
      ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρ,
        ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρ,
          dist (equalAreaPhiEuclidean8 u) (equalAreaPhiEuclidean8 v) ≤ L*dist u v := by
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL.le
  have hk : ‖equalAreaEuclideanDerivative8‖₊ < Real.toNNReal L := by
    apply NNReal.coe_lt_coe.mp
    simpa only [coe_nnnorm, Real.coe_toNNReal _ hL0] using
      equalAreaEuclideanDerivative8_opNorm_le.trans_lt hL
  obtain ⟨s,hs,hLip⟩ := equalAreaPhiEuclidean8_hasStrictFDerivAt_zero.exists_lipschitzOnWith_of_nnnorm_lt
    (Real.toNNReal L) hk
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min δ (1/8),lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro u hu v hv
  have hu' := hsub (ball_subset_ball (min_le_left δ (1/8)) hu)
  have hv' := hsub (ball_subset_ball (min_le_left δ (1/8)) hv)
  simpa only [Real.coe_toNNReal _ hL0] using hLip.dist_le_mul u hu' v hv'

theorem sphereChartCutoff8_chord_bound (ρ : ℝ) (hρ : 0 < ρ) (L : ℝ)
    (hLip : ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρ,
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρ,
        dist (equalAreaPhiEuclidean8 u) (equalAreaPhiEuclidean8 v) ≤ L*dist u v)
    (x y : Sphere8) (hx : sphereChartCutoff8 ρ hρ x ≠ 0)
    (hy : sphereChartCutoff8 ρ hρ y ≠ 0) :
    dist x y ≤ L*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖ := by
  have hxs := hx
  change x ∈ Function.support (sphereChartCutoff8 ρ hρ) at hxs
  rw [sphereChartCutoff8_support] at hxs
  have hys := hy
  change y ∈ Function.support (sphereChartCutoff8 ρ hρ) at hys
  rw [sphereChartCutoff8_support] at hys
  have h := hLip _ (by simpa only [mem_ball,dist_zero_right] using hxs.2)
    _ (by simpa only [mem_ball,dist_zero_right] using hys.2)
  rw [equalAreaPhiEuclidean8_inverse x hxs.1, equalAreaPhiEuclidean8_inverse y hys.1] at h
  simpa only [Subtype.dist_eq, dist_eq_norm] using h

theorem sphereChartCutoff8_exists_near_isometric_support (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ∃ hρ : 0 < ρ, ρ ≤ 1/8 ∧
      ∀ x y : Sphere8, sphereChartCutoff8 ρ hρ x ≠ 0 → sphereChartCutoff8 ρ hρ y ≠ 0 →
        dist x y ≤ L*‖sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y‖ := by
  obtain ⟨ρ,hρ,hr,hLip⟩ := equalAreaPhiEuclidean8_near_isometry L hL
  exact ⟨ρ,hρ,hρ,hr,fun x y hx hy => sphereChartCutoff8_chord_bound ρ hρ L hLip x y hx hy⟩

end SphericalRiesz
