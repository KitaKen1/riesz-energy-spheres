import Riesz.SphereGridPool8
import Riesz.EqualAreaEuclideanGeometry8
import Riesz.SphereCutoffPartition8
import Riesz.SupportedChartCutoff8

/-! Bi-Lipschitz equal-area charts and the spherical cap bound (stage NEG, stratification).

The equal-area chart `Φ` has an isometric derivative at the centre (`‖DΦ(0) v‖ = ‖v‖`) and is
strictly differentiable there, so `Φ - DΦ(0)` is `1/2`-Lipschitz near `0`; hence
`|u - v| ≤ 2 |Φu - Φv| ≤ 4 |u - v|` near the centre. Consequently a small spherical cap around
any point is the rotated chart image of a small coordinate set: `area(B(x,R)) ≤ (4R)^8` for
`R ≤ R₀` (rotate `x` to the north pole, pull back by the chart, compare with a coordinate cube;
the chart is exactly equal-area). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

theorem equalAreaPhiEuclidean8_near_biLipschitz :
    ∃ ρ > 0, ρ ≤ 1/8 ∧ ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρ,
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρ,
        dist u v ≤ 2*dist (equalAreaPhiEuclidean8 u) (equalAreaPhiEuclidean8 v) ∧
        dist (equalAreaPhiEuclidean8 u) (equalAreaPhiEuclidean8 v) ≤ 2*dist u v := by
  set D := equalAreaEuclideanDerivative8 with hDdef
  have hD := equalAreaPhiEuclidean8_hasStrictFDerivAt_zero
  have hsub : HasStrictFDerivAt (fun u => equalAreaPhiEuclidean8 u-D u) (D-D) 0 :=
    hD.sub D.hasStrictFDerivAt
  rw [sub_self] at hsub
  have hk : ‖(0 : EuclideanSpace ℝ (Fin 8) →L[ℝ] Ambient9)‖₊ < Real.toNNReal (1/2) := by
    simp
  obtain ⟨s, hs, hLip⟩ := hsub.exists_lipschitzOnWith_of_nnnorm_lt (Real.toNNReal (1/2)) hk
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min δ (1/8), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro u hu v hv
  have hu' := hball (ball_subset_ball (min_le_left δ (1/8)) hu)
  have hv' := hball (ball_subset_ball (min_le_left δ (1/8)) hv)
  have h := hLip.dist_le_mul u hu' v hv'
  rw [Real.coe_toNNReal _ (by norm_num)] at h
  set E := (equalAreaPhiEuclidean8 u-D u)-(equalAreaPhiEuclidean8 v-D v) with hEdef
  have hE : ‖E‖ ≤ 1/2*‖u-v‖ := by
    rw [hEdef, ← dist_eq_norm, ← dist_eq_norm]
    exact h
  have hDn : ‖D (u-v)‖ = ‖u-v‖ := equalAreaEuclideanDerivative8_norm (u-v)
  have hdecomp : equalAreaPhiEuclidean8 u-equalAreaPhiEuclidean8 v = D (u-v)+E := by
    rw [hEdef, map_sub]
    abel
  rw [dist_eq_norm, dist_eq_norm, hdecomp]
  constructor
  · have h4 := norm_sub_le (D (u-v)+E) E
    have h2 : D (u-v)+E-E = D (u-v) := by abel
    rw [h2, hDn] at h4
    linarith
  · have h1 := norm_add_le (D (u-v)) E
    rw [hDn] at h1
    nlinarith [norm_nonneg (u-v)]

theorem equalAreaPhiEuclidean8_zero : equalAreaPhiEuclidean8 0 = (northPole8 : Ambient9) := by
  have h := equalAreaPhiEuclidean8_inverse northPole8 (by simp [northPole8])
  rwa [sphereEqualAreaCoordinates8_northPole] at h

theorem sphere8_coord0_gt_of_dist_northPole (y : Sphere8) (hy : dist y northPole8 < 1/2) :
    1/2 < (y:Ambient9) 0 := by
  have h1 : |((y:Ambient9)-(northPole8:Ambient9)) 0| ≤ ‖(y:Ambient9)-(northPole8:Ambient9)‖ := by
    have := PiLp.norm_apply_le ((y:Ambient9)-(northPole8:Ambient9)) (0 : Fin 9)
    rwa [Real.norm_eq_abs] at this
  have h2 : ((y:Ambient9)-(northPole8:Ambient9)) 0 = (y:Ambient9) 0-1 := by
    simp [northPole8]
  rw [h2] at h1
  have h3 : dist y northPole8 = ‖(y:Ambient9)-(northPole8:Ambient9)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  rw [← h3] at h1
  have := (abs_lt.mp (lt_of_le_of_lt h1 hy)).1
  linarith

/-- The spherical cap bound: `area(B(x,R)) ≤ (4R)^8` for small `R`. -/
theorem sphereArea8_ball_le : ∃ R₀ > 0, ∀ x : Sphere8, ∀ R : ℝ, 0 < R → R ≤ R₀ →
    sphereArea8 {y : Sphere8 | dist y x < R} ≤ ENNReal.ofReal ((4*R)^8) := by
  obtain ⟨ρ, hρ, _hρ8, hbi⟩ := equalAreaPhiEuclidean8_near_biLipschitz
  have hc := sphereEqualAreaCoordinates8_continuousAt northPole8 (by simp [northPole8])
  obtain ⟨R₁, hR₁, hR₁c⟩ := Metric.continuousAt_iff.mp hc ρ hρ
  refine ⟨min R₁ (1/8), lt_min hR₁ (by norm_num), fun x R hR hRR => ?_⟩
  have hR1 : R ≤ R₁ := hRR.trans (min_le_left _ _)
  have hR8 : R ≤ 1/8 := hRR.trans (min_le_right _ _)
  obtain ⟨g, hg⟩ := sphereRotation8_transitive northPole8 x
  have hpre : (sphereRotation8 g) ⁻¹' {y : Sphere8 | dist y x < R} =
      {y : Sphere8 | dist y northPole8 < R} := by
    ext y
    simp only [mem_preimage, mem_setOf_eq, ← hg]
    have : dist (sphereRotation8 g y) (sphereRotation8 g northPole8) = dist y northPole8 := by
      rw [Subtype.dist_eq, Subtype.dist_eq]
      change dist (g (y:Ambient9)) (g (northPole8:Ambient9)) = _
      exact g.dist_map _ _
    rw [this]
  have hm := (sphereArea8_rotation_preserving g).measure_preimage_emb
    (sphereRotation8 g).measurableEmbedding {y : Sphere8 | dist y x < R}
  rw [hpre] at hm
  rw [← hm]
  set cube : Set (Fin 8 → ℝ) := Set.pi univ (fun _ => Icc (-(2*R)) (2*R)) with hcube
  have hcm : MeasurableSet cube := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hcd : cube ⊆ equalAreaChartDomain := by
    intro p hp
    have hpi : ∀ i, |p i| ≤ 2*R := fun i => abs_le.mpr (hp i (mem_univ i))
    refine ⟨?_, ?_⟩
    · unfold equalAreaSquaredNorm
      calc ∑ j : Fin 7, p j.succ^2 ≤ ∑ _j : Fin 7, (2*R)^2 := by
            apply Finset.sum_le_sum
            intro j _
            have := hpi j.succ
            nlinarith [abs_nonneg (p j.succ), sq_abs (p j.succ)]
        _ < 1 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hR2 : R^2 ≤ 1/64 := by nlinarith
            norm_num
            nlinarith
    · have h0 := abs_le.mp (hpi 0)
      have hpi3 := Real.pi_gt_three
      constructor <;> linarith
  have hsub : {y : Sphere8 | dist y northPole8 < R} ⊆ equalAreaSpherePatch cube := by
    intro y hy
    simp only [mem_setOf_eq] at hy
    have hy0 : 0 < (y:Ambient9) 0 :=
      lt_trans (by norm_num) (sphere8_coord0_gt_of_dist_northPole y (lt_of_lt_of_le hy (by linarith)))
    set u := sphereEqualAreaCoordinates8 y with hudef
    have hu : dist u 0 < ρ := by
      rw [← sphereEqualAreaCoordinates8_northPole]
      exact hR₁c (lt_of_lt_of_le hy hR1)
    have hΦu : equalAreaPhiEuclidean8 u = (y:Ambient9) := equalAreaPhiEuclidean8_inverse y hy0
    have hb := (hbi u (mem_ball.mpr hu) 0 (mem_ball_self hρ)).1
    rw [hΦu, equalAreaPhiEuclidean8_zero] at hb
    have hyd : dist (y:Ambient9) (northPole8:Ambient9) = dist y northPole8 := (Subtype.dist_eq _ _).symm
    rw [hyd] at hb
    have hun : ‖u‖ < 2*R := by
      rw [← dist_zero_right]
      linarith
    refine ⟨WithLp.ofLp u, ?_, hΦu⟩
    intro i _
    have := (PiLp.norm_apply_le u i).trans hun.le
    exact abs_le.mp this
  calc sphereArea8 {y : Sphere8 | dist y northPole8 < R}
      ≤ sphereArea8 (equalAreaSpherePatch cube) := measure_mono hsub
    _ = (volume : Measure (Fin 8 → ℝ)) cube := sphereArea8_equalAreaSpherePatch cube hcm hcd
    _ = ENNReal.ofReal ((4*R)^8) := by
        rw [hcube, volume_pi_pi]
        simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by linarith)]
        congr 1
        ring

#print axioms equalAreaPhiEuclidean8_near_biLipschitz
#print axioms equalAreaPhiEuclidean8_zero
#print axioms sphere8_coord0_gt_of_dist_northPole
#print axioms sphereArea8_ball_le

end SphericalRiesz
