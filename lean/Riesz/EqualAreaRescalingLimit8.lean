import Riesz.EqualAreaRescaling8

/-! Actual first and higher derivative limits of the exact-area chart.
Higher derivatives vanish by the exact scaling coefficient; the first
derivative converges by continuity of the actual fderiv at the origin. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaFlatDerivative8 : (Fin 8 → ℝ) →L[ℝ] Ambient9 :=
  (equalAreaPhiDerivative 0).comp e8Map

theorem equalAreaPhiDerivative_zero_apply (v : Fin 8 → ℝ) :
    equalAreaPhiDerivative 0 v = ambientCons9 (0,v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [equalAreaPhiDerivative,equalAreaHeightGradient,equalAreaNormGradient,
      equalAreaHeight,equalAreaSquaredNorm,ambientCons9_apply]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [equalAreaPhiDerivative,equalAreaHeightGradient,equalAreaNormGradient,
        equalAreaHeight,equalAreaSquaredNorm,ambientCons9_apply]
    · simp [equalAreaPhiDerivative,ambientCons9_apply]

theorem equalAreaFlatDerivative8_apply (x : Fin 8 → ℝ) :
    equalAreaFlatDerivative8 x = ambientCons9 (0,e8Map x) :=
  equalAreaPhiDerivative_zero_apply _

theorem equalAreaNormalizedE8Chart_hasFDerivAt (ε : ℝ) (hε : ε ≠ 0)
    (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (ε • e8Map x) < 1) :
    HasFDerivAt (equalAreaNormalizedE8Chart ε)
      ((equalAreaPhiDerivative (ε • e8Map x)).comp e8Map) x := by
  have hf := (equalAreaPhi_hasFDerivAt _ hx).comp x
    (ε • e8Map).hasFDerivAt
  have hg := (hf.sub_const (equalAreaPhi 0)).const_smul ε⁻¹
  apply hg.congr_fderiv
  ext v
  simp [ContinuousLinearMap.comp_apply,smul_smul,hε]

theorem equalAreaNormalizedE8Chart_fderiv (ε : ℝ) (hε : ε ≠ 0)
    (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (ε • e8Map x) < 1) :
    fderiv ℝ (equalAreaNormalizedE8Chart ε) x =
      (fderiv ℝ equalAreaPhi (ε • e8Map x)).comp e8Map := by
  rw [equalAreaPhi_fderiv _ hx]
  exact (equalAreaNormalizedE8Chart_hasFDerivAt ε hε x hx).fderiv

theorem equalAreaPhi_fderiv_comp_continuousAt_zero :
    ContinuousAt (fun p : Fin 8 → ℝ => (fderiv ℝ equalAreaPhi p).comp e8Map) 0 := by
  have hf := (equalAreaPhi_contDiffAt 0 (by simp [equalAreaSquaredNorm])).continuousAt_fderiv
    (by simp : (∞:ℕ∞ω) ≠ 0)
  fun_prop

theorem equalAreaNormalizedE8Chart_first_uniform_limit :
    TendstoUniformlyOn (fun ε x => fderiv ℝ (equalAreaNormalizedE8Chart ε) x)
      (fun _ => equalAreaFlatDerivative8) (𝓝[>] (0:ℝ)) (UnitCube 8) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp
    equalAreaPhi_fderiv_comp_continuousAt_zero η hη
  have ht : Tendsto (fun ε : ℝ => |ε| * equalAreaScaleRadius) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => |ε| * equalAreaScaleRadius) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const equalAreaScaleRadius
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    ht.eventually (gt_mem_nhds (show (0:ℝ) < min δ (1/8) by positivity))] with ε hε hs x hx
  have hn := (equalAreaScaledE8_cube_norm ε x hx).trans_lt hs
  have hdom := equalArea_small_norm_domain (ε • e8Map x) (le_of_lt (hn.trans_le (min_le_right _ _)))
  rw [equalAreaNormalizedE8Chart_fderiv ε (ne_of_gt hε) x hdom]
  have he : (fderiv ℝ equalAreaPhi (0 : Fin 8 → ℝ)).comp e8Map = equalAreaFlatDerivative8 := by
    rw [equalAreaPhi_fderiv _ (by simp [equalAreaSquaredNorm])]
    rfl
  rw [←he,dist_comm]
  exact hb (by simpa only [dist_zero_right] using hn.trans_le (min_le_left _ _))

theorem equalAreaNormalizedE8Chart_high_uniform_limit (k : ℕ) (hk : 2 ≤ k) :
    TendstoUniformlyOn (fun ε x => iteratedFDeriv ℝ k (equalAreaNormalizedE8Chart ε) x)
      (fun _ => 0) (𝓝[>] (0:ℝ)) (UnitCube 8) := by
  obtain ⟨C,hC,hb⟩ := equalAreaNormalizedE8Chart_high_derivatives k hk
  have ht : Tendsto (fun ε : ℝ => C*ε^(k-1)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : k-1 ≠ 0 := by omega
    have hc : Continuous (fun ε : ℝ => C*ε^(k-1)) := by fun_prop
    simpa [h0] using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius
    exact h.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [self_mem_nhdsWithin,hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    ht.eventually (gt_mem_nhds hη)] with ε hε hsmall hbound x hx
  rw [dist_zero_left]
  exact (hb ε hε hsmall.le x hx).trans_lt hbound

end SphericalRiesz
