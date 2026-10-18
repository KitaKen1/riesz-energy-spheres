import Riesz.EqualAreaRescaling24

/-! Actual first and higher derivative limits of the exact-area chart.
Higher derivatives vanish by the exact scaling coefficient; the first
derivative converges by continuity of the actual fderiv at the origin. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaFlatDerivative24 : (Fin 24 → ℝ) →L[ℝ] (AmbientD 24) :=
  (equalAreaPhiDerivativeD 0).comp leechMap

theorem equalAreaPhiDerivative24_zero_apply (v : Fin 24 → ℝ) :
    equalAreaPhiDerivativeD 0 v = (ambientConsD 23) (0,v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [equalAreaPhiDerivativeD,equalAreaHeightGradientD,equalAreaNormGradientD,
      equalAreaHeightD,equalAreaSquaredNormD,ambientConsD_apply]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [equalAreaPhiDerivativeD,equalAreaHeightGradientD,equalAreaNormGradientD,
        equalAreaHeightD,equalAreaSquaredNormD,ambientConsD_apply]
    · simp [equalAreaPhiDerivativeD,ambientConsD_apply]

theorem equalAreaFlatDerivative24_apply (x : Fin 24 → ℝ) :
    equalAreaFlatDerivative24 x = (ambientConsD 23) (0,leechMap x) :=
  equalAreaPhiDerivative24_zero_apply _

theorem equalAreaNormalizedLeechChart_hasFDerivAt (ε : ℝ) (hε : ε ≠ 0)
    (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (ε • leechMap x) < 1) :
    HasFDerivAt (equalAreaNormalizedLeechChart ε)
      ((equalAreaPhiDerivativeD (ε • leechMap x)).comp leechMap) x := by
  have hf := (equalAreaPhiD_hasFDerivAt _ hx).comp x
    (ε • leechMap).hasFDerivAt
  have hg := (hf.sub_const (equalAreaPhiD 0)).const_smul ε⁻¹
  apply hg.congr_fderiv
  ext v
  simp [ContinuousLinearMap.comp_apply,smul_smul,hε]

theorem equalAreaNormalizedLeechChart_fderiv (ε : ℝ) (hε : ε ≠ 0)
    (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (ε • leechMap x) < 1) :
    fderiv ℝ (equalAreaNormalizedLeechChart ε) x =
      (fderiv ℝ equalAreaPhiD (ε • leechMap x)).comp leechMap := by
  rw [equalAreaPhiD_fderiv _ hx]
  exact (equalAreaNormalizedLeechChart_hasFDerivAt ε hε x hx).fderiv

theorem equalAreaPhi24_fderiv_comp_continuousAt_zero :
    ContinuousAt (fun p : Fin 24 → ℝ => (fderiv ℝ equalAreaPhiD p).comp leechMap) 0 := by
  have hf := (equalAreaPhi24_contDiffAt 0 (by simp [equalAreaSquaredNormD])).continuousAt_fderiv
    (by simp : (∞:ℕ∞ω) ≠ 0)
  fun_prop

theorem equalAreaNormalizedLeechChart_first_uniform_limit :
    TendstoUniformlyOn (fun ε x => fderiv ℝ (equalAreaNormalizedLeechChart ε) x)
      (fun _ => equalAreaFlatDerivative24) (𝓝[>] (0:ℝ)) (UnitCube 24) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp
    equalAreaPhi24_fderiv_comp_continuousAt_zero η hη
  have ht : Tendsto (fun ε : ℝ => |ε| * equalAreaScaleRadius24) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => |ε| * equalAreaScaleRadius24) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const equalAreaScaleRadius24
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    ht.eventually (gt_mem_nhds (show (0:ℝ) < min δ (1/8) by positivity))] with ε hε hs x hx
  have hn := (equalAreaScaledLeech_cube_norm ε x hx).trans_lt hs
  have hdom := equalArea24_small_norm_domain (ε • leechMap x) (le_of_lt (hn.trans_le (min_le_right _ _)))
  rw [equalAreaNormalizedLeechChart_fderiv ε (ne_of_gt hε) x hdom]
  have he : (fderiv ℝ equalAreaPhiD (0 : Fin 24 → ℝ)).comp leechMap = equalAreaFlatDerivative24 := by
    rw [equalAreaPhiD_fderiv _ (by simp [equalAreaSquaredNormD])]
    rfl
  rw [←he,dist_comm]
  exact hb (by simpa only [dist_zero_right] using hn.trans_le (min_le_left _ _))

theorem equalAreaNormalizedLeechChart_high_uniform_limit (k : ℕ) (hk : 2 ≤ k) :
    TendstoUniformlyOn (fun ε x => iteratedFDeriv ℝ k (equalAreaNormalizedLeechChart ε) x)
      (fun _ => 0) (𝓝[>] (0:ℝ)) (UnitCube 24) := by
  obtain ⟨C,hC,hb⟩ := equalAreaNormalizedLeechChart_high_derivatives k hk
  have ht : Tendsto (fun ε : ℝ => C*ε^(k-1)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : k-1 ≠ 0 := by omega
    have hc : Continuous (fun ε : ℝ => C*ε^(k-1)) := by fun_prop
    simpa [h0] using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius24) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius24) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius24
    exact h.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [self_mem_nhdsWithin,hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    ht.eventually (gt_mem_nhds hη)] with ε hε hsmall hbound x hx
  rw [dist_zero_left]
  exact (hb ε hε hsmall.le x hx).trans_lt hbound

end SphericalRiesz
