import Riesz.EqualAreaMeasure8
import Riesz.E8SphereGraph
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual rescaling of the exact-area chart.  Local linear composition
and compact bounds keep the high-order derivative expressions intact;
no seven-fold coordinate expansion is required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaE8Chart (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  equalAreaPhi (ε • e8Map x)

def equalAreaNormalizedE8Chart (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  ε⁻¹ • (equalAreaE8Chart ε x-equalAreaPhi 0)

def equalAreaScaleRadius : ℝ := 1+‖e8Map‖

theorem equalAreaScaleRadius_pos : 0 < equalAreaScaleRadius := by
  unfold equalAreaScaleRadius
  positivity

theorem equalAreaSquaredNorm_le_pi_norm (p : Fin 8 → ℝ) :
    equalAreaSquaredNorm p ≤ 7*‖p‖^2 := by
  calc
    _ ≤ ∑ _j : Fin 7, ‖p‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := norm_le_pi_norm p j.succ
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by simp

theorem equalArea_small_norm_domain (p : Fin 8 → ℝ) (hp : ‖p‖ ≤ 1/8) :
    equalAreaSquaredNorm p < 1 := by
  have h := equalAreaSquaredNorm_le_pi_norm p
  have hn := norm_nonneg p
  nlinarith

theorem equalAreaPhi_contDiffAt (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    ContDiffAt ℝ ∞ equalAreaPhi p := by
  have hq : Continuous equalAreaSquaredNorm := by unfold equalAreaSquaredNorm; fun_prop
  exact (equalAreaPhi_contDiffOn p hp).contDiffAt ((isOpen_lt hq continuous_const).mem_nhds hp)

theorem equalAreaPhi_iterated_derivatives_bounded (k : ℕ) :
    ∃ C ≥ 0, ∀ p : Fin 8 → ℝ, ‖p‖ ≤ 1/8 → ‖iteratedFDeriv ℝ k equalAreaPhi p‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k equalAreaPhi)
      (Metric.closedBall (0 : Fin 8 → ℝ) (1/8)) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply (equalAreaPhi_contDiffAt p (equalArea_small_norm_domain p
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp))).continuousAt_iteratedFDeriv
    simp
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Fin 8 → ℝ) (1/8)).exists_bound_of_continuousOn hc
  exact ⟨max C 0,le_max_right _ _,fun p hp => (hC p
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)).trans (le_max_left _ _)⟩

/-- Local form of the linear-composition chain rule, for the actual
iterated derivative rather than a derivative supplied as an input. -/
theorem equalAreaPhi_iterated_comp_linear (L : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ))
    (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (L x) < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (equalAreaPhi ∘ L) x =
      (iteratedFDeriv ℝ k equalAreaPhi (L x)).compContinuousLinearMap (fun _ => L) := by
  have hq : Continuous equalAreaSquaredNorm := by unfold equalAreaSquaredNorm; fun_prop
  have hu : IsOpen {p | equalAreaSquaredNorm p < 1} := isOpen_lt hq continuous_const
  have hp := hu.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right equalAreaPhi_contDiffOn
    hu.uniqueDiffOn hp.uniqueDiffOn hx (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hu hx] at h
  exact h

theorem equalAreaE8Chart_contDiffAt (ε : ℝ) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (ε • e8Map x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaE8Chart ε) x :=
  (equalAreaPhi_contDiffAt _ hx).comp x (by fun_prop)

theorem equalAreaNormalizedE8Chart_contDiffAt (ε : ℝ) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (ε • e8Map x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaNormalizedE8Chart ε) x :=
  ((equalAreaE8Chart_contDiffAt ε x hx).sub contDiffAt_const).const_smul ε⁻¹

theorem equalAreaNormalizedE8Chart_iteratedFDeriv (ε : ℝ) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (ε • e8Map x) < 1) (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (equalAreaNormalizedE8Chart ε) x =
      ε⁻¹ • (iteratedFDeriv ℝ k equalAreaPhi (ε • e8Map x)).compContinuousLinearMap
        (fun _ => ε • e8Map) := by
  have hf := (equalAreaE8Chart_contDiffAt ε x hx).of_le (by simp : (k:ℕ∞ω) ≤ ∞)
  have hsub := hf.sub (contDiffAt_const (c := equalAreaPhi 0))
  change iteratedFDeriv ℝ k (fun y => ε⁻¹ • (equalAreaE8Chart ε y-equalAreaPhi 0)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  change ε⁻¹ • iteratedFDeriv ℝ k (equalAreaE8Chart ε-(fun _ => equalAreaPhi 0)) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero]
  exact congrArg (fun D => ε⁻¹ • D) (equalAreaPhi_iterated_comp_linear (ε • e8Map) x hx k)

theorem equalAreaNormalizedE8Chart_derivative_bound (ε : ℝ) (hε : 0 < ε)
    (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (ε • e8Map x) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (equalAreaNormalizedE8Chart ε) x‖ ≤
      ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhi (ε • e8Map x)‖*‖e8Map‖^k := by
  rw [equalAreaNormalizedE8Chart_iteratedFDeriv ε x hx k (by omega),norm_smul]
  calc
    _ ≤ ‖ε⁻¹‖*(‖iteratedFDeriv ℝ k equalAreaPhi (ε • e8Map x)‖*
        ∏ _i : Fin k, ‖ε • e8Map‖) := by
      apply mul_le_mul_of_nonneg_left
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hε,mul_pow]
      have he : ε⁻¹*ε^k = ε^(k-1) := by
        have heq : ε^k = ε^(k-1)*ε := by
          conv_lhs => rw [show k = (k-1)+1 by omega,pow_succ]
        rw [heq]
        field_simp
      calc
        _ = (ε⁻¹*ε^k)*‖iteratedFDeriv ℝ k equalAreaPhi (ε • e8Map x)‖*‖e8Map‖^k := by ring
        _ = _ := by rw [he]

theorem equalAreaScaledE8_cube_norm (ε : ℝ) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    ‖ε • e8Map x‖ ≤ |ε| * equalAreaScaleRadius := by
  rw [norm_smul,Real.norm_eq_abs]
  have hn : ‖x‖ ≤ (1:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ |ε| * (‖e8Map‖*‖x‖) := mul_le_mul_of_nonneg_left (e8Map.le_opNorm x) (abs_nonneg ε)
    _ ≤ |ε| * (‖e8Map‖*1) := by gcongr
    _ ≤ _ := by unfold equalAreaScaleRadius; nlinarith [norm_nonneg e8Map,abs_nonneg ε]

theorem equalAreaNormalizedE8Chart_high_derivatives (k : ℕ) (hk : 2 ≤ k) :
    ∃ C ≥ 0, ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ 1/8 →
      ∀ x ∈ UnitCube 8, ‖iteratedFDeriv ℝ k (equalAreaNormalizedE8Chart ε) x‖ ≤ C*ε^(k-1) := by
  obtain ⟨C,hC,hb⟩ := equalAreaPhi_iterated_derivatives_bounded k
  refine ⟨C*‖e8Map‖^k,by positivity,?_⟩
  intro ε hε hs x hx
  have hn : ‖ε • e8Map x‖ ≤ 1/8 := (equalAreaScaledE8_cube_norm ε x hx).trans
    (by simpa only [abs_of_pos hε] using hs)
  calc
    _ ≤ ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhi (ε • e8Map x)‖*‖e8Map‖^k :=
      equalAreaNormalizedE8Chart_derivative_bound ε hε x (equalArea_small_norm_domain _ hn) k (by omega)
    _ ≤ ε^(k-1)*C*‖e8Map‖^k := by gcongr; exact hb _ hn
    _ = _ := by ring

end SphericalRiesz
