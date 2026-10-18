import Riesz.EqualAreaMeasureD
import Riesz.PatchSupportD
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

def equalAreaLeechChart (ε : ℝ) (x : Fin 24 → ℝ) : (AmbientD 24) :=
  equalAreaPhiD (ε • leechMap x)

def equalAreaNormalizedLeechChart (ε : ℝ) (x : Fin 24 → ℝ) : (AmbientD 24) :=
  ε⁻¹ • (equalAreaLeechChart ε x-equalAreaPhiD 0)

def equalAreaScaleRadius24 : ℝ := 1+‖leechMap‖

theorem equalAreaScaleRadius24_pos : 0 < equalAreaScaleRadius24 := by
  unfold equalAreaScaleRadius24
  positivity

theorem equalAreaSquaredNorm24_le_pi_norm (p : Fin 24 → ℝ) :
    equalAreaSquaredNormD p ≤ 23*‖p‖^2 := by
  calc
    _ ≤ ∑ _j : Fin 23, ‖p‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := norm_le_pi_norm p j.succ
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by simp

theorem equalArea24_small_norm_domain (p : Fin 24 → ℝ) (hp : ‖p‖ ≤ 1/8) :
    equalAreaSquaredNormD p < 1 := by
  have h := equalAreaSquaredNorm24_le_pi_norm p
  have hn := norm_nonneg p
  nlinarith

theorem equalAreaPhi24_contDiffAt (p : Fin 24 → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    ContDiffAt ℝ ∞ equalAreaPhiD p := by
  have hq : Continuous (equalAreaSquaredNormD (n := 23)) := by unfold equalAreaSquaredNormD; fun_prop
  exact (equalAreaPhiD_contDiffOn p hp).contDiffAt ((isOpen_lt hq continuous_const).mem_nhds hp)

theorem equalAreaPhi24_iterated_derivatives_bounded (k : ℕ) :
    ∃ C ≥ 0, ∀ p : Fin 24 → ℝ, ‖p‖ ≤ 1/8 → ‖iteratedFDeriv ℝ k equalAreaPhiD p‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k equalAreaPhiD)
      (Metric.closedBall (0 : Fin 24 → ℝ) (1/8)) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply (equalAreaPhi24_contDiffAt p (equalArea24_small_norm_domain p
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp))).continuousAt_iteratedFDeriv
    simp
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Fin 24 → ℝ) (1/8)).exists_bound_of_continuousOn hc
  exact ⟨max C 0,le_max_right _ _,fun p hp => (hC p
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)).trans (le_max_left _ _)⟩

/-- Local form of the linear-composition chain rule, for the actual
iterated derivative rather than a derivative supplied as an input. -/
theorem equalAreaPhi24_iterated_comp_linear (L : (Fin 24 → ℝ) →L[ℝ] (Fin 24 → ℝ))
    (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (L x) < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (equalAreaPhiD ∘ L) x =
      (iteratedFDeriv ℝ k equalAreaPhiD (L x)).compContinuousLinearMap (fun _ => L) := by
  have hq : Continuous (equalAreaSquaredNormD (n := 23)) := by unfold equalAreaSquaredNormD; fun_prop
  have hu : IsOpen {p | equalAreaSquaredNormD p < 1} := isOpen_lt hq continuous_const
  have hp := hu.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right equalAreaPhiD_contDiffOn
    hu.uniqueDiffOn hp.uniqueDiffOn hx (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hu hx] at h
  exact h

theorem equalAreaLeechChart_contDiffAt (ε : ℝ) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (ε • leechMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaLeechChart ε) x :=
  (equalAreaPhi24_contDiffAt _ hx).comp x (by fun_prop)

theorem equalAreaNormalizedLeechChart_contDiffAt (ε : ℝ) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (ε • leechMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaNormalizedLeechChart ε) x :=
  ((equalAreaLeechChart_contDiffAt ε x hx).sub contDiffAt_const).const_smul ε⁻¹

theorem equalAreaNormalizedLeechChart_iteratedFDeriv (ε : ℝ) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (ε • leechMap x) < 1) (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (equalAreaNormalizedLeechChart ε) x =
      ε⁻¹ • (iteratedFDeriv ℝ k equalAreaPhiD (ε • leechMap x)).compContinuousLinearMap
        (fun _ => ε • leechMap) := by
  have hf := (equalAreaLeechChart_contDiffAt ε x hx).of_le (by simp : (k:ℕ∞ω) ≤ ∞)
  have hsub := hf.sub (contDiffAt_const (c := equalAreaPhiD 0))
  change iteratedFDeriv ℝ k (fun y => ε⁻¹ • (equalAreaLeechChart ε y-equalAreaPhiD 0)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  change ε⁻¹ • iteratedFDeriv ℝ k (equalAreaLeechChart ε-(fun _ => equalAreaPhiD 0)) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero]
  exact congrArg (fun D => ε⁻¹ • D) (equalAreaPhi24_iterated_comp_linear (ε • leechMap) x hx k)

theorem equalAreaNormalizedLeechChart_derivative_bound (ε : ℝ) (hε : 0 < ε)
    (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (ε • leechMap x) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (equalAreaNormalizedLeechChart ε) x‖ ≤
      ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (ε • leechMap x)‖*‖leechMap‖^k := by
  rw [equalAreaNormalizedLeechChart_iteratedFDeriv ε x hx k (by omega),norm_smul]
  calc
    _ ≤ ‖ε⁻¹‖*(‖iteratedFDeriv ℝ k equalAreaPhiD (ε • leechMap x)‖*
        ∏ _i : Fin k, ‖ε • leechMap‖) := by
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
        _ = (ε⁻¹*ε^k)*‖iteratedFDeriv ℝ k equalAreaPhiD (ε • leechMap x)‖*‖leechMap‖^k := by ring
        _ = _ := by rw [he]

theorem equalAreaScaledLeech_cube_norm (ε : ℝ) (x : Fin 24 → ℝ) (hx : x ∈ UnitCube 24) :
    ‖ε • leechMap x‖ ≤ |ε| * equalAreaScaleRadius24 := by
  rw [norm_smul,Real.norm_eq_abs]
  have hn : ‖x‖ ≤ (1:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ |ε| * (‖leechMap‖*‖x‖) := mul_le_mul_of_nonneg_left (leechMap.le_opNorm x) (abs_nonneg ε)
    _ ≤ |ε| * (‖leechMap‖*1) := by gcongr
    _ ≤ _ := by unfold equalAreaScaleRadius24; nlinarith [norm_nonneg leechMap,abs_nonneg ε]

theorem equalAreaNormalizedLeechChart_high_derivatives (k : ℕ) (hk : 2 ≤ k) :
    ∃ C ≥ 0, ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius24 ≤ 1/8 →
      ∀ x ∈ UnitCube 24, ‖iteratedFDeriv ℝ k (equalAreaNormalizedLeechChart ε) x‖ ≤ C*ε^(k-1) := by
  obtain ⟨C,hC,hb⟩ := equalAreaPhi24_iterated_derivatives_bounded k
  refine ⟨C*‖leechMap‖^k,by positivity,?_⟩
  intro ε hε hs x hx
  have hn : ‖ε • leechMap x‖ ≤ 1/8 := (equalAreaScaledLeech_cube_norm ε x hx).trans
    (by simpa only [abs_of_pos hε] using hs)
  calc
    _ ≤ ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (ε • leechMap x)‖*‖leechMap‖^k :=
      equalAreaNormalizedLeechChart_derivative_bound ε hε x (equalArea24_small_norm_domain _ hn) k (by omega)
    _ ≤ ε^(k-1)*C*‖leechMap‖^k := by gcongr; exact hb _ hn
    _ = _ := by ring

end SphericalRiesz
