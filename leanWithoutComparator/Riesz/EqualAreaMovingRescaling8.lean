import Riesz.EqualAreaRescalingGeometry8

/-! Moving coordinate centers in the actual exact-area chart.  All bounds
use one fixed compact smooth domain, independently of the center. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaMovingE8Chart (v : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ) : Ambient9 :=
  equalAreaPhi (v+ε • e8Map x)

def equalAreaMovingNormalizedE8Chart (v : Fin 8 → ℝ) (ε : ℝ)
    (x : Fin 8 → ℝ) : Ambient9 :=
  ε⁻¹ • (equalAreaMovingE8Chart v ε x-equalAreaPhi v)

theorem equalAreaPhi_iterated_comp_affine (v : Fin 8 → ℝ)
    (L : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+L x) < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => equalAreaPhi (v+L y)) x =
      (iteratedFDeriv ℝ k equalAreaPhi (v+L x)).compContinuousLinearMap (fun _ => L) := by
  have hq : Continuous (fun p => equalAreaSquaredNorm (v+p)) := by
    unfold equalAreaSquaredNorm; fun_prop
  have hu : IsOpen {p | equalAreaSquaredNorm (v+p) < 1} := isOpen_lt hq continuous_const
  have hf : ContDiffOn ℝ ∞ (fun p => equalAreaPhi (v+p))
      {p | equalAreaSquaredNorm (v+p) < 1} := by
    intro p hp
    exact ((equalAreaPhi_contDiffAt _ hp).comp p (by fun_prop)).contDiffWithinAt
  have hp := hu.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hu.uniqueDiffOn hp.uniqueDiffOn hx
    (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hu hx,iteratedFDeriv_comp_add_left] at h
  exact h

theorem equalAreaMovingE8Chart_contDiffAt (v : Fin 8 → ℝ) (ε : ℝ) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+ε • e8Map x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaMovingE8Chart v ε) x :=
  (equalAreaPhi_contDiffAt _ hx).comp x (by fun_prop)

theorem equalAreaMovingNormalizedE8Chart_contDiffAt (v : Fin 8 → ℝ) (ε : ℝ)
    (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (v+ε • e8Map x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaMovingNormalizedE8Chart v ε) x :=
  ((equalAreaMovingE8Chart_contDiffAt v ε x hx).sub contDiffAt_const).const_smul ε⁻¹

theorem equalAreaMovingNormalizedE8Chart_iteratedFDeriv (v : Fin 8 → ℝ) (ε : ℝ)
    (x : Fin 8 → ℝ) (hx : equalAreaSquaredNorm (v+ε • e8Map x) < 1)
    (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (equalAreaMovingNormalizedE8Chart v ε) x =
      ε⁻¹ • (iteratedFDeriv ℝ k equalAreaPhi (v+ε • e8Map x)).compContinuousLinearMap
        (fun _ => ε • e8Map) := by
  have hf := (equalAreaMovingE8Chart_contDiffAt v ε x hx).of_le (by simp : (k:ℕ∞ω) ≤ ∞)
  have hsub := hf.sub (contDiffAt_const (c := equalAreaPhi v))
  change iteratedFDeriv ℝ k (fun y => ε⁻¹ • (equalAreaMovingE8Chart v ε y-equalAreaPhi v)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  change ε⁻¹ • iteratedFDeriv ℝ k (equalAreaMovingE8Chart v ε-(fun _ => equalAreaPhi v)) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero]
  exact congrArg (fun D => ε⁻¹ • D) (equalAreaPhi_iterated_comp_affine v (ε • e8Map) x hx k)

theorem equalAreaMovingNormalizedE8Chart_derivative_bound (v : Fin 8 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+ε • e8Map x) < 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedE8Chart v ε) x‖ ≤
      ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhi (v+ε • e8Map x)‖*‖e8Map‖^k := by
  rw [equalAreaMovingNormalizedE8Chart_iteratedFDeriv v ε x hx k (by omega),norm_smul]
  calc
    _ ≤ ‖ε⁻¹‖*(‖iteratedFDeriv ℝ k equalAreaPhi (v+ε • e8Map x)‖*
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
        _ = (ε⁻¹*ε^k)*‖iteratedFDeriv ℝ k equalAreaPhi (v+ε • e8Map x)‖*‖e8Map‖^k := by ring
        _ = _ := by rw [he]

theorem equalAreaMovingScaledE8_norm (v : Fin 8 → ℝ) (ε : ℝ)
    (x : Fin 8 → ℝ) (hx : ‖x‖ ≤ 1) :
    ‖v+ε • e8Map x‖ ≤ ‖v‖+|ε| * equalAreaScaleRadius := by
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |ε| * (‖e8Map‖*‖x‖) := mul_le_mul_of_nonneg_left (e8Map.le_opNorm x) (abs_nonneg ε)
    _ ≤ |ε| * (‖e8Map‖*1) := by gcongr
    _ ≤ _ := by unfold equalAreaScaleRadius; nlinarith [norm_nonneg e8Map,abs_nonneg ε]

theorem equalAreaMovingNormalizedE8Chart_high_derivatives (k : ℕ) (hk : 2 ≤ k) :
    ∃ C ≥ 0, ∀ v : Fin 8 → ℝ, ∀ ε : ℝ, 0 < ε →
      ‖v‖+ε*equalAreaScaleRadius ≤ 1/8 → ∀ x : Fin 8 → ℝ, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedE8Chart v ε) x‖ ≤ C*ε^(k-1) := by
  obtain ⟨C,hC,hb⟩ := equalAreaPhi_iterated_derivatives_bounded k
  refine ⟨C*‖e8Map‖^k,by positivity,?_⟩
  intro v ε hε hs x hx
  have hn : ‖v+ε • e8Map x‖ ≤ 1/8 := (equalAreaMovingScaledE8_norm v ε x hx).trans
    (by simpa only [abs_of_pos hε] using hs)
  calc
    _ ≤ ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhi (v+ε • e8Map x)‖*‖e8Map‖^k :=
      equalAreaMovingNormalizedE8Chart_derivative_bound v ε hε x
        (equalArea_small_norm_domain _ hn) k (by omega)
    _ ≤ ε^(k-1)*C*‖e8Map‖^k := by gcongr; exact hb _ hn
    _ = _ := by ring

theorem equalAreaMovingNormalizedE8Chart_hasFDerivAt (v : Fin 8 → ℝ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+ε • e8Map x) < 1) :
    HasFDerivAt (equalAreaMovingNormalizedE8Chart v ε)
      ((equalAreaPhiDerivative (v+ε • e8Map x)).comp e8Map) x := by
  have hf := (equalAreaPhi_hasFDerivAt _ hx).comp x
    ((ε • e8Map).hasFDerivAt.const_add v)
  have hg := (hf.sub_const (equalAreaPhi v)).const_smul ε⁻¹
  apply hg.congr_fderiv
  ext w
  simp [ContinuousLinearMap.comp_apply,smul_smul,hε]

theorem equalAreaMovingNormalizedE8Chart_fderiv (v : Fin 8 → ℝ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Fin 8 → ℝ)
    (hx : equalAreaSquaredNorm (v+ε • e8Map x) < 1) :
    fderiv ℝ (equalAreaMovingNormalizedE8Chart v ε) x =
      (fderiv ℝ equalAreaPhi (v+ε • e8Map x)).comp e8Map := by
  rw [equalAreaPhi_fderiv _ hx]
  exact (equalAreaMovingNormalizedE8Chart_hasFDerivAt v ε hε x hx).fderiv

/-- One radius controls every moving center and scale, uniformly on the
unit coordinate ball. No rate or first derivative bound is supplied. -/
theorem equalAreaMovingNormalizedE8Chart_first_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ x : Fin 8 → ℝ, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (equalAreaMovingNormalizedE8Chart v ε) x-equalAreaFlatDerivative8‖ ≤ η := by
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp
    equalAreaPhi_fderiv_comp_continuousAt_zero η hη
  let ρ : ℝ := min (δ/4) (1/16)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ,hρ,min_le_right _ _,?_⟩
  intro v hv ε hε hs x hx
  have hn : ‖v+ε • e8Map x‖ ≤ 2*ρ := (equalAreaMovingScaledE8_norm v ε x hx).trans
    (by rw [abs_of_pos hε]; linarith)
  have hsmall : ‖v+ε • e8Map x‖ ≤ 1/8 := hn.trans (by have := min_le_right (δ/4) (1/16); change ρ ≤ _ at this; linarith)
  have hclose : dist (v+ε • e8Map x) 0 < δ := by
    rw [dist_zero_right]
    have := min_le_left (δ/4) (1/16)
    change ρ ≤ _ at this
    linarith
  rw [equalAreaMovingNormalizedE8Chart_fderiv v ε hε.ne' x (equalArea_small_norm_domain _ hsmall)]
  have he : (fderiv ℝ equalAreaPhi (0 : Fin 8 → ℝ)).comp e8Map = equalAreaFlatDerivative8 := by
    rw [equalAreaPhi_fderiv _ (by simp [equalAreaSquaredNorm])]
    rfl
  simpa only [he,dist_eq_norm] using (hb hclose).le

end SphericalRiesz
