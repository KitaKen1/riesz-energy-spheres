import Riesz.EqualAreaRescalingGeometry24

/-! Moving coordinate centers in the actual exact-area chart.  All bounds
use one fixed compact smooth domain, independently of the center. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaMovingLeechChart (v : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ) : (AmbientD 24) :=
  equalAreaPhiD (v+ε • leechMap x)

def equalAreaMovingNormalizedLeechChart (v : Fin 24 → ℝ) (ε : ℝ)
    (x : Fin 24 → ℝ) : (AmbientD 24) :=
  ε⁻¹ • (equalAreaMovingLeechChart v ε x-equalAreaPhiD v)

theorem equalAreaPhi24_iterated_comp_affine (v : Fin 24 → ℝ)
    (L : (Fin 24 → ℝ) →L[ℝ] (Fin 24 → ℝ)) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+L x) < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => equalAreaPhiD (v+L y)) x =
      (iteratedFDeriv ℝ k equalAreaPhiD (v+L x)).compContinuousLinearMap (fun _ => L) := by
  have hq : Continuous (fun p => equalAreaSquaredNormD (v+p)) := by
    unfold equalAreaSquaredNormD; fun_prop
  have hu : IsOpen {p | equalAreaSquaredNormD (v+p) < 1} := isOpen_lt hq continuous_const
  have hf : ContDiffOn ℝ ∞ (fun p => equalAreaPhiD (v+p))
      {p | equalAreaSquaredNormD (v+p) < 1} := by
    intro p hp
    exact ((equalAreaPhi24_contDiffAt _ hp).comp p (by fun_prop)).contDiffWithinAt
  have hp := hu.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hu.uniqueDiffOn hp.uniqueDiffOn hx
    (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hu hx,iteratedFDeriv_comp_add_left] at h
  exact h

theorem equalAreaMovingLeechChart_contDiffAt (v : Fin 24 → ℝ) (ε : ℝ) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • leechMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaMovingLeechChart v ε) x :=
  (equalAreaPhi24_contDiffAt _ hx).comp x (by fun_prop)

theorem equalAreaMovingNormalizedLeechChart_contDiffAt (v : Fin 24 → ℝ) (ε : ℝ)
    (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (v+ε • leechMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaMovingNormalizedLeechChart v ε) x :=
  ((equalAreaMovingLeechChart_contDiffAt v ε x hx).sub contDiffAt_const).const_smul ε⁻¹

theorem equalAreaMovingNormalizedLeechChart_iteratedFDeriv (v : Fin 24 → ℝ) (ε : ℝ)
    (x : Fin 24 → ℝ) (hx : equalAreaSquaredNormD (v+ε • leechMap x) < 1)
    (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (equalAreaMovingNormalizedLeechChart v ε) x =
      ε⁻¹ • (iteratedFDeriv ℝ k equalAreaPhiD (v+ε • leechMap x)).compContinuousLinearMap
        (fun _ => ε • leechMap) := by
  have hf := (equalAreaMovingLeechChart_contDiffAt v ε x hx).of_le (by simp : (k:ℕ∞ω) ≤ ∞)
  have hsub := hf.sub (contDiffAt_const (c := equalAreaPhiD v))
  change iteratedFDeriv ℝ k (fun y => ε⁻¹ • (equalAreaMovingLeechChart v ε y-equalAreaPhiD v)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  change ε⁻¹ • iteratedFDeriv ℝ k (equalAreaMovingLeechChart v ε-(fun _ => equalAreaPhiD v)) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero]
  exact congrArg (fun D => ε⁻¹ • D) (equalAreaPhi24_iterated_comp_affine v (ε • leechMap) x hx k)

theorem equalAreaMovingNormalizedLeechChart_derivative_bound (v : Fin 24 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • leechMap x) < 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedLeechChart v ε) x‖ ≤
      ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • leechMap x)‖*‖leechMap‖^k := by
  rw [equalAreaMovingNormalizedLeechChart_iteratedFDeriv v ε x hx k (by omega),norm_smul]
  calc
    _ ≤ ‖ε⁻¹‖*(‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • leechMap x)‖*
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
        _ = (ε⁻¹*ε^k)*‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • leechMap x)‖*‖leechMap‖^k := by ring
        _ = _ := by rw [he]

theorem equalAreaMovingScaledLeech_norm (v : Fin 24 → ℝ) (ε : ℝ)
    (x : Fin 24 → ℝ) (hx : ‖x‖ ≤ 1) :
    ‖v+ε • leechMap x‖ ≤ ‖v‖+|ε| * equalAreaScaleRadius24 := by
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |ε| * (‖leechMap‖*‖x‖) := mul_le_mul_of_nonneg_left (leechMap.le_opNorm x) (abs_nonneg ε)
    _ ≤ |ε| * (‖leechMap‖*1) := by gcongr
    _ ≤ _ := by unfold equalAreaScaleRadius24; nlinarith [norm_nonneg leechMap,abs_nonneg ε]

theorem equalAreaMovingNormalizedLeechChart_high_derivatives (k : ℕ) (hk : 2 ≤ k) :
    ∃ C ≥ 0, ∀ v : Fin 24 → ℝ, ∀ ε : ℝ, 0 < ε →
      ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8 → ∀ x : Fin 24 → ℝ, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedLeechChart v ε) x‖ ≤ C*ε^(k-1) := by
  obtain ⟨C,hC,hb⟩ := equalAreaPhi24_iterated_derivatives_bounded k
  refine ⟨C*‖leechMap‖^k,by positivity,?_⟩
  intro v ε hε hs x hx
  have hn : ‖v+ε • leechMap x‖ ≤ 1/8 := (equalAreaMovingScaledLeech_norm v ε x hx).trans
    (by simpa only [abs_of_pos hε] using hs)
  calc
    _ ≤ ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • leechMap x)‖*‖leechMap‖^k :=
      equalAreaMovingNormalizedLeechChart_derivative_bound v ε hε x
        (equalArea24_small_norm_domain _ hn) k (by omega)
    _ ≤ ε^(k-1)*C*‖leechMap‖^k := by gcongr; exact hb _ hn
    _ = _ := by ring

theorem equalAreaMovingNormalizedLeechChart_hasFDerivAt (v : Fin 24 → ℝ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • leechMap x) < 1) :
    HasFDerivAt (equalAreaMovingNormalizedLeechChart v ε)
      ((equalAreaPhiDerivativeD (v+ε • leechMap x)).comp leechMap) x := by
  have hf := (equalAreaPhiD_hasFDerivAt _ hx).comp x
    ((ε • leechMap).hasFDerivAt.const_add v)
  have hg := (hf.sub_const (equalAreaPhiD v)).const_smul ε⁻¹
  apply hg.congr_fderiv
  ext w
  simp [ContinuousLinearMap.comp_apply,smul_smul,hε]

theorem equalAreaMovingNormalizedLeechChart_fderiv (v : Fin 24 → ℝ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Fin 24 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • leechMap x) < 1) :
    fderiv ℝ (equalAreaMovingNormalizedLeechChart v ε) x =
      (fderiv ℝ equalAreaPhiD (v+ε • leechMap x)).comp leechMap := by
  rw [equalAreaPhiD_fderiv _ hx]
  exact (equalAreaMovingNormalizedLeechChart_hasFDerivAt v ε hε x hx).fderiv

/-- One radius controls every moving center and scale, uniformly on the
unit coordinate ball. No rate or first derivative bound is supplied. -/
theorem equalAreaMovingNormalizedLeechChart_first_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 24 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ x : Fin 24 → ℝ, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (equalAreaMovingNormalizedLeechChart v ε) x-equalAreaFlatDerivative24‖ ≤ η := by
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp
    equalAreaPhi24_fderiv_comp_continuousAt_zero η hη
  let ρ : ℝ := min (δ/4) (1/16)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ,hρ,min_le_right _ _,?_⟩
  intro v hv ε hε hs x hx
  have hn : ‖v+ε • leechMap x‖ ≤ 2*ρ := (equalAreaMovingScaledLeech_norm v ε x hx).trans
    (by rw [abs_of_pos hε]; linarith)
  have hsmall : ‖v+ε • leechMap x‖ ≤ 1/8 := hn.trans (by have := min_le_right (δ/4) (1/16); change ρ ≤ _ at this; linarith)
  have hclose : dist (v+ε • leechMap x) 0 < δ := by
    rw [dist_zero_right]
    have := min_le_left (δ/4) (1/16)
    change ρ ≤ _ at this
    linarith
  rw [equalAreaMovingNormalizedLeechChart_fderiv v ε hε.ne' x (equalArea24_small_norm_domain _ hsmall)]
  have he : (fderiv ℝ equalAreaPhiD (0 : Fin 24 → ℝ)).comp leechMap = equalAreaFlatDerivative24 := by
    rw [equalAreaPhiD_fderiv _ (by simp [equalAreaSquaredNormD])]
    rfl
  simpa only [he,dist_eq_norm] using (hb hclose).le

end SphericalRiesz
