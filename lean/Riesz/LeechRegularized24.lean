import Riesz.LeechGaussianContact24
import Mathlib.Analysis.MellinTransform

/-! # The regularized Leech theta function (stage P24-3)

On the imaginary axis `Θ_Λ(it)` is the real Gaussian lattice sum. Poisson inversion gives
`Θ_Λ(i/t) = t^12 Θ_Λ(it)`, and evenness (every nonzero vector has `|v|² ≥ 2`) gives the
elementary tail bound `Θ_Λ(it) - 1 ≤ e^(-2π(t-1)) (Θ_Λ(i) - 1)` for `t ≥ 1`, with no modular-form
input. Hence `Θ_Λ(it) - 1 - t^(-12)` is bounded near `0`, is `O(t^(-12))` at infinity, and its
Mellin transform converges on `0 < Re s < 12`. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace SphericalRiesz

def leechThetaImag (t : ℝ) : ℂ := leechTheta ((t : ℂ) * Complex.I)

def leechThetaTail (t : ℝ) : ℂ := leechThetaImag t - 1

def leechThetaRegularized (t : ℝ) : ℂ := leechThetaTail t - ((t : ℂ)^12)⁻¹

theorem leechThetaImag_eq_real {t : ℝ} (ht : 0 < t) :
    leechThetaImag t = (leechGaussianThetaReal24 t : ℂ) := by
  have hτ : 0 < ((t:ℂ)*Complex.I).im := by simpa using ht
  have hterm : ∀ x : leechLattice, leechLatticeThetaTerm ((t:ℂ)*Complex.I) x =
      ((Real.exp (-(Real.pi*t*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ) := by
    intro x
    unfold leechLatticeThetaTerm
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : leechLatticeThetaTerm ((t:ℂ)*Complex.I) = fun x : leechLattice =>
      ((Real.exp (-(Real.pi*t*‖(x : LeechAmbient)‖^2)) : ℝ) : ℂ) := funext hterm
  unfold leechThetaImag leechTheta
  rw [hfun]
  exact (leechLatticeGaussian_hasSum ht).tsum_eq

theorem leechThetaImag_continuousOn : ContinuousOn leechThetaImag (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => (leechGaussianThetaReal24 t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn leechGaussianThetaReal24_continuousOn
  exact h.congr (fun t ht => leechThetaImag_eq_real ht)

theorem leechThetaTail_continuousOn : ContinuousOn leechThetaTail (Ioi 0) :=
  leechThetaImag_continuousOn.sub continuousOn_const

theorem leechThetaRegularized_continuousOn : ContinuousOn leechThetaRegularized (Ioi 0) := by
  apply leechThetaTail_continuousOn.sub
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))

theorem leechThetaImag_transform {t : ℝ} (ht : 0 < t) :
    leechThetaImag t⁻¹ = (t : ℂ)^12 * leechThetaImag t := by
  have h := leechTheta_transform_S (τ := (t : ℂ)*Complex.I) (by simpa using ht)
  have hI12 : Complex.I^12 = 1 := by
    rw [show (12:ℕ) = 4*3 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hS : -1/((t:ℂ)*Complex.I) = ((t⁻¹ : ℝ) : ℂ)*Complex.I := by
    push_cast
    field_simp
    rw [Complex.I_sq]
  unfold leechThetaImag
  rw [← hS, h, mul_pow, hI12, mul_one]

theorem leechThetaRegularized_inversion {t : ℝ} (ht : 0 < t) :
    leechThetaRegularized t = ((t : ℂ)^12)⁻¹ * leechThetaTail t⁻¹ - 1 := by
  have h := leechThetaImag_transform ht
  have h0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold leechThetaRegularized leechThetaTail
  rw [h]
  field_simp
  ring

/-- Nonzero Leech vectors have squared norm at least two (evenness). -/
theorem leechLattice_norm_sq_ge_two (x : leechLattice) (hx : (x : LeechAmbient) ≠ 0) :
    2 ≤ ‖(x : LeechAmbient)‖^2 := by
  obtain ⟨k, hk⟩ := leechLattice_even x
  have hpos : 0 < ‖(x : LeechAmbient)‖^2 := by positivity
  rw [hk] at hpos ⊢
  have hk1 : (1:ℝ) ≤ k := by
    have : (0:ℝ) < k := by linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by intro h; rw [h] at this; norm_num at this)
  linarith

/-- The real tail `Θ_Λ(t) - 1` decays like `e^(-2π t)`. -/
theorem leechGaussianThetaReal24_tail_le {t : ℝ} (ht : 1 ≤ t) :
    leechGaussianThetaReal24 t - 1 ≤
      Real.exp (-(2*Real.pi)*(t-1)) * (leechGaussianThetaReal24 1 - 1) := by
  classical
  have ht0 : 0 < t := by linarith
  let f : ℝ → leechLattice → ℝ := fun u x => Real.exp (-(Real.pi*u*‖(x : LeechAmbient)‖^2))
  have hf : ∀ u, 0 < u → HasSum (f u) (leechGaussianThetaReal24 u) := fun u hu =>
    Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hu)
  have hf0 : ∀ u, f u 0 = 1 := fun u => by simp [f]
  have h1 := (hf t ht0).update (0 : leechLattice) 0
  have h2 := ((hf 1 one_pos).update (0 : leechLattice) 0).mul_left (Real.exp (-(2*Real.pi)*(t-1)))
  rw [hf0] at h1 h2
  have hle : ∀ x, Function.update (f t) (0 : leechLattice) 0 x ≤
      Real.exp (-(2*Real.pi)*(t-1)) * Function.update (f 1) (0 : leechLattice) 0 x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
      have hx0 : (x : LeechAmbient) ≠ 0 := fun h => hx (Subtype.ext h)
      have hn := leechLattice_norm_sq_ge_two x hx0
      simp only [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h3 : 0 ≤ t-1 := by linarith
      have h4 := mul_le_mul_of_nonneg_left hn (mul_nonneg Real.pi_pos.le h3)
      nlinarith [h4]
  have := hasSum_le hle h1 h2
  linarith

theorem leechGaussianThetaReal24_ge_one' {t : ℝ} (ht : 0 < t) : 1 ≤ leechGaussianThetaReal24 t :=
  leechGaussianThetaReal24_ge_one ht

theorem leechThetaTail_exp_decay :
    leechThetaTail =O[atTop] (fun t : ℝ => Real.exp (-(2*Real.pi)*t)) := by
  refine isBigO_iff.mpr ⟨Real.exp (2*Real.pi) * (leechGaussianThetaReal24 1 - 1), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have htail : leechThetaTail t = ((leechGaussianThetaReal24 t - 1 : ℝ) : ℂ) := by
    unfold leechThetaTail
    rw [leechThetaImag_eq_real ht0]
    push_cast
    ring
  rw [htail, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [leechGaussianThetaReal24_ge_one ht0]), abs_of_pos (Real.exp_pos _)]
  have h := leechGaussianThetaReal24_tail_le ht
  have he : Real.exp (-(2*Real.pi)*(t-1)) = Real.exp (2*Real.pi) * Real.exp (-(2*Real.pi)*t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he] at h
  linarith

theorem leechThetaTail_littleO_rpow (a : ℝ) :
    leechThetaTail =o[atTop] (fun t : ℝ => t^a) :=
  leechThetaTail_exp_decay.trans_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop (by positivity) a)

theorem leechThetaTail_scaled_tendsto :
    Tendsto (fun t : ℝ => (t : ℂ)^12 * leechThetaTail t) atTop (𝓝 0) := by
  have h := (leechThetaTail_littleO_rpow (-12)).tendsto_inv_smul_nhds_zero (𝕜 := ℝ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.rpow_neg ht.le, inv_inv,
    show (12 : ℝ) = (12 : ℕ) by norm_num, Real.rpow_natCast]
  simp [Complex.real_smul]

theorem leechThetaRegularized_tendsto_zero :
    Tendsto leechThetaRegularized (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have h := leechThetaTail_scaled_tendsto.comp tendsto_inv_nhdsGT_zero
  have h' := h.sub_const (1 : ℂ)
  simp only [zero_sub] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [leechThetaRegularized_inversion ht]
  simp [Complex.ofReal_inv, inv_pow]

theorem leechThetaRegularized_bigO_zero :
    leechThetaRegularized =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t^(-(0 : ℝ))) := by
  simpa using leechThetaRegularized_tendsto_zero.isBigO_one ℝ

theorem leechThetaRegularized_bigO_infty :
    leechThetaRegularized =O[atTop] (fun t : ℝ => t^(-(12 : ℝ))) := by
  have hp : (fun t : ℝ => ((t : ℂ)^12)⁻¹) =O[atTop]
      (fun t : ℝ => t^(-(12 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Real.rpow_neg ht.le, Real.rpow_ofNat]
  exact (leechThetaTail_littleO_rpow (-12)).isBigO.sub hp

theorem leechThetaRegularized_mellinConvergent {s : ℂ}
    (h0 : 0 < s.re) (h12 : s.re < 12) : MellinConvergent leechThetaRegularized s :=
  mellinConvergent_of_isBigO_rpow
    (leechThetaRegularized_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    leechThetaRegularized_bigO_infty h12 leechThetaRegularized_bigO_zero h0

theorem leechThetaRegularized_mellin_differentiableAt {s : ℂ}
    (h0 : 0 < s.re) (h12 : s.re < 12) :
    DifferentiableAt ℂ (mellin leechThetaRegularized) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (leechThetaRegularized_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    leechThetaRegularized_bigO_infty h12 leechThetaRegularized_bigO_zero h0).2.differentiableAt

#print axioms leechThetaImag_eq_real
#print axioms leechThetaImag_continuousOn
#print axioms leechThetaRegularized_continuousOn
#print axioms leechThetaImag_transform
#print axioms leechThetaRegularized_inversion
#print axioms leechLattice_norm_sq_ge_two
#print axioms leechGaussianThetaReal24_tail_le
#print axioms leechThetaTail_exp_decay
#print axioms leechThetaTail_littleO_rpow
#print axioms leechThetaTail_scaled_tendsto
#print axioms leechThetaRegularized_tendsto_zero
#print axioms leechThetaRegularized_bigO_zero
#print axioms leechThetaRegularized_bigO_infty
#print axioms leechThetaRegularized_mellinConvergent
#print axioms leechThetaRegularized_mellin_differentiableAt

end SphericalRiesz
