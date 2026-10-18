import Mathlib

/-! The Gamma function on the strip `-1 < a < 0` as a subtracted Mellin integral.

For `-1 < a < 0`, `∫₀^∞ t^(a-1) (e^(-t) - 1) dt = Γ(a)`: integrate by parts against
`t^a/a` and use `Γ(a+1) = a Γ(a)`. Rescaling gives, for every `d ≥ 0`,
`∫₀^∞ t^(a-1) (e^(-d² t) - 1) dt = Γ(a) d^(-2a)`, the Mellin representation of the
negative-exponent Riesz kernel `d^(-s)`, `s = 2a ∈ (-2, 0)` (the diagonal `d = 0` included). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SphericalRiesz

/-- A function continuous on `(0,∞)` and bounded by `C t^(a-1) min(t,1)` is integrable there,
for `-1 < a < 0`. -/
theorem integrableOn_Ioi_of_rpow_min_bound {f : ℝ → ℝ} {a C : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hf : ContinuousOn f (Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |f t| ≤ C*(t^(a-1)*min t 1)) :
    IntegrableOn f (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  apply IntegrableOn.union
  · have hd : IntegrableOn (fun t : ℝ => C*t^a) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' ha)).const_mul C
    refine Integrable.mono' hd ((hf.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    have hC : 0 ≤ C := by
      have h1 := (abs_nonneg (f t)).trans (hb t ht.1)
      have h2 : 0 < t^(a-1)*min t 1 :=
        mul_pos (Real.rpow_pos_of_pos ht.1 _) (lt_min ht.1 zero_lt_one)
      exact nonneg_of_mul_nonneg_left h1 h2
    refine (hb t ht.1).trans ?_
    have hm : t^(a-1)*min t 1 ≤ t^(a-1)*t :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg ht.1.le _)
    have he : t^(a-1)*t = t^a := by rw [← Real.rpow_add_one ht.1.ne', sub_add_cancel]
    rw [he] at hm
    exact mul_le_mul_of_nonneg_left hm hC
  · have hd : IntegrableOn (fun t : ℝ => C*t^(a-1)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul C
    refine Integrable.mono' hd ((hf.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
    have hC : 0 ≤ C := by
      have h1 := (abs_nonneg (f t)).trans (hb t ht0)
      have h2 : 0 < t^(a-1)*min t 1 :=
        mul_pos (Real.rpow_pos_of_pos ht0 _) (lt_min ht0 zero_lt_one)
      exact nonneg_of_mul_nonneg_left h1 h2
    refine (hb t ht0).trans ?_
    have hm : t^(a-1)*min t 1 ≤ t^(a-1) := by
      have := mul_le_mul_of_nonneg_left (min_le_right t 1) (Real.rpow_nonneg ht0.le (a-1))
      rwa [mul_one] at this
    exact mul_le_mul_of_nonneg_left hm hC

theorem one_sub_exp_neg_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1-Real.exp (-t) ∧ 1-Real.exp (-t) ≤ min t 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.add_one_le_exp (-t)
  have h3 := Real.exp_pos (-t)
  exact ⟨by linarith, le_min (by linarith) (by linarith)⟩

theorem rpow_mul_exp_sub_one_integrableOn {a : ℝ} (ha : -1 < a) (ha0 : a < 0) :
    IntegrableOn (fun t : ℝ => t^(a-1)*(Real.exp (-t)-1)) (Ioi 0) := by
  apply integrableOn_Ioi_of_rpow_min_bound (C := 1) ha ha0
  · intro t ht
    exact ((Real.continuousAt_rpow_const t (a-1) (Or.inl (ne_of_gt ht))).mul
      ((Real.continuous_exp.comp continuous_neg).continuousAt.sub
        continuousAt_const)).continuousWithinAt
  · intro t ht
    obtain ⟨h1, h2⟩ := one_sub_exp_neg_bounds ht.le
    have hw : 0 ≤ t^(a-1) := Real.rpow_nonneg ht.le _
    rw [abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub, one_mul]
    exact mul_le_mul_of_nonneg_left h2 hw

/-- `Γ(a)` on the strip `-1 < a < 0` as the subtracted Mellin integral. -/
theorem integral_rpow_mul_exp_sub_one {a : ℝ} (ha : -1 < a) (ha0 : a < 0) :
    (∫ t : ℝ in Ioi 0, t^(a-1)*(Real.exp (-t)-1)) = Real.Gamma a := by
  have hane : a ≠ 0 := ha0.ne
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun t : ℝ => Real.exp (-t)-1) (-Real.exp (-x)) x := by
    intro x _
    have h := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).sub_const 1
    have he : Real.exp (-x) * -1 = -Real.exp (-x) := by ring
    rw [he] at h
    exact h
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun t : ℝ => t^a/a) (x^(a-1)) x := by
    intro x hx
    have h := (Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl (ne_of_gt hx))).div_const a
    convert h using 1
    field_simp
  have huv' : IntegrableOn ((fun t : ℝ => Real.exp (-t)-1)*(fun t : ℝ => t^(a-1))) (Ioi 0) := by
    refine (rpow_mul_exp_sub_one_integrableOn ha ha0).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hΓ : IntegrableOn (fun t : ℝ => Real.exp (-t)*t^(a+1-1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by linarith)
  have hu'v : IntegrableOn ((fun t : ℝ => -Real.exp (-t))*(fun t : ℝ => t^a/a)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.const_mul hΓ (-a⁻¹)) (fun t _ => ?_)
      measurableSet_Ioi
    simp only [Pi.mul_apply, add_sub_cancel_right]
    field_simp
  have hbound : ∀ t : ℝ, 0 < t →
      ‖((fun t : ℝ => Real.exp (-t)-1)*(fun t : ℝ => t^a/a)) t‖ ≤ min t 1*t^a/|a| := by
    intro t ht
    obtain ⟨h1, h2⟩ := one_sub_exp_neg_bounds ht.le
    have hw : 0 ≤ t^a := Real.rpow_nonneg ht.le _
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hw]
    rw [abs_of_nonpos (by linarith), neg_sub, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right h2 (div_nonneg hw (abs_nonneg a))
  have h0 : Tendsto ((fun t : ℝ => Real.exp (-t)-1)*(fun t : ℝ => t^a/a)) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => t^(a+1)/|a|) (𝓝[>] 0) (𝓝 0) := by
      have hc := (Real.continuous_rpow_const (q := a+1) (by linarith)).tendsto 0
      rw [Real.zero_rpow (by linarith)] at hc
      simpa using (hc.mono_left nhdsWithin_le_nhds).div_const |a|
    apply squeeze_zero_norm' _ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine (hbound t ht).trans ?_
    have hw : 0 ≤ t^a := Real.rpow_nonneg (le_of_lt ht) _
    have he : t*t^a = t^(a+1) := by rw [Real.rpow_add_one (ne_of_gt ht), mul_comm]
    rw [← he]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hw)
      (abs_nonneg a)
  have hinf : Tendsto ((fun t : ℝ => Real.exp (-t)-1)*(fun t : ℝ => t^a/a)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => t^a/|a|) atTop (𝓝 0) := by
      have hc := tendsto_rpow_neg_atTop (y := -a) (by linarith)
      simp only [neg_neg] at hc
      simpa using hc.div_const |a|
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    refine (hbound t ht).trans ?_
    have hw : 0 ≤ t^a := Real.rpow_nonneg (le_of_lt ht) _
    have hm : min t 1*t^a ≤ t^a := by
      have := mul_le_mul_of_nonneg_right (min_le_right t 1) hw
      rwa [one_mul] at this
    exact div_le_div_of_nonneg_right hm (abs_nonneg a)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have hl : (∫ t : ℝ in Ioi 0, t^(a-1)*(Real.exp (-t)-1)) =
      ∫ x : ℝ in Ioi 0, (Real.exp (-x)-1)*x^(a-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  have hr : (∫ x : ℝ in Ioi 0, -Real.exp (-x)*(x^a/a)) =
      -a⁻¹*∫ x : ℝ in Ioi 0, Real.exp (-x)*x^(a+1-1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [add_sub_cancel_right]
    field_simp
  rw [hl, h, hr, ← Real.Gamma_eq_integral (by linarith), Real.Gamma_add_one hane]
  field_simp
  ring

/-- The Mellin representation of `d^(-s)` for `-2 < s < 0`, including `d = 0`. -/
theorem gaussianPair_mellin_neg {s d : ℝ} (hs : -2 < s) (hs0 : s < 0) (hd : 0 ≤ d) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*(Real.exp (-(d^2*t))-1)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*(Real.exp (-(d^2*t))-1)) = Real.Gamma (s/2)*d^(-s) := by
  rcases hd.eq_or_lt with hd0 | hd
  · subst hd0
    have hz : (fun t : ℝ => t^(s/2-1)*(Real.exp (-((0:ℝ)^2*t))-1)) = fun _ => 0 := by
      funext t
      simp
    rw [hz]
    refine ⟨integrableOn_zero, ?_⟩
    rw [Real.zero_rpow (by linarith)]
    simp
  · have ha : -1 < s/2 := by linarith
    have ha0 : s/2 < 0 := by linarith
    set g : ℝ → ℝ := fun t => t^(s/2-1)*(Real.exp (-t)-1) with hg
    have hgi : IntegrableOn g (Ioi 0) := rpow_mul_exp_sub_one_integrableOn ha ha0
    have hb : 0 < d^2 := by positivity
    have hcomp : ∀ t ∈ Ioi (0:ℝ), t^(s/2-1)*(Real.exp (-(d^2*t))-1) =
        (d^2)^(1-s/2)*g (d^2*t) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      simp only [hg]
      rw [Real.mul_rpow hb.le ht0.le]
      have hcancel : (d^2)^(1-s/2)*(d^2)^(s/2-1) = 1 := by
        rw [← Real.rpow_add hb, show 1-s/2+(s/2-1) = (0:ℝ) by ring, Real.rpow_zero]
      calc t^(s/2-1)*(Real.exp (-(d^2*t))-1)
          = ((d^2)^(1-s/2)*(d^2)^(s/2-1))*(t^(s/2-1)*(Real.exp (-(d^2*t))-1)) := by
            rw [hcancel, one_mul]
        _ = (d^2)^(1-s/2)*((d^2)^(s/2-1)*t^(s/2-1)*(Real.exp (-(d^2*t))-1)) := by ring
    constructor
    · have h1 : IntegrableOn (fun t : ℝ => g (d^2*t)) (Ioi 0) := by
        apply (integrableOn_Ioi_comp_mul_left_iff g 0 hb).mpr
        simpa only [mul_zero] using hgi
      exact IntegrableOn.congr_fun (Integrable.const_mul h1 ((d^2)^(1-s/2)))
        (fun t ht => (hcomp t ht).symm) measurableSet_Ioi
    · rw [setIntegral_congr_fun measurableSet_Ioi hcomp, integral_const_mul,
        integral_comp_mul_left_Ioi g 0 hb, mul_zero, smul_eq_mul, hg,
        integral_rpow_mul_exp_sub_one ha ha0]
      have h1 : (d^2)^(1-s/2)*(d^2)⁻¹ = (d^2)^(-(s/2)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
        congr 1
        ring
      have h2 : (d^2)^(-(s/2)) = d^(-s) := by
        rw [← Real.rpow_natCast d 2, ← Real.rpow_mul hd.le]
        congr 1
        push_cast
        ring
      calc (d^2)^(1-s/2)*((d^2)⁻¹*Real.Gamma (s/2))
          = ((d^2)^(1-s/2)*(d^2)⁻¹)*Real.Gamma (s/2) := by ring
        _ = Real.Gamma (s/2)*d^(-s) := by rw [h1, h2, mul_comm]

#print axioms integrableOn_Ioi_of_rpow_min_bound
#print axioms one_sub_exp_neg_bounds
#print axioms rpow_mul_exp_sub_one_integrableOn
#print axioms integral_rpow_mul_exp_sub_one
#print axioms gaussianPair_mellin_neg

end SphericalRiesz
