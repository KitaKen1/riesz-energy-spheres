import Riesz.SphereLogLower8

/-! The logarithmic coefficient in closed form (stage LOG).

`κ = ∫ α⁻¹ (e^(-α) - 1_{(0,1)}) = Γ'(1)`: for `0 < a`, `∫ t^(a-1) (e^(-t) - 1_{(0,1)}) = Γ(a) - 1/a`
`= (Γ(1+a) - Γ(1))/a`, and dominated convergence as `a → 0⁺`. The E8 profile integral is
`∫ g = Re Λ₀(0) - 1/4`, and `Λ₀(u) = Λ(u) + 1/u + 1/(4-u)` with `Λ(u) = π^(-u) Γ(u) E(u)` on
`(0,1)`, `E(u) = 2^(-u) 240 ζ(u) ζ(u-3)`, `E(0) = -1`. With `H(u) = Γ(u+1) π^(-u) Re E(u)`,
`Re Λ₀(u) = (H(u) - H(0))/u + 1/(4-u)`, so `Re Λ₀(0) = H'(0) + 1/4` and
`∫ g = -Γ'(1) + log π + Re E'(0)`. The Euler constants cancel:
`C_log = ½ Re E'(0) + ⅛ log A₈` (`½ E'(0)` is the derivative of the E8 Epstein zeta at `s = 0`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem gamma_sub_inv_integral {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t^(a-1)*(Real.exp (-t)-(Ioo (0:ℝ) 1).indicator 1 t)) (Ioi 0) ∧
    (∫ t in Ioi 0, t^(a-1)*(Real.exp (-t)-(Ioo (0:ℝ) 1).indicator 1 t)) = Real.Gamma a-1/a := by
  have h1 : IntegrableOn (fun t : ℝ => t^(a-1)*Real.exp (-t)) (Ioi 0) := by
    have := Real.GammaIntegral_convergent ha
    exact this.congr_fun (fun t _ => by ring) measurableSet_Ioi
  have hind : (fun t : ℝ => t^(a-1)*(Ioo (0:ℝ) 1).indicator 1 t) =
      (Ioo (0:ℝ) 1).indicator (fun t => t^(a-1)) := by
    funext t
    by_cases h : t ∈ Ioo (0:ℝ) 1
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  have h2 : IntegrableOn (fun t : ℝ => t^(a-1)*(Ioo (0:ℝ) 1).indicator 1 t) (Ioi 0) := by
    have hI : IntegrableOn (fun t : ℝ => t^(a-1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    rw [hind]
    exact (hI.integrable_indicator measurableSet_Ioo).integrableOn
  have hfun : (fun t : ℝ => t^(a-1)*(Real.exp (-t)-(Ioo (0:ℝ) 1).indicator 1 t)) =
      fun t => t^(a-1)*Real.exp (-t)-t^(a-1)*(Ioo (0:ℝ) 1).indicator 1 t := by
    funext t; ring
  rw [hfun]
  refine ⟨h1.sub h2, ?_⟩
  rw [integral_sub h1 h2]
  have hΓ : (∫ t in Ioi 0, t^(a-1)*Real.exp (-t)) = Real.Gamma a := by
    rw [Real.Gamma_eq_integral ha]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  have hI : (∫ t in Ioi 0, t^(a-1)*(Ioo (0:ℝ) 1).indicator 1 t) = 1/a := by
    rw [hind, setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < a-1))]
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow ha.ne', sub_zero]
  rw [hΓ, hI]

/-- `κ = Γ'(1)`. -/
theorem logGaussianConst_eq_deriv_Gamma : logGaussianConst = deriv Real.Gamma 1 := by
  set F : ℝ → ℝ → ℝ := fun a t => t^(a-1)*(Real.exp (-t)-(Ioo (0:ℝ) 1).indicator 1 t) with hF
  set bound : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator 1 t+Real.exp (-t) with hb
  have hbound : IntegrableOn bound (Ioi 0) := by
    have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc 0 1) := integrableOn_const (by simp)
    have h1 : IntegrableOn ((Ioc (0:ℝ) 1).indicator 1) (Ioi 0) :=
      (hc.integrable_indicator measurableSet_Ioc).integrableOn
    have h2 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
      have := exp_neg_integrableOn_Ioi 0 one_pos
      exact this.congr_fun (fun t _ => by simp) measurableSet_Ioi
    exact h1.add h2
  have hlim1 : Tendsto (fun a => ∫ t in Ioi 0, F a t) (𝓝[>] 0) (𝓝 logGaussianConst) := by
    unfold logGaussianConst
    apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact ((gamma_sub_inv_integral ha).1).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with a ha
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      simp only [hF, hb, Real.norm_eq_abs]
      rcases lt_trichotomy t 1 with h | h | h
      · have hm : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, h⟩
        have hm' : t ∈ Ioc (0:ℝ) 1 := ⟨ht0, h.le⟩
        simp only [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply]
        obtain ⟨e1, e2⟩ := one_sub_exp_neg_bounds ht0.le
        have hw : 0 ≤ t^(a-1) := Real.rpow_nonneg ht0.le _
        rw [abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub]
        have hta : t^(a-1)*t = t^a := by rw [← Real.rpow_add_one ht0.ne', sub_add_cancel]
        have hle : t^a ≤ 1 := Real.rpow_le_one ht0.le h.le ha.1.le
        calc t^(a-1)*(1-Real.exp (-t)) ≤ t^(a-1)*t :=
              mul_le_mul_of_nonneg_left (e2.trans (min_le_left _ _)) hw
          _ ≤ 1 := by rw [hta]; exact hle
          _ ≤ 1+Real.exp (-t) := by linarith [Real.exp_pos (-t)]
      · subst h
        have hm : (1:ℝ) ∉ Ioo (0:ℝ) 1 := fun h => lt_irrefl _ h.2
        have hm' : (1:ℝ) ∈ Ioc (0:ℝ) 1 := ⟨one_pos, le_rfl⟩
        simp only [indicator_of_notMem hm, indicator_of_mem hm', Pi.one_apply, sub_zero,
          Real.one_rpow, one_mul, abs_of_pos (Real.exp_pos _)]
        linarith
      · have hm : t ∉ Ioo (0:ℝ) 1 := fun hh => by linarith [hh.2]
        have hm' : t ∉ Ioc (0:ℝ) 1 := fun hh => by linarith [hh.2]
        simp only [indicator_of_notMem hm, indicator_of_notMem hm', sub_zero, zero_add]
        rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        have hle : t^(a-1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith [ha.2])
        calc t^(a-1)*Real.exp (-t) ≤ 1*Real.exp (-t) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
          _ = Real.exp (-t) := one_mul _
    · exact hbound
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      have hc : Tendsto (fun a : ℝ => t^(a-1)) (𝓝[>] 0) (𝓝 (t^((0:ℝ)-1))) :=
        ((Real.continuousAt_const_rpow ht0.ne').comp
          (continuous_sub_right (1:ℝ)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      have he : t^((0:ℝ)-1) = t⁻¹ := by rw [zero_sub, Real.rpow_neg_one]
      rw [he] at hc
      exact hc.mul_const _
  have hlim2 : Tendsto (fun a => ∫ t in Ioi 0, F a t) (𝓝[>] 0) (𝓝 (deriv Real.Gamma 1)) := by
    have hd : HasDerivAt Real.Gamma (deriv Real.Gamma 1) 1 :=
      (Real.differentiableAt_Gamma (fun m h => by
        have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith)).hasDerivAt
    have hs := hd.tendsto_slope_zero_right
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : (0:ℝ) < a := ha
    rw [(gamma_sub_inv_integral ha0).2, smul_eq_mul, add_comm (1:ℝ) a,
      Real.Gamma_add_one ha0.ne', Real.Gamma_one]
    field_simp
  exact tendsto_nhds_unique hlim1 hlim2

/-- The E8 logarithmic profile integral through the entire part `Λ₀` of the completed theta. -/
theorem e8GaussianLogProfile8_integral_eq :
    (∫ α in Ioi 0, e8GaussianLogProfile8 α) = (e8ThetaFEPair.Λ₀ 0).re-1/4 := by
  rw [integral_congr_ae e8GaussianLogProfile8_ae]
  have hmod : IntegrableOn (fun t : ℝ => ((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t) (Ioi 0) :=
    (e8ThetaFEPair.isStrongFEPair_toStrongFEPair.hasMellin (0:ℂ)).1
  have h5 : IntegrableOn (fun t : ℝ => t^(-5:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hl := (h5.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have hre : IntegrableOn (fun t : ℝ => (((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t).re) (Ioi 0) :=
    hmod.re
  rw [integral_sub hre hl]
  have h1 : (∫ t in Ioi (0:ℝ), (((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t).re) =
      (e8ThetaFEPair.Λ₀ 0).re := by
    have h := integral_re hmod
    change (∫ t : ℝ in Ioi 0, (((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t).re) =
      (∫ t : ℝ in Ioi 0, ((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t).re at h
    rw [h]
    rfl
  have h2 : (∫ t in Ioi (0:ℝ), (Ioi 1).indicator (fun t : ℝ => t^(-5:ℝ)) t) = 1/4 := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1)),
      integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
  rw [h1, h2]

theorem riemannZeta_neg_three : riemannZeta (-3) = 1/120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 3
  have hb : bernoulli 4 = -1/30 := by
    rw [bernoulli, bernoulli'_four]
    norm_num
  push_cast at h
  rw [h, hb]
  push_cast
  norm_num

theorem e8EpsteinCandidate_zero : e8EpsteinCandidate 0 = -1 := by
  unfold e8EpsteinCandidate
  rw [neg_zero, Complex.cpow_zero, riemannZeta_zero, zero_sub, riemannZeta_neg_three]
  norm_num

/-- `Re Λ₀(0) = H'(0) + 1/4` with `H(u) = Γ(u+1) π^(-u) Re E(u)`. -/
theorem e8ThetaFEPair_Λ₀_zero_re :
    (e8ThetaFEPair.Λ₀ 0).re =
      -deriv Real.Gamma 1+Real.log Real.pi+(deriv e8EpsteinCandidate 0).re+1/4 := by
  set e : ℝ → ℝ := fun u => (e8EpsteinCandidate (u:ℂ)).re with he
  have he0 : e 0 = -1 := by
    simp only [he, Complex.ofReal_zero, e8EpsteinCandidate_zero, Complex.neg_re, Complex.one_re]
  have hde : HasDerivAt e (deriv e8EpsteinCandidate 0).re 0 := by
    have h := ((e8EpsteinCandidate_differentiableAt (u := ((0:ℝ):ℂ)) (by norm_num)
      (by norm_num)).hasDerivAt).real_of_complex
    simpa only [Complex.ofReal_zero] using h
  have hdG : HasDerivAt (fun u : ℝ => Real.Gamma (u+1)) (deriv Real.Gamma 1) 0 := by
    have hd : HasDerivAt Real.Gamma (deriv Real.Gamma 1) (0+1) := by
      rw [zero_add]
      exact (Real.differentiableAt_Gamma (fun m h => by
        have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith)).hasDerivAt
    exact hd.comp_add_const 0 1
  have hdP : HasDerivAt (fun u : ℝ => Real.pi^(-u)) (-Real.log Real.pi) 0 := by
    have h := (Real.hasStrictDerivAt_const_rpow Real.pi_pos (-0)).hasDerivAt.comp (0:ℝ)
      (hasDerivAt_neg 0)
    simp only [neg_zero, Real.rpow_zero, one_mul, mul_neg, mul_one] at h
    exact h
  set H : ℝ → ℝ := fun u => Real.Gamma (u+1)*Real.pi^(-u)*e u with hH
  have hdH : HasDerivAt H (-deriv Real.Gamma 1+Real.log Real.pi+(deriv e8EpsteinCandidate 0).re)
      0 := by
    have h := (hdG.mul hdP).mul hde
    convert h using 1
    simp only [Pi.mul_apply, zero_add, Real.Gamma_one, neg_zero, Real.rpow_zero, he0]
    ring
  have hH0 : H 0 = -1 := by
    simp only [hH, zero_add, Real.Gamma_one, neg_zero, Real.rpow_zero, he0]
    ring
  -- the slope limit
  have hs := hdH.tendsto_slope_zero_right
  -- `Re Λ₀(u)` on `(0,1)`
  have hΛ₀ : ∀ u : ℝ, 0 < u → u < 1 →
      (e8ThetaFEPair.Λ₀ (u:ℂ)).re = u⁻¹ • (H (0+u)-H 0)+1/(4-u) := by
    intro u hu0 hu1
    have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have h4 : (4:ℝ)-u ≠ 0 := by linarith
    rw [e8ThetaFEPair.Λ₀_eq]
    change (e8ThetaCompleted (u:ℂ)+(1/(u:ℂ)) • (1:ℂ)+((1:ℂ)/((4:ℝ)-(u:ℂ))) • (1:ℂ)).re = _
    rw [e8ThetaCompleted_eq_candidate_real hu0 (by linarith) (by linarith : u ≠ 1),
      e8CompletedCandidate]
    have hG : Complex.Gamma (u:ℂ) = ((Real.Gamma u : ℝ) : ℂ) := Complex.Gamma_ofReal u
    have hP : (Real.pi : ℂ)^(-(u:ℂ)) = ((Real.pi^(-u) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow Real.pi_pos.le]
      push_cast
      ring_nf
    have hinv : (1/(u:ℂ)) • (1:ℂ) = ((1/u : ℝ) : ℂ) := by
      rw [smul_eq_mul, mul_one]; push_cast; ring
    have hinv4 : ((1:ℂ)/((4:ℝ)-(u:ℂ))) • (1:ℂ) = ((1/(4-u) : ℝ) : ℂ) := by
      rw [smul_eq_mul, mul_one]; push_cast; ring
    rw [hG, hP, hinv, hinv4, Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    have hΓu : Real.Gamma u = Real.Gamma (u+1)/u := by
      rw [Real.Gamma_add_one hu0.ne']
      field_simp
    have hE0 : (e8EpsteinCandidate ((0:ℝ):ℂ)).re = -1 := he0
    simp only [hH, he, zero_add, Real.Gamma_one, neg_zero, Real.rpow_zero, smul_eq_mul]
    rw [hΓu, hE0]
    field_simp
    ring
  -- `Re Λ₀` is continuous at `0`
  have hc : Tendsto (fun u : ℝ => (e8ThetaFEPair.Λ₀ (u:ℂ)).re) (𝓝[>] 0)
      (𝓝 (e8ThetaFEPair.Λ₀ 0).re) := by
    have hcont : Continuous (fun u : ℝ => (e8ThetaFEPair.Λ₀ (u:ℂ)).re) :=
      Complex.continuous_re.comp (e8ThetaFEPair.differentiable_Λ₀.continuous.comp
        Complex.continuous_ofReal)
    have := hcont.tendsto 0
    simp only [Complex.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h4 : Tendsto (fun u : ℝ => 1/(4-u)) (𝓝[>] 0) (𝓝 (1/4)) := by
    have hc4 : ContinuousAt (fun u : ℝ => 1/(4-u)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have := hc4.tendsto
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => (e8ThetaFEPair.Λ₀ (u:ℂ)).re) (𝓝[>] 0)
      (𝓝 ((-deriv Real.Gamma 1+Real.log Real.pi+(deriv e8EpsteinCandidate 0).re)+1/4)) := by
    apply (hs.add h4).congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with u hu
    exact (hΛ₀ u hu.1 hu.2).symm
  exact tendsto_nhds_unique hc hlim

/-- The logarithmic coefficient through the E8 Epstein derivative at `0`:
`C_log = ½ Re E'(0) + ⅛ log A₈`, `E(u) = 2^(-u) 240 ζ(u) ζ(u-3)`. -/
theorem sphereLogCoefficient8_eq_epstein :
    sphereLogCoefficient8 =
      (1/2)*(deriv e8EpsteinCandidate 0).re+(1/8)*Real.log (sphereArea8.real univ) := by
  unfold sphereLogCoefficient8
  rw [e8GaussianLogProfile8_integral_eq, e8ThetaFEPair_Λ₀_zero_re, logGaussianConst_eq_deriv_Gamma]
  ring

theorem e8EpsteinCandidate_hasDerivAt_zero :
    HasDerivAt e8EpsteinCandidate
      (Complex.log 2+240*(deriv riemannZeta 0*(1/120)+(-1/2)*deriv riemannZeta (-3))) 0 := by
  have h2 : HasDerivAt (fun u : ℂ => (2:ℂ)^(-u)) ((2:ℂ)^(-(0:ℂ))*Complex.log 2*(-1)) 0 :=
    (hasDerivAt_neg (0:ℂ)).const_cpow (Or.inl two_ne_zero)
  have hz0 : HasDerivAt riemannZeta (deriv riemannZeta 0) 0 :=
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
  have hz3 : HasDerivAt (fun u : ℂ => riemannZeta (u-3)) (deriv riemannZeta (-3)) 0 := by
    have h := (differentiableAt_riemannZeta (s := (0:ℂ)-3) (by norm_num)).hasDerivAt
    have h' := h.comp_sub_const (0:ℂ) 3
    simpa using h'
  have hprod := h2.mul ((hz0.const_mul 240).mul hz3)
  have hE : e8EpsteinCandidate = fun u : ℂ => (2:ℂ)^(-u)*(240*riemannZeta u*riemannZeta (u-3)) := by
    funext u; rfl
  rw [hE]
  convert hprod using 1
  simp only [Pi.mul_apply, neg_zero, Complex.cpow_zero, one_mul, zero_sub, riemannZeta_zero,
    riemannZeta_neg_three]
  ring

/-- `Re E'(0) = -log π - 120 Re ζ'(-3)`. -/
theorem e8EpsteinCandidate_deriv_zero_re :
    (deriv e8EpsteinCandidate 0).re = -Real.log Real.pi-120*(deriv riemannZeta (-3)).re := by
  rw [e8EpsteinCandidate_hasDerivAt_zero.deriv, deriv_riemannZeta_zero]
  have hl2 : (Complex.log 2).re = Real.log 2 := by
    rw [Complex.log_re]; simp
  have hl2π : (Complex.log (2*(Real.pi:ℂ))).re = Real.log (2*Real.pi) := by
    rw [Complex.log_re]
    congr 1
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  simp only [Complex.add_re, Complex.mul_re, Complex.div_re, Complex.neg_re, hl2, hl2π]
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
  norm_num
  ring

/-- The logarithmic coefficient in closed form:
`C_log = -60 Re ζ'(-3) - ½ log π + ⅛ log A₈ = -60 Re ζ'(-3) + ⅝ log 2 - ⅛ log 105`. -/
theorem sphereLogCoefficient8_eq_zeta :
    sphereLogCoefficient8 = -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105 := by
  rw [sphereLogCoefficient8_eq_epstein, e8EpsteinCandidate_deriv_zero_re, sphereArea8_mass_real]
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, show (32:ℝ) = 2^5 by norm_num, Real.log_pow]
  push_cast
  ring

/-- Universal sharp lower bound for the logarithmic energy on S⁸ with the explicit coefficient
`-60 Re ζ'(-3) + ⅝ log 2 - ⅛ log 105`, under the CKMRV Laplace–sine contract. -/
theorem sphere8_log_lower_explicit (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105-η ≤
        normalizedEnergyLog8 X := by
  rw [← sphereLogCoefficient8_eq_zeta]
  exact sphere8_log_lower_of_laplaceSineData D

#print axioms gamma_sub_inv_integral
#print axioms logGaussianConst_eq_deriv_Gamma
#print axioms e8GaussianLogProfile8_integral_eq
#print axioms riemannZeta_neg_three
#print axioms e8EpsteinCandidate_zero
#print axioms e8ThetaFEPair_Λ₀_zero_re
#print axioms sphereLogCoefficient8_eq_epstein
#print axioms e8EpsteinCandidate_hasDerivAt_zero
#print axioms e8EpsteinCandidate_deriv_zero_re
#print axioms sphereLogCoefficient8_eq_zeta
#print axioms sphere8_log_lower_explicit

end SphericalRiesz
