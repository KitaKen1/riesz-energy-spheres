import Riesz.SphereGaussianMonotone8
import Riesz.SphereRieszLowerRpow8
import Riesz.RealFatouTruncation

/-! Reverse-Fatou reduction of the all-exponent sharp upper bound (stage HP, upper half).

For a sequence of configurations the density-scaled Mellin identity
`normalizedEnergyRpow s X = c_s ∫ α^(s/2-1) F_X(α) dα` and reverse Fatou give
`limsup normalizedEnergyRpow s X_k ≤ c_s ∫ g` as soon as `α^(s/2-1) F_k(α)` lies eventually below
`g(α) + ε` at every scale and below one integrable majorant.  For `4 < s < 8` the small-scale part
of the majorant is automatic from a bound on the normalized `s = 4` energy (PSD monotonicity), so
only the pointwise profile and a large-scale decay remain.  The actual sphere background satisfies
the lower asymptotic `N·B(cα) ≥ α⁻⁴ - 3/(α⁴ cα)`, so the E8 profile `Θ(α) - α⁻⁴ - 1` is reached
from an upper bound on the full Gaussian sum alone. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- Reverse Fatou in the integrable-majorant form, by negating the lower-profile Fatou lemma. -/
theorem integral_ge_of_eventual_upper_profile {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g G : α → ℝ} {f : ℕ → α → ℝ} {C : ℝ}
    (hg : Integrable g μ) (hf : ∀ n, Integrable (f n) μ) (hG : Integrable G μ)
    (hG0 : ∀ᵐ x ∂μ, 0 ≤ G x) (hu : ∀ n, ∀ᵐ x ∂μ, f n x ≤ G x)
    (hp : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n x ≤ g x+ε)
    (hC : ∀ n, C ≤ ∫ x, f n x ∂μ) : C ≤ ∫ x, g x ∂μ := by
  have h := integral_le_of_eventual_lower_profile (μ := μ) (g := fun x => -g x) (M := G)
    (f := fun n x => -f n x) (C := -C) hg.neg (fun n => (hf n).neg) hG hG0
    (fun n => (hu n).mono fun x hx => by linarith)
    (hp.mono fun x hx ε hε => (hx ε hε).mono fun n hn => by linarith)
    (fun n => by rw [integral_neg]; linarith [hC n])
  rw [integral_neg] at h
  linarith

theorem polePolynomialGaussian8_ge_quartic (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    8*(v^3*Real.exp (-(2*t*v)))-12*(v^4*Real.exp (-(2*t*v))) ≤ polePolynomialGaussian8 t v := by
  have hp : 8-12*v ≤ (2-v)^3 := by nlinarith [sq_nonneg v, hv.1, hv.2, mul_nonneg (sq_nonneg v) hv.1]
  have hw : 0 ≤ Real.exp (-(2*t*v))*v^3 := mul_nonneg (Real.exp_pos _).le (pow_nonneg hv.1 3)
  unfold polePolynomialGaussian8
  calc 8*(v^3*Real.exp (-(2*t*v)))-12*(v^4*Real.exp (-(2*t*v)))
      = Real.exp (-(2*t*v))*v^3*(8-12*v) := by ring
    _ ≤ Real.exp (-(2*t*v))*v^3*(2-v)^3 := mul_le_mul_of_nonneg_left hp hw

theorem quarticGaussian8_integral {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ in Ioi 0, v^4*Real.exp (-(2*t*v))) = 3/(4*t^5) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 5) (r := 2*t) (by norm_num) (by positivity)
  have h' : (∫ v : ℝ in Ioi 0, v^4*Real.exp (-(2*t*v))) = (1/(2*t))^5*24 := by
    simpa only [show (5:ℝ)-1 = 4 by norm_num, Real.rpow_ofNat,
      show Real.Gamma 5 = 24 by norm_num] using h
  rw [h']
  field_simp
  ring

theorem quarticGaussian8_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => v^4*Real.exp (-(2*t*v))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [quarticGaussian8_integral ht]
  exact (by positivity : (0:ℝ) < 3/(4*t^5)).ne'

/-- Lower asymptotic of the actual sphere Gaussian background. -/
theorem sphereGaussianBackground8_lower {t : ℝ} (ht : 0 < t) :
    (105/32:ℝ)/t^4-(315/32:ℝ)/t^5 ≤ sphereGaussianBackground8 t := by
  set h : ℝ → ℝ := fun v => 8*(v^3*Real.exp (-(2*t*v)))-12*(v^4*Real.exp (-(2*t*v))) with hh
  have hi : IntegrableOn h (Ioi 0) :=
    ((cubicGaussian8_integrable ht).const_mul 8).sub ((quarticGaussian8_integrable ht).const_mul 12)
  have hint : (∫ v in Ioi (0:ℝ), h v) = 3/t^4-9/t^5 := by
    rw [hh, integral_sub ((cubicGaussian8_integrable ht).const_mul 8)
      ((quarticGaussian8_integrable ht).const_mul 12), integral_const_mul, integral_const_mul,
      cubicGaussian8_integral ht, quarticGaussian8_integral ht]
    field_simp
    ring
  have hsplit := integral_inter_add_sdiff (μ := volume) (measurableSet_Ioo (a := (0:ℝ)) (b := 2)) hi
  rw [inter_eq_right.mpr Ioo_subset_Ioi_self] at hsplit
  have htail : (∫ v in Ioi (0:ℝ) \ Ioo 0 2, h v) ≤ 0 := by
    apply setIntegral_nonpos (measurableSet_Ioi.diff measurableSet_Ioo)
    intro v hv
    have hv2 : 2 ≤ v := by
      by_contra hlt
      exact hv.2 ⟨hv.1, lt_of_not_ge hlt⟩
    have he := (Real.exp_pos (-(2*t*v))).le
    have hv0 : 0 ≤ v := by linarith
    simp only [hh]
    have : 8*(v^3*Real.exp (-(2*t*v)))-12*(v^4*Real.exp (-(2*t*v))) =
        -(4*v^3*(3*v-2)*Real.exp (-(2*t*v))) := by ring
    rw [this, neg_nonpos]
    apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hv0 3)) (by linarith)) he
  have hlow : 3/t^4-9/t^5 ≤ ∫ v in Ioo (0:ℝ) 2, h v := by linarith
  have hg : IntegrableOn (polePolynomialGaussian8 t) (Ioo (0:ℝ) 2) :=
    (polePolynomialGaussian8_continuous t).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcmp : (∫ v in Ioo (0:ℝ) 2, h v) ≤ ∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian8 t v :=
    setIntegral_mono_on (hi.mono_set Ioo_subset_Ioi_self) hg measurableSet_Ioo
      (fun v hv => polePolynomialGaussian8_ge_quartic t ⟨hv.1.le, hv.2.le⟩)
  rw [sphereGaussianBackground8_polynomial_set ht.le]
  have hfin : (105/32:ℝ)/t^4-(315/32:ℝ)/t^5 = (35/32:ℝ)*(3/t^4-9/t^5) := by ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_left (hlow.trans hcmp) (by norm_num)

/-- Density-scaled form: `N·B(cα) ≥ α⁻⁴ - 3/(α⁴ cα)`. -/
theorem sphereGaussianBackground8_scaled_lower {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    (α^4)⁻¹-3/(α^4*sphereGaussianScale8 N α) ≤
      (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : sphereArea8.real univ = 32*Real.pi^4/105 := sphereArea8_mass_real
  have hs := sphereGaussianScale8_pos hN hα
  have h4 := sphereGaussianScale8_pow_four hN α
  set c := sphereGaussianScale8 N α with hc
  have hb := mul_le_mul_of_nonneg_left (sphereGaussianBackground8_lower hs) hNR.le
  have he : (N:ℝ)*((105/32:ℝ)/c^4-(315/32:ℝ)/c^5) = (α^4)⁻¹-3/(α^4*c) := by
    rw [show c^5 = c^4*c by ring, h4, hA]
    have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
    ring
  linarith

theorem sphereGaussianCenteredScaled8_le_full {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α)
    (X : Configuration N) :
    sphereGaussianCenteredScaled8 α X ≤
      sphereGaussianFullScaled8 α X-(α^4)⁻¹-1+3/(α^4*sphereGaussianScale8 N α) := by
  have h := sphereGaussianBackground8_scaled_lower hN hα
  unfold sphereGaussianCenteredScaled8 sphereGaussianFullScaled8
  linarith

theorem sphereGaussianScale8_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {α : ℝ}
    (hα : 0 < α) : Tendsto (fun k => sphereGaussianScale8 (N k) α) atTop atTop := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have h1 : Tendsto (fun k => ((N k:ℕ):ℝ)/sphereArea8.real univ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hN).atTop_div_const hA
  have h2 := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp h1
  unfold sphereGaussianScale8
  exact h2.const_mul_atTop (by positivity)

/-- Upper energy transfer: a uniform lower bound on the energies passes to the profile. -/
theorem sphereGaussianSequence_energy_upper_of_profile_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {g G : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ g α+ε)
    {C : ℝ} (hC : ∀ k, C ≤ normalizedEnergyRpow s (X k)) :
    C ≤ (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
      ∫ α : ℝ in Ioi 0, g α := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set c := Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2) with hcdef
  have hc : 0 < c := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < (sphereArea8.real univ)^(-(s/8)) := Real.rpow_pos_of_pos hA _
    positivity
  have hi : ∀ k, C/c ≤ ∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) := by
    intro k
    rw [div_le_iff₀ hc, mul_comm, ← normalizedEnergyRpow_gaussian_mellin hs hs8 (hN k) (X k)]
    exact hC k
  have h := integral_ge_of_eventual_upper_profile
    (μ := volume.restrict (Ioi (0:ℝ))) (g := g) (G := G)
    (f := fun k α => α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) hg
    (fun k => sphereGaussianCenteredScaled8_weighted_integrable_rpow hs hs8 (hN k) (X k)) hG
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hG0 α hα)
    (fun k => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hdom k α hα)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hp α hα)
    hi
  have hh := mul_le_mul_of_nonneg_left h hc.le
  rwa [mul_div_cancel₀ C hc.ne'] at hh

/-- Reverse-Fatou upper bound for a sequence: `limsup normalizedEnergyRpow s X_k ≤ c_s ∫ g`. -/
theorem normalizedEnergyRpow_eventually_le_of_profile {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {g G : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ g α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤
      (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η := by
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have h := sphereGaussianSequence_energy_upper_of_profile_rpow hs hs8 (fun n => hN (φ n))
    (fun n => X (φ n)) hg hG hG0 (fun n => hdom (φ n))
    (fun α hα ε hε => hφt.eventually (hp α hα ε hε))
    (C := (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η) (fun n => (lt_of_not_ge (hbad n)).le)
  linarith

/-- For `4 < s < 8` the small-scale majorant comes from the normalized `s = 4` energy; only the
pointwise profile and a large-scale decay remain. -/
theorem normalizedEnergyRpow_eventually_le_of_profile_four_lt {s : ℝ} (hs4 : 4 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k)) {E₀ : ℝ}
    (hE : ∀ k, normalizedEnergy (X k) ≤ E₀)
    {D : ℝ → ℝ} (hD : IntegrableOn (fun α => α^(s/2-1)*D α) (Ioi 1))
    (hD0 : ∀ α : ℝ, 1 < α → 0 ≤ D α)
    (hdecay : ∀ k, ∀ α : ℝ, 1 < α → sphereGaussianCenteredScaled8 α (X k) ≤ D α)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ g α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤
      (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η := by
  have hs : 0 < s := by linarith
  set a₀ := (8/Real.sqrt 210)*E₀+1 with ha₀
  have hr : 0 < Real.sqrt 210 := by positivity
  have ha₀0 : 0 ≤ a₀ := by
    have h1 := normalizedEnergy_coarse_lower (hN 0) (X 0)
    have h2 := hE 0
    have h3 : -1 ≤ (8/Real.sqrt 210)*E₀ := by
      have : -Real.sqrt 210/8 ≤ E₀ := h1.trans h2
      have h8 : (8/Real.sqrt 210)*(-Real.sqrt 210/8) = -1 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 8/Real.sqrt 210)]
    linarith
  set K₁ := Real.sqrt 2^9 with hK₁
  set K₂ := Real.sqrt 2^9*((2/3)*a₀) with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hsmall : ∀ k, ∀ α : ℝ, 0 < α →
      sphereGaussianCenteredScaled8 α (X k) ≤ K₁+K₂*(α^2)⁻¹ := by
    intro k α hα
    have h := sphereGaussianCenteredScaled8_le_inv_sq (hN k) (X k) hα
    have hEk : (8/Real.sqrt 210)*normalizedEnergy (X k)+1 ≤ a₀ := by
      have := mul_le_mul_of_nonneg_left (hE k) (by positivity : (0:ℝ) ≤ 8/Real.sqrt 210)
      linarith
    have hα2 : 0 < α^2 := by positivity
    have hmono : Real.sqrt 2^9*(1+(2/3)*((8/Real.sqrt 210)*normalizedEnergy (X k)+1)/α^2) ≤
        K₁+K₂*(α^2)⁻¹ := by
      rw [hK₁, hK₂]
      have : (2/3)*((8/Real.sqrt 210)*normalizedEnergy (X k)+1)/α^2 ≤ (2/3)*a₀*(α^2)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hα2.le)
      nlinarith [pow_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) 9]
    linarith
  set G : ℝ → ℝ := fun α => (Iic 1).indicator (fun α => α^(s/2-1)*(K₁+K₂*(α^2)⁻¹)) α+
    (Ioi 1).indicator (fun α => α^(s/2-1)*D α) α with hGdef
  have hsm : IntegrableOn (fun α : ℝ => α^(s/2-1)*(K₁+K₂*(α^2)⁻¹)) (Ioc 0 1) := by
    have h1 : IntegrableOn (fun α : ℝ => α^(s/2-1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    have h2 : IntegrableOn (fun α : ℝ => α^(s/2-3)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    have h3 : IntegrableOn (fun α : ℝ => K₁*α^(s/2-1)+K₂*α^(s/2-3)) (Ioo 0 1) :=
      (h1.const_mul K₁).add (h2.const_mul K₂)
    have h4 : IntegrableOn (fun α : ℝ => α^(s/2-1)*(K₁+K₂*(α^2)⁻¹)) (Ioo 0 1) := by
      apply h3.congr_fun _ measurableSet_Ioo
      intro α hα
      have hα0 : 0 < α := hα.1
      have hr : α^(s/2-3) = α^(s/2-1)*(α^2)⁻¹ := by
        rw [show s/2-3 = (s/2-1)+(-2:ℝ) by ring, Real.rpow_add hα0, Real.rpow_neg hα0.le,
          show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      dsimp only
      rw [hr]
      ring
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h4
  have hGi : IntegrableOn G (Ioi 0) := by
    have hA : IntegrableOn ((Iic 1).indicator (fun α : ℝ => α^(s/2-1)*(K₁+K₂*(α^2)⁻¹))) (Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn, Measure.restrict_restrict
        measurableSet_Iic, show Iic (1:ℝ) ∩ Ioi 0 = Ioc 0 1 by ext; simp [and_comm]]
      exact hsm
    have hB : IntegrableOn ((Ioi 1).indicator (fun α : ℝ => α^(s/2-1)*D α)) (Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn, Measure.restrict_restrict
        measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
      exact hD
    exact hA.add hB
  have hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α := by
    intro α hα
    have hw : 0 ≤ α^(s/2-1) := Real.rpow_nonneg hα.le _
    simp only [hGdef]
    rcases le_or_gt α 1 with h1 | h1
    · rw [indicator_of_mem (show α ∈ Iic 1 from h1), indicator_of_notMem (by simpa using h1),
        add_zero]
      exact mul_nonneg hw (add_nonneg hK₁0 (mul_nonneg hK₂0 (inv_nonneg.mpr (sq_nonneg α))))
    · rw [indicator_of_notMem (by simpa using h1), indicator_of_mem (show α ∈ Ioi 1 from h1),
        zero_add]
      exact mul_nonneg hw (hD0 α h1)
  have hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ G α := by
    intro k α hα
    have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
    simp only [hGdef]
    rcases le_or_gt α 1 with h1 | h1
    · rw [indicator_of_mem (show α ∈ Iic 1 from h1), indicator_of_notMem (by simpa using h1),
        add_zero]
      exact mul_le_mul_of_nonneg_left (hsmall k α hα) hw.le
    · rw [indicator_of_notMem (by simpa using h1), indicator_of_mem (show α ∈ Ioi 1 from h1),
        zero_add]
      exact mul_le_mul_of_nonneg_left (hdecay k α h1) hw.le
  exact normalizedEnergyRpow_eventually_le_of_profile hs hs8 hN X hg hGi hG0 hdom hp

/-- The pointwise E8 upper profile from an upper bound on the full Gaussian sums; the background
correction `3/(α⁴ cα)` vanishes as `N → ∞`. -/
theorem sphereGaussianCenteredScaled8_weighted_profile_upper_eventually (s : ℝ)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled8 α (X k) ≤ e8GaussianThetaReal8 α+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ e8GaussianRieszProfileRpow8 s α+ε := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  set δ := ε/α^(s/2-1)/2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsc := sphereGaussianScale8_tendsto hNt hα
  have hcorr : ∀ᶠ k in atTop, 3/(α^4*sphereGaussianScale8 (N k) α) ≤ δ := by
    have ht : Tendsto (fun k => 3/(α^4*sphereGaussianScale8 (N k) α)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (hsc.const_mul_atTop (by positivity))
    exact ht.eventually (ge_mem_nhds hδ0)
  filter_upwards [hp δ hδ0, hcorr] with k hk hc
  have hb := sphereGaussianCenteredScaled8_le_full (hN k) hα (X k)
  have h2 : δ+δ = ε/α^(s/2-1) := by rw [hδ]; ring
  have hF : sphereGaussianCenteredScaled8 α (X k) ≤
      e8GaussianThetaReal8 α-(α^4)⁻¹-1+ε/α^(s/2-1) := by linarith
  unfold e8GaussianRieszProfileRpow8
  calc α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)
      ≤ α^(s/2-1)*(e8GaussianThetaReal8 α-(α^4)⁻¹-1+ε/α^(s/2-1)) :=
        mul_le_mul_of_nonneg_left hF hw.le
    _ = α^(s/2-1)*(e8GaussianThetaReal8 α-(α^4)⁻¹-1)+ε := by
      field_simp

/-- All-exponent upper reduction with a supplied majorant: the E8 coefficient is reached from an
upper bound on the full Gaussian sums at every scale. -/
theorem sphere8_riesz_upper_of_full_profile {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0)) (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled8 α (X k) ≤ e8GaussianThetaReal8 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η := by
  intro η hη
  have h := normalizedEnergyRpow_eventually_le_of_profile hs hs8 hN X
    (e8GaussianRieszProfileRpow8_integrable hs hs8) hG hG0 hdom
    (fun α hα => sphereGaussianCenteredScaled8_weighted_profile_upper_eventually s hNt hN X hα
      (hp α hα)) η hη
  unfold sphereRieszCoefficient8
  exact h

/-- For `4 < s < 8`: the sharp upper bound for a sequence with bounded normalized `s = 4` energy,
from the pointwise full-Gaussian upper profile and a large-scale decay. -/
theorem sphere8_riesz_upper_of_full_profile_four_lt {s : ℝ} (hs4 : 4 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {E₀ : ℝ} (hE : ∀ k, normalizedEnergy (X k) ≤ E₀)
    {D : ℝ → ℝ} (hD : IntegrableOn (fun α => α^(s/2-1)*D α) (Ioi 1))
    (hD0 : ∀ α : ℝ, 1 < α → 0 ≤ D α)
    (hdecay : ∀ k, ∀ α : ℝ, 1 < α → sphereGaussianCenteredScaled8 α (X k) ≤ D α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled8 α (X k) ≤ e8GaussianThetaReal8 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η := by
  intro η hη
  have h := normalizedEnergyRpow_eventually_le_of_profile_four_lt hs4 hs8 hN X hE hD hD0 hdecay
    (e8GaussianRieszProfileRpow8_integrable (by linarith) hs8)
    (fun α hα => sphereGaussianCenteredScaled8_weighted_profile_upper_eventually s hNt hN X hα
      (hp α hα)) η hη
  unfold sphereRieszCoefficient8
  exact h

end SphericalRiesz
