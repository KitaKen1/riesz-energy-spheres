import Riesz.E8SmoothValue
import Riesz.SphereRieszLowerRpow8

/-! The all-exponent coefficient as the analytically continued E8 Epstein value (stage HP).

For real `0 < u < 4` the completed E8 theta function (the `WeakFEPair` Λ, already used at `u = 2`)
equals the Mellin integral of the regularized theta `Θ(t) - 1 - t⁻⁴` along the strip, and for
`u ≠ 1` it equals the explicit candidate `π^(-u) Γ(u) 2^(-u) 240 ζ(u) ζ(u-3)` by the same
upper-quadrant continuation as at `u = 2`. Hence for `0 < s < 8`, `s ≠ 2`, the sharp lower-bound
constant is `C_s = A₈^(-s/8) * Re(2^(-s/2) 240 ζ(s/2) ζ(s/2-3))`, the Brauchart–Hardin–Saff
second-order coefficient with the E8 Epstein zeta value. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem e8ThetaFEPair_modified_weighted_ae_rpow (u : ℝ) :
    (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • e8ThetaFEPair.f_modif t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t +
        (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t +
        (Ioi 1).indicator (fun t : ℝ => ((t^(u-5) : ℝ) : ℂ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  have hc : (t:ℂ)^((u:ℂ)-1) = ((t^(u-1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht0.le]
    push_cast
    ring_nf
  have hc5 : ((t^(u-5) : ℝ) : ℂ) = ((t^(u-1) : ℝ) : ℂ) * ((t:ℂ)^4)⁻¹ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [show u-5 = (u-1)-(4:ℝ) by ring, Real.rpow_sub ht0, Real.rpow_ofNat, div_eq_mul_inv]
  have h4 : ((t^(-(4:ℝ)) : ℝ) : ℂ) = ((t:ℂ)^4)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_ofNat, Complex.ofReal_inv, Complex.ofReal_pow]
  simp only [WeakFEPair.f_modif, e8ThetaFEPair, Pi.add_apply, hc, smul_eq_mul]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hA : t ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    have hB : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, hsmall⟩
    simp only [indicator_of_notMem hA, indicator_of_mem hB, h4]
    unfold e8ThetaRegularized e8ThetaTail
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, hc5]
    unfold e8ThetaRegularized e8ThetaTail
    ring

/-- In the strip, the completed theta value is the Mellin integral of the regularized theta. -/
theorem e8ThetaCompleted_eq_integral_strip {u : ℝ} (hu0 : 0 < u) (hu4 : u < 4) :
    e8ThetaCompleted (u:ℂ) =
      ∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t := by
  have hreg : IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t) (Ioi 0) :=
    e8ThetaRegularized_mellinConvergent (s := (u:ℂ)) (by simpa using hu0) (by simpa using hu4)
  have hsmall : IntegrableOn (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)).ofReal
  have hlarge : IntegrableOn (fun t : ℝ => ((t^(u-5) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have hs := (hsmall.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi 0)
  have hl := (hlarge.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have Ismall : (∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t) =
      1/(u:ℂ) := by
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < u-1))]
    have hu : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hu0.ne', sub_zero]
    push_cast
    field_simp
  have Ilarge : (∫ t : ℝ in Ioi 0, (Ioi 1).indicator (fun t : ℝ => ((t^(u-5) : ℝ) : ℂ)) t) =
      1/(4-(u:ℂ)) := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)),
      integral_complex_ofReal, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    have h4 : (u:ℂ)-4 ≠ 0 := by
      have : u-4 ≠ 0 := by linarith
      exact_mod_cast this
    have h4' : (4:ℂ)-(u:ℂ) ≠ 0 := by
      intro h; apply h4; linear_combination -h
    simp only [Real.one_rpow, show u-5+1 = u-4 by ring]
    push_cast
    field_simp
    ring
  have hm : mellin e8ThetaFEPair.f_modif (u:ℂ) =
      (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t) + 1/(u:ℂ) + 1/(4-(u:ℂ)) := by
    unfold mellin
    rw [integral_congr_ae (e8ThetaFEPair_modified_weighted_ae_rpow u)]
    have e1 : (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t +
          (Ioi 1).indicator (fun t : ℝ => ((t^(u-5) : ℝ) : ℂ)) t)) =
        (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t)) +
        ∫ t : ℝ in Ioi 0, (Ioi 1).indicator (fun t : ℝ => ((t^(u-5) : ℝ) : ℂ)) t :=
      integral_add (hreg.add hs) hl
    have e2 : (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t)) =
        (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • e8ThetaRegularized t) +
        ∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t :=
      integral_add hreg hs
    rw [e1, e2, Ismall, Ilarge]
  change mellin e8ThetaFEPair.f_modif (u:ℂ) - (1/(u:ℂ))*1 - (1/(4-(u:ℂ)))*1 = _
  rw [hm]
  ring

/-- Continuation to every real point `0 < u < 4`, `u ≠ 1`. -/
theorem e8ThetaCompleted_eq_candidate_real {u : ℝ} (hu0 : 0 < u) (hu4 : u < 4) (hu1 : u ≠ 1) :
    e8ThetaCompleted (u:ℂ) = e8CompletedCandidate (u:ℂ) := by
  let U : Set ℂ := {s | 0 < s.re ∧ 0 < s.im}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (r := 0)).inter (convex_halfSpace_im_gt (r := 0))).isPreconnected
  have hreal {s : ℂ} (hs : s ∈ U) (c : ℝ) : s ≠ (c : ℂ) := by
    intro h
    have hi := hs.2
    simp [h] at hi
  have hf : AnalyticOnNhd ℂ e8ThetaCompleted U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s hs
    exact (e8ThetaCompleted_differentiableAt (by simpa using hreal hs 0)
      (by simpa using hreal hs 4)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ e8CompletedCandidate U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s hs
    exact (e8CompletedCandidate_differentiableAt hs.1 (by simpa using hreal hs 1)
      (by simpa using hreal hs 4)).differentiableWithinAt
  have hfg : e8ThetaCompleted =ᶠ[𝓝 ((5 : ℂ)+Complex.I)] e8CompletedCandidate := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (4 : ℝ) < ((5 : ℂ)+Complex.I).re by norm_num)] with s hs
    exact e8ThetaCompleted_eq_Epstein hs
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc
    (show ((5 : ℂ)+Complex.I) ∈ U by norm_num [U]) hfg
  have ht : Tendsto (fun ε : ℝ => (u : ℂ)+(ε : ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hε |>.mul_const Complex.I)
  have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have hu4' : (u:ℂ) ≠ 4 := by
    intro h
    have : u = 4 := by exact_mod_cast h
    linarith
  have hu1' : (u:ℂ) ≠ 1 := by exact_mod_cast hu1
  apply tendsto_nhds_unique_of_eventuallyEq
    ((e8ThetaCompleted_differentiableAt hu0' hu4').continuousAt.tendsto.comp ht)
    ((e8CompletedCandidate_differentiableAt (by simpa using hu0) hu1' hu4').continuousAt.tendsto.comp ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply heq
  have hε0 : 0 < ε := hε
  show 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).re ∧ 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).im
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
  exact ⟨hu0, hε0⟩

/-- The profile integral is the real part of the completed theta value in the strip. -/
theorem e8GaussianRieszProfileRpow8_integral_eq {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    (∫ α : ℝ in Ioi 0, e8GaussianRieszProfileRpow8 s α) = (e8ThetaCompleted ((s/2:ℝ):ℂ)).re := by
  rw [e8ThetaCompleted_eq_integral_strip (by linarith) (by linarith)]
  have hint : IntegrableOn (fun t : ℝ => ((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • e8ThetaRegularized t) (Ioi 0) :=
    e8ThetaRegularized_mellinConvergent (s := ((s/2:ℝ):ℂ)) (by simp; linarith) (by simp; linarith)
  have h := integral_re hint
  change (∫ t : ℝ in Ioi 0, (((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • e8ThetaRegularized t).re) =
    (∫ t : ℝ in Ioi 0, ((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • e8ThetaRegularized t).re at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α hα
  exact e8GaussianRieszProfileRpow8_eq_re s hα

/-- The all-exponent sharp coefficient is the E8 Epstein value `A₈^(-s/8) ζ_E8(s)`,
`ζ_E8(s) = 2^(-s/2) 240 ζ(s/2) ζ(s/2-3)` (continued), for `0 < s < 8`, `s ≠ 2`. -/
theorem sphereRieszCoefficient8_eq_epstein {s : ℝ} (hs : 0 < s) (hs8 : s < 8) (hs2 : s ≠ 2) :
    sphereRieszCoefficient8 s =
      (sphereArea8.real univ)^(-(s/8)) * (e8EpsteinCandidate ((s/2:ℝ):ℂ)).re := by
  have hu0 : 0 < s/2 := by linarith
  have hu1 : s/2 ≠ 1 := by intro h; apply hs2; linarith
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos hu0
  have hπ : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
  unfold sphereRieszCoefficient8
  rw [e8GaussianRieszProfileRpow8_integral_eq hs hs8,
    e8ThetaCompleted_eq_candidate_real hu0 (by linarith) hu1, e8CompletedCandidate]
  have hG : Complex.Gamma ((s/2:ℝ):ℂ) = ((Real.Gamma (s/2) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (s/2)
  have hP : (Real.pi : ℂ)^(-((s/2:ℝ):ℂ)) = ((Real.pi^(-(s/2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    ring_nf
  rw [hG, hP, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Real.rpow_neg Real.pi_pos.le]
  field_simp

/-- All-exponent sharp lower bound with the explicit E8 Epstein coefficient (`0 < s < 8`,
`s ≠ 2`), under the CKMRV Laplace–sine contract. -/
theorem sphere8_riesz_sharp_lower_epstein_of_laplaceSineData (D : E8LaplaceSineData8)
    {s : ℝ} (hs : 0 < s) (hs8 : s < 8) (hs2 : s ≠ 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (sphereArea8.real univ)^(-(s/8)) * (e8EpsteinCandidate ((s/2:ℝ):ℂ)).re-η ≤
        normalizedEnergyRpow s X := by
  rw [← sphereRieszCoefficient8_eq_epstein hs hs8 hs2]
  exact sphere8_riesz_sharp_lower_of_laplaceSineData D hs hs8

#print axioms sphere8_riesz_sharp_lower_epstein_of_laplaceSineData
#print axioms e8ThetaFEPair_modified_weighted_ae_rpow
#print axioms e8ThetaCompleted_eq_integral_strip
#print axioms e8ThetaCompleted_eq_candidate_real
#print axioms e8GaussianRieszProfileRpow8_integral_eq
#print axioms sphereRieszCoefficient8_eq_epstein

end SphericalRiesz
