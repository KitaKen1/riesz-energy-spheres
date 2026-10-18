import Riesz.E8EpsteinStrip8
import Riesz.SphereRieszNegMellin8

/-! The negative-exponent coefficient as the continued E8 Epstein value (stage NEG).

For real `u < 0` the completed E8 theta value `Λ(u)` (the `WeakFEPair` Λ) is the Mellin
integral of `Θ(t) - t⁻⁴` (no subtraction of `1` is needed since `u < 0`): the modified
function `f_modif` of the strong FE pair is Mellin convergent everywhere and differs from
`Θ - t⁻⁴` by `t^(u-1) - t^(u-5)` on `(1,∞)`, whose integral `-1/u - 1/(4-u)` is exactly the
pole correction of `Λ`. For `-1 < u < 0` the continuation through the open upper half plane
identifies `Λ(u)` with `π^(-u) Γ(u) 2^(-u) 240 ζ(u) ζ(u-3)`. Hence for `-2 < s < 0`
`C_s = π^(s/2) A₈^(-s/8)/Γ(s/2) ∫ α^(s/2-1) (Θ(α) - α⁻⁴) dα = A₈^(-s/8) Re ζ_E8(s)`,
the same closed form as for positive exponents. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

/-- The weighted negative-exponent E8 Gaussian profile `α^(s/2-1)(Θ(α) - α⁻⁴)`. -/
def e8GaussianRieszProfileNeg8 (s α : ℝ) : ℝ :=
  α^(s/2-1)*(e8GaussianThetaReal8 α-(α^4)⁻¹)

theorem e8GaussianRieszProfileNeg8_eq_re (s : ℝ) {α : ℝ} (hα : 0 < α) :
    e8GaussianRieszProfileNeg8 s α =
      ((α:ℂ)^(((s/2:ℝ):ℂ)-1) • (e8ThetaImag α-((α:ℂ)^4)⁻¹)).re := by
  have hc : (α:ℂ)^(((s/2:ℝ):ℂ)-1) = ((α^(s/2-1):ℝ):ℂ) := by
    rw [Complex.ofReal_cpow hα.le]
    push_cast
    ring_nf
  rw [hc, smul_eq_mul, Complex.re_ofReal_mul]
  simp only [e8GaussianRieszProfileNeg8, e8GaussianThetaReal8, Complex.sub_re,
    ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re]

theorem e8ThetaFEPair_modified_weighted_ae_neg (u : ℝ) :
    (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹)) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • e8ThetaFEPair.f_modif t +
        (Ioi 1).indicator (fun t : ℝ => ((t^(u-1)-t^(u-5) : ℝ) : ℂ)) t) := by
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
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, Complex.ofReal_sub, hc5]
    ring

/-- For real `u < 0` the completed theta value is the Mellin integral of `Θ(t) - t⁻⁴`. -/
theorem e8ThetaCompleted_eq_integral_neg {u : ℝ} (hu : u < 0) :
    IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹)) (Ioi 0) ∧
    e8ThetaCompleted (u:ℂ) =
      ∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹) := by
  have hmod : IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • e8ThetaFEPair.f_modif t) (Ioi 0) :=
    (e8ThetaFEPair.isStrongFEPair_toStrongFEPair.hasMellin (u:ℂ)).1
  have h1 : IntegrableOn (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have h5 : IntegrableOn (fun t : ℝ => ((t^(u-5) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have hind : IntegrableOn (fun t : ℝ => ((t^(u-1)-t^(u-5) : ℝ) : ℂ)) (Ioi 1) := by
    refine (h1.sub h5).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Complex.ofReal_sub]
  have hl := (hind.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have hint : IntegrableOn
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹)) (Ioi 0) :=
    (hmod.add hl).congr_fun_ae (e8ThetaFEPair_modified_weighted_ae_neg u).symm
  refine ⟨hint, ?_⟩
  have Iind : (∫ t : ℝ in Ioi 0, (Ioi 1).indicator
      (fun t : ℝ => ((t^(u-1)-t^(u-5) : ℝ) : ℂ)) t) = -1/(u:ℂ)-1/(4-(u:ℂ)) := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)),
      integral_complex_ofReal]
    have hr : (∫ t : ℝ in Ioi 1, (t^(u-1)-t^(u-5))) = -1/u-1/(4-u) := by
      rw [integral_sub (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one)
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one),
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      have hu4 : (4:ℝ)-u ≠ 0 := by linarith
      have hu4' : u-4 ≠ 0 := by linarith
      have hu0 : u ≠ 0 := hu.ne
      simp only [Real.one_rpow, show u-1+1 = u by ring, show u-5+1 = u-4 by ring]
      field_simp
      ring
    rw [hr]
    push_cast
    ring
  have hm : (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹)) =
      mellin e8ThetaFEPair.f_modif (u:ℂ)+(-1/(u:ℂ)-1/(4-(u:ℂ))) := by
    rw [integral_congr_ae (e8ThetaFEPair_modified_weighted_ae_neg u),
      integral_add hmod hl, Iind]
    rfl
  rw [hm]
  change mellin e8ThetaFEPair.f_modif (u:ℂ)-(1/(u:ℂ))*1-(1/(4-(u:ℂ)))*1 = _
  ring

theorem e8CompletedCandidate_differentiableAt_of_ne {s : ℂ} (hΓ : ∀ m : ℕ, s ≠ -m)
    (h1 : s ≠ 1) (h4 : s ≠ 4) : DifferentiableAt ℂ e8CompletedCandidate s :=
  ((differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      (Complex.differentiableAt_Gamma s hΓ)).mul (e8EpsteinCandidate_differentiableAt h1 h4)

/-- Continuation to every real point `-1 < u < 0` through the open upper half plane. -/
theorem e8ThetaCompleted_eq_candidate_neg {u : ℝ} (hu : -1 < u) (hu0 : u < 0) :
    e8ThetaCompleted (u:ℂ) = e8CompletedCandidate (u:ℂ) := by
  let U : Set ℂ := {s | 0 < s.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hc : IsPreconnected U := (convex_halfSpace_im_gt (r := 0)).isPreconnected
  have hreal {s : ℂ} (hs : s ∈ U) (c : ℝ) : s ≠ (c : ℂ) := by
    intro h
    have hi : 0 < s.im := hs
    simp [h] at hi
  have hf : AnalyticOnNhd ℂ e8ThetaCompleted U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s hs
    exact (e8ThetaCompleted_differentiableAt (by simpa using hreal hs 0)
      (by simpa using hreal hs 4)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ e8CompletedCandidate U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro s hs
    refine (e8CompletedCandidate_differentiableAt_of_ne (fun m h => ?_)
      (by simpa using hreal hs 1) (by simpa using hreal hs 4)).differentiableWithinAt
    exact hreal hs (-(m:ℝ)) (by rw [h]; push_cast; ring)
  have hfg : e8ThetaCompleted =ᶠ[𝓝 ((5 : ℂ)+Complex.I)] e8CompletedCandidate := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (4 : ℝ) < ((5 : ℂ)+Complex.I).re by norm_num)] with s hs
    exact e8ThetaCompleted_eq_Epstein hs
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc
    (show ((5 : ℂ)+Complex.I) ∈ U by simp [U]) hfg
  have ht : Tendsto (fun ε : ℝ => (u : ℂ)+(ε : ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hε |>.mul_const Complex.I)
  have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne
  have hu4' : (u:ℂ) ≠ 4 := by
    intro h
    have : u = 4 := by exact_mod_cast h
    linarith
  have hu1' : (u:ℂ) ≠ 1 := by
    intro h
    have : u = 1 := by exact_mod_cast h
    linarith
  have hΓu : ∀ m : ℕ, (u:ℂ) ≠ -m := by
    intro m h
    have h' : u = -(m:ℝ) := by exact_mod_cast h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp at h'
      linarith
    · have : (1:ℝ) ≤ m := by exact_mod_cast hm
      linarith
  apply tendsto_nhds_unique_of_eventuallyEq
    ((e8ThetaCompleted_differentiableAt hu0' hu4').continuousAt.tendsto.comp ht)
    ((e8CompletedCandidate_differentiableAt_of_ne hΓu hu1' hu4').continuousAt.tendsto.comp ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply heq
  have hε0 : 0 < ε := hε
  show 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).im
  simpa using hε0

theorem e8GaussianRieszProfileNeg8_integrable {s : ℝ} (hs0 : s < 0) :
    IntegrableOn (e8GaussianRieszProfileNeg8 s) (Ioi 0) := by
  have h := (e8ThetaCompleted_eq_integral_neg (u := s/2) (by linarith)).1
  have hre := h.re
  apply hre.congr_fun _ measurableSet_Ioi
  intro α hα
  exact (e8GaussianRieszProfileNeg8_eq_re s hα).symm

theorem e8GaussianRieszProfileNeg8_integral_eq {s : ℝ} (hs0 : s < 0) :
    (∫ α : ℝ in Ioi 0, e8GaussianRieszProfileNeg8 s α) =
      (e8ThetaCompleted ((s/2:ℝ):ℂ)).re := by
  obtain ⟨hint, heq⟩ := e8ThetaCompleted_eq_integral_neg (u := s/2) (by linarith)
  rw [heq]
  have h := integral_re hint
  change (∫ t : ℝ in Ioi 0, (((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹)).re) =
    (∫ t : ℝ in Ioi 0, ((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • (e8ThetaImag t-((t:ℂ)^4)⁻¹)).re at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α hα
  exact e8GaussianRieszProfileNeg8_eq_re s hα

/-- The conjectured second-order coefficient for `-2 < s < 0`, as a Gaussian profile integral. -/
def sphereRieszCoefficientNeg8 (s : ℝ) : ℝ :=
  (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
    ∫ α : ℝ in Ioi 0, e8GaussianRieszProfileNeg8 s α

/-- For `-2 < s < 0` the coefficient is `A₈^(-s/8) Re ζ_E8(s)`,
`ζ_E8(s) = 2^(-s/2) 240 ζ(s/2) ζ(s/2-3)`. -/
theorem sphereRieszCoefficientNeg8_eq_epstein {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    sphereRieszCoefficientNeg8 s =
      (sphereArea8.real univ)^(-(s/8)) * (e8EpsteinCandidate ((s/2:ℝ):ℂ)).re := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  have hπ : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
  unfold sphereRieszCoefficientNeg8
  rw [e8GaussianRieszProfileNeg8_integral_eq hs0,
    e8ThetaCompleted_eq_candidate_neg (by linarith) (by linarith), e8CompletedCandidate]
  have hG : Complex.Gamma ((s/2:ℝ):ℂ) = ((Real.Gamma (s/2) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (s/2)
  have hP : (Real.pi : ℂ)^(-((s/2:ℝ):ℂ)) = ((Real.pi^(-(s/2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    ring_nf
  rw [hG, hP, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Real.rpow_neg Real.pi_pos.le]
  field_simp

#print axioms e8GaussianRieszProfileNeg8_eq_re
#print axioms e8ThetaFEPair_modified_weighted_ae_neg
#print axioms e8ThetaCompleted_eq_integral_neg
#print axioms e8CompletedCandidate_differentiableAt_of_ne
#print axioms e8ThetaCompleted_eq_candidate_neg
#print axioms e8GaussianRieszProfileNeg8_integrable
#print axioms e8GaussianRieszProfileNeg8_integral_eq
#print axioms sphereRieszCoefficientNeg8_eq_epstein

end SphericalRiesz
