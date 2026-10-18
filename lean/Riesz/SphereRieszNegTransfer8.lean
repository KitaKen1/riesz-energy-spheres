import Riesz.SphereRieszUpperLtFour8
import Riesz.SphereRieszNegUpper8

/-! Known-answer transfer for negative exponents (stage NEG, second half reduced).

For `-2 < s < 0`, `(E_s - I_s N²)/N^(1+s/8) = K ∫ α^(s/2-1)(F_N(α)+1) dα` with `K < 0` and a
nonnegative integrand. Along a sharp `s = 4` sequence, `α F_k → α P` in `L¹(0,∞)` (G8 profile and
Scheffé), so on every compact window the weight `α^(s/2-2)` transfers the convergence. The large
end is automatic: `F + 1 ≤ √2⁹ (1 + (2/3) max((8/√210) E + 1, 0))` for `α ≥ 1` from the `s = 4`
energy bound `E`, and `∫_R^∞ α^(s/2-1) dα = R^(s/2)/(-s/2) → 0`. Hence configurations attaining
the negative-exponent bound exist as soon as some sharp `s = 4` sequence has a uniformly small
macroscopic end `∫₀^δ α^(s/2-1)(F_k+1) dα`; this is the single remaining obligation. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem weighted_profile_window_bound_neg {s a b α F : ℝ} (ha : 0 < a) (hα : α ∈ Ioc a b) :
    |α^(s/2-1)*(F+1)-e8GaussianRieszProfileNeg8 s α| ≤
      (a^(s/2-2)+b^(s/2-2))*|α*F-e8GaussianRieszProfile8 α| := by
  have hα0 : 0 < α := ha.trans hα.1
  have hw : α^(s/2-1) = α^(s/2-2)*α := by
    rw [show s/2-1 = (s/2-2)+1 by ring, Real.rpow_add_one hα0.ne']
  have he : α^(s/2-1)*(F+1)-e8GaussianRieszProfileNeg8 s α =
      α^(s/2-2)*(α*F-e8GaussianRieszProfile8 α) := by
    rw [e8GaussianRieszProfileNeg8, ← e8GaussianRieszProfileRpow8_four, e8GaussianRieszProfileRpow8,
      show (4:ℝ)/2-1 = 1 by norm_num, Real.rpow_one, hw]
    ring
  rw [he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hα0 _)]
  exact mul_le_mul_of_nonneg_right (rpow_le_add_of_mem_Ioc ha hα) (abs_nonneg _)

/-- General transfer for `-2 < s < 0`: `L¹` convergence of the `s = 4` weighted profiles plus
control of the two ends gives the sharp lower bound for the negative exponent. -/
theorem normalizedEnergyNeg8_eventually_ge_of_L1_tails {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hL1 : Tendsto (fun k => ∫ α in Ioi (0:ℝ),
      |α*sphereGaussianCenteredScaled8 α (X k)-e8GaussianRieszProfile8 α|) atTop (𝓝 0))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ ε)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      sphereRieszCoefficientNeg8 s-η ≤ normalizedEnergyNeg8 s (X k) := by
  intro η hη
  have hK := sphereRieszNegPrefactor8_neg hs hs0
  set c := Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2) with hcdef
  set ε := η/(6*(-c)) with hεdef
  have hε : 0 < ε := div_pos hη (by linarith)
  set P := e8GaussianRieszProfileNeg8 s with hPdef
  have hPi : IntegrableOn P (Ioi 0) := e8GaussianRieszProfileNeg8_integrable hs0
  obtain ⟨n₁, hn₁⟩ := hsmall ε hε
  obtain ⟨n₂, hn₂⟩ := hlarge ε hε
  have hPs := tendsto_setIntegral_Ioc_zero_inv (hPi.mono_set Ioc_subset_Ioi_self)
  have hPl := tendsto_setIntegral_Ioi_nat (hPi.mono_set (Ioi_subset_Ioi zero_le_one))
  obtain ⟨n, hn12, hsP, hlP⟩ := ((eventually_ge_atTop (max n₁ n₂)).and
    ((Metric.tendsto_nhds.mp hPs ε hε).and (Metric.tendsto_nhds.mp hPl ε hε))).exists
  rw [Real.dist_eq, sub_zero] at hsP hlP
  set a : ℝ := 1/((n:ℝ)+1) with hadef
  set b : ℝ := (n:ℝ)+1 with hbdef
  have ha : 0 < a := by positivity
  have hb1 : 1 ≤ b := by
    rw [hbdef]
    have := (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    linarith
  have ha1 : a ≤ 1 := by
    rw [hadef, div_le_one (by positivity)]
    have := (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    linarith [hb1]
  have hab : a ≤ b := ha1.trans hb1
  set C := a^(s/2-2)+b^(s/2-2) with hCdef
  have hC : 0 ≤ C := by positivity
  have hsub1 : a ≤ 1/((n₁:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (n₁:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn12
    linarith
  have hsub2 : (n₂:ℝ)+1 ≤ b := by
    have : (n₂:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn12
    linarith
  have hL1' : ∀ᶠ k in atTop, C*∫ α in Ioi (0:ℝ),
      |α*sphereGaussianCenteredScaled8 α (X k)-e8GaussianRieszProfile8 α| ≤ ε := by
    have ht := hL1.const_mul C
    rw [mul_zero] at ht
    exact ht.eventually (ge_mem_nhds hε)
  filter_upwards [hn₁, hn₂, hL1'] with k hk1 hk2 hk3
  set F : ℝ → ℝ := fun α => sphereGaussianCenteredScaled8 α (X k) with hFdef
  set G : ℝ → ℝ := fun α => α^(s/2-1)*(F α+1) with hGdef
  have hGi : IntegrableOn G (Ioi 0) :=
    sphereGaussianCenteredScaled8_neg_integrable hs hs0 (hN k) (X k)
  have hG0 : ∀ α ∈ Ioi (0:ℝ), 0 ≤ G α := fun α hα =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hα) _)
      (sphereGaussianCenteredScaled8_add_one_nonneg (hN k) (le_of_lt hα) (X k))
  -- the two ends
  have hend1 : ∫ α in Ioc 0 a, G α ≤ ε := by
    have h2 : ∫ α in Ioc 0 a, G α ≤ ∫ α in Ioc 0 (1/((n₁:ℝ)+1)), G α := by
      apply setIntegral_mono_set (hGi.mono_set Ioc_subset_Ioi_self)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
        exact hG0 α hα.1
      · exact (Ioc_subset_Ioc_right hsub1).eventuallyLE
    linarith
  have hend2 : ∫ α in Ioi b, G α ≤ ε := by
    have h2 : ∫ α in Ioi b, G α ≤ ∫ α in Ioi ((n₂:ℝ)+1), G α := by
      apply setIntegral_mono_set (hGi.mono_set (Ioi_subset_Ioi (by positivity)))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact hG0 α (lt_of_lt_of_le (by positivity : (0:ℝ) < (n₂:ℝ)+1) (le_of_lt hα))
      · exact (Ioi_subset_Ioi hsub2).eventuallyLE
    linarith
  -- the window
  have hwin : (∫ α in Ioc a b, G α) ≤ (∫ α in Ioc a b, P α)+ε := by
    have hdi : IntegrableOn (fun α => |α*F α-e8GaussianRieszProfile8 α|) (Ioi 0) :=
      ((sphereGaussianCenteredScaled8_weighted_integrable (hN k) (X k)).sub
        e8GaussianRieszProfile8_integrable).abs
    have h1 : ∫ α in Ioc a b, (G α-P α) ≤
        ∫ α in Ioc a b, C*|α*F α-e8GaussianRieszProfile8 α| := by
      apply setIntegral_mono_on (IntegrableOn.mono_set (hGi.sub hPi) (Ioc_subset_Ioi_self.trans
        (Ioi_subset_Ioi ha.le))) (IntegrableOn.mono_set (hdi.const_mul C)
        (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le))) measurableSet_Ioc
      intro α hα
      exact (le_abs_self _).trans (weighted_profile_window_bound_neg ha hα)
    have h2 : ∫ α in Ioc a b, C*|α*F α-e8GaussianRieszProfile8 α| ≤
        C*∫ α in Ioi (0:ℝ), |α*F α-e8GaussianRieszProfile8 α| := by
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ hC
      apply setIntegral_mono_set hdi
      · exact Eventually.of_forall fun α => abs_nonneg _
      · exact (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)).eventuallyLE
    have h3 : ∫ α in Ioc a b, (G α-P α) = (∫ α in Ioc a b, G α)-∫ α in Ioc a b, P α :=
      integral_sub (hGi.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)))
        (hPi.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)))
    linarith
  have hsplitG := setIntegral_Ioi_zero_split hGi ha hab
  have hsplitP := setIntegral_Ioi_zero_split hPi ha hab
  have htot : (∫ α in Ioi 0, G α) ≤ (∫ α in Ioi 0, P α)+5*ε := by
    have h4 := (le_abs_self (∫ α in Ioc 0 a, P α))
    have h5 := (le_abs_self (∫ α in Ioi b, P α))
    have h6 := neg_abs_le (∫ α in Ioc 0 a, P α)
    have h7 := neg_abs_le (∫ α in Ioi b, P α)
    linarith
  rw [normalizedEnergyNeg8_gaussian_mellin hs hs0 (hN k) (X k)]
  unfold sphereRieszCoefficientNeg8
  rw [← hcdef]
  have h8 := mul_le_mul_of_nonpos_left htot hK.le
  have hc0 : c ≠ 0 := hK.ne
  have h9 : c*(5*ε) = -(5/6)*η := by
    rw [hεdef]
    field_simp
  have h10 : c*((∫ α in Ioi 0, P α)+5*ε) = c*(∫ α in Ioi 0, P α)+c*(5*ε) := by ring
  change c*(∫ α in Ioi 0, P α)-η ≤ c*(∫ α in Ioi 0, G α)
  linarith

/-- The large end for negative exponents is controlled by an upper bound on the normalized
`s = 4` energy. -/
theorem neg_large_tail_of_energy_bound {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {N : ℕ → ℕ}
    (hN : ∀ k, 0 < N k)
    (X : ∀ k, Configuration (N k)) {E : ℝ}
    (hE : ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ E) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ ε := by
  intro ε hε
  set K := Real.sqrt 2^9*(1+(2/3)*max ((8/Real.sqrt 210)*E+1) 0) with hKdef
  have hK0 : 0 < K := by
    have : 0 ≤ max ((8/Real.sqrt 210)*E+1) 0 := le_max_right _ _
    positivity
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)^(s/2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (y := -(s/2)) (by linarith)).comp h1
    simp only [neg_neg] at h2
    exact h2
  have hδ : 0 < ε*(-(s/2))/K := by
    apply div_pos _ hK0
    exact mul_pos hε (by linarith)
  obtain ⟨n₀, hn₀⟩ := (ht.eventually (ge_mem_nhds hδ)).exists
  refine ⟨n₀, ?_⟩
  filter_upwards [hE] with k hk
  have hc : (0:ℝ) < (n₀:ℝ)+1 := by positivity
  have hw : IntegrableOn (fun α : ℝ => α^(s/2-1)) (Ioi ((n₀:ℝ)+1)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  have hGi : IntegrableOn (fun α : ℝ => α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1))
      (Ioi ((n₀:ℝ)+1)) :=
    (sphereGaussianCenteredScaled8_neg_integrable hs hs0 (hN k) (X k)).mono_set
      (Ioi_subset_Ioi hc.le)
  have hpt : ∀ α ∈ Ioi ((n₀:ℝ)+1),
      α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ K*α^(s/2-1) := by
    intro α hα
    have hα1 : 1 ≤ α := by
      have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
      have : (1:ℝ) ≤ (n₀:ℝ)+1 := by linarith
      exact this.trans (le_of_lt hα)
    have hα0 : 0 < α := by linarith
    have hb := sphereGaussianCenteredScaled8_le_inv_sq (hN k) (X k) hα0
    have hα2 : 1 ≤ α^2 := one_le_pow₀ hα1
    have hq : (2/3)*((8/Real.sqrt 210)*normalizedEnergy (X k)+1)/α^2 ≤
        (2/3)*max ((8/Real.sqrt 210)*E+1) 0 := by
      have h1 : (8/Real.sqrt 210)*normalizedEnergy (X k)+1 ≤ max ((8/Real.sqrt 210)*E+1) 0 := by
        have : (8/Real.sqrt 210)*normalizedEnergy (X k) ≤ (8/Real.sqrt 210)*E :=
          mul_le_mul_of_nonneg_left hk (by positivity)
        exact (by linarith : (8/Real.sqrt 210)*normalizedEnergy (X k)+1 ≤ (8/Real.sqrt 210)*E+1).trans
          (le_max_left _ _)
      have hm0 : 0 ≤ max ((8/Real.sqrt 210)*E+1) 0 := le_max_right _ _
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hF : sphereGaussianCenteredScaled8 α (X k)+1 ≤ K := by
      rw [hKdef]
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hw0 : 0 ≤ α^(s/2-1) := Real.rpow_nonneg hα0.le _
    calc α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ α^(s/2-1)*K :=
          mul_le_mul_of_nonneg_left hF hw0
      _ = K*α^(s/2-1) := by ring
  calc ∫ α in Ioi ((n₀:ℝ)+1), α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1)
      ≤ ∫ α in Ioi ((n₀:ℝ)+1), K*α^(s/2-1) :=
        setIntegral_mono_on hGi (hw.const_mul K) measurableSet_Ioi hpt
    _ = K*(-((n₀:ℝ)+1)^(s/2-1+1)/(s/2-1+1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hc]
    _ = K*(((n₀:ℝ)+1)^(s/2)/(-(s/2))) := by
        rw [show s/2-1+1 = s/2 by ring]
        ring
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        have := mul_le_mul_of_nonneg_left hn₀ hK0.le
        rw [mul_div_assoc', mul_div_cancel_left₀ _ hK0.ne'] at this
        linarith

/-- Negative-exponent sharp lower bound along any sharp `s = 4` sequence with a uniformly small
macroscopic end, under the CKMRV Laplace–sine contract. -/
theorem sphere8_riesz_neg_lower_of_sharp_sequence (D : E8LaplaceSineData8) {s : ℝ}
    (hs : -2 < s) (hs0 : s < 0) {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (hNt : Tendsto N atTop atTop)
    (X : ∀ k, Configuration (N k))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      sphereRieszCoefficientNeg8 s-η ≤ normalizedEnergyNeg8 s (X k) := by
  have hp : SphereGaussianSharpProfileLower8 :=
    sphereGaussianSharpProfileLower8_of_schwartz_input
      (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩))
  have hL1 := sphereGaussianCenteredScaled8_L1_tendsto_of_sharp hN X (hp N hNt hN X) hE
  exact normalizedEnergyNeg8_eventually_ge_of_L1_tails hs hs0 hN X hL1 hsmall
    (neg_large_tail_of_energy_bound hs hs0 hN X (hE 1 one_pos))

#print axioms weighted_profile_window_bound_neg
#print axioms normalizedEnergyNeg8_eventually_ge_of_L1_tails
#print axioms neg_large_tail_of_energy_bound
#print axioms sphere8_riesz_neg_lower_of_sharp_sequence

end SphericalRiesz
