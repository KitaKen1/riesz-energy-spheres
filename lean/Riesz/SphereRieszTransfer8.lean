import Riesz.SphereRieszUpperRpow8

/-! Transfer of the sharp `s = 4` asymptotics to every exponent (stage HP, upper half).

Known-answer shortcut: along a sequence whose normalized `s = 4` energy tends to the sharp
coefficient, the sharp Gaussian lower profile (the G8 input) forces the weighted Gaussian
profiles `α·F_k(α)` to converge to the E8 profile in `L¹(0, ∞)` (a Scheffé-type argument: the
negative parts vanish pointwise and are dominated; the integrals converge).  On every compact
window `[a, b] ⊂ (0, ∞)` the Mellin weight `α^(s/2-2)` is bounded, so only the two ends remain.
For `4 < s < 8` the small-scale end is automatic from PSD monotonicity; for `0 < s < 4` the
large-scale end is automatic because the off-diagonal Gaussian sum is antitone in the scale.
No pointwise analysis of the patch lattice sums is needed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- Scheffé-type lemma with one-sided pointwise information. -/
theorem tendsto_integral_abs_sub_of_eventual_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g m : α → ℝ}
    (hg : Integrable g μ) (hf : ∀ n, Integrable (f n) μ) (hm : Integrable m μ)
    (hl : ∀ n, ∀ᵐ x ∂μ, -m x ≤ f n x)
    (hp : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, g x-ε ≤ f n x)
    (hI : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ x, f n x ∂μ ≤ (∫ x, g x ∂μ)+ε) :
    Tendsto (fun n => ∫ x, |f n x-g x| ∂μ) atTop (𝓝 0) := by
  set h : ℕ → α → ℝ := fun n x => max (g x-f n x) 0 with hh
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ |g x|+|m x| := by
    intro n
    filter_upwards [hl n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · linarith [le_abs_self (g x), le_abs_self (m x)]
    · positivity
  have hmeas : ∀ n, AEStronglyMeasurable (h n) μ := fun n =>
    (hg.sub (hf n)).aestronglyMeasurable.sup aestronglyMeasurable_const
  have hhi : ∀ n, Integrable (h n) μ := fun n => (hg.abs.add hm.abs).mono' (hmeas n) (hbound n)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0) := by
    filter_upwards [hp] with x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hx (ε/2) (half_pos hε))
    refine ⟨N₀, fun n hn => ?_⟩
    have h1 := hN₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
    have h2 : h n x ≤ ε/2 := max_le (by linarith) (by linarith)
    linarith
  have hD := tendsto_integral_of_dominated_convergence (fun x => |g x|+|m x|) hmeas
    (hg.abs.add hm.abs) hbound hlim
  rw [integral_zero] at hD
  have hab : ∀ n, ∫ x, |f n x-g x| ∂μ = ((∫ x, f n x ∂μ)-∫ x, g x ∂μ)+2*∫ x, h n x ∂μ := by
    intro n
    have hpt : (fun x => |f n x-g x|) = fun x => (f n x-g x)+2*h n x := by
      funext x
      simp only [hh]
      rcases le_total (f n x) (g x) with hle | hle
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        ring
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
        ring
    rw [hpt]
    have e1 : ∫ x, (f n x-g x+2*h n x) ∂μ = (∫ x, (f n x-g x) ∂μ)+∫ x, 2*h n x ∂μ :=
      integral_add ((hf n).sub hg) ((hhi n).const_mul 2)
    have e2 : ∫ x, (f n x-g x) ∂μ = (∫ x, f n x ∂μ)-∫ x, g x ∂μ := integral_sub (hf n) hg
    rw [e1, e2, integral_const_mul]
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => ?_, fun a ha => ?_⟩
  · exact ha.trans_le (integral_nonneg fun x => abs_nonneg _)
  · filter_upwards [hI (a/3) (by positivity), hD.eventually (gt_mem_nhds (by positivity : (0:ℝ) < a/6))]
      with n h1 h2
    rw [hab n]
    linarith

/-- Sharp `s = 4` sequences under the G8 lower profile: `α·F_k → α·P` in `L¹(0, ∞)`. -/
theorem sphereGaussianCenteredScaled8_L1_tendsto_of_sharp
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε) :
    Tendsto (fun k => ∫ α in Ioi (0:ℝ),
      |α*sphereGaussianCenteredScaled8 α (X k)-e8GaussianRieszProfile8 α|) atTop (𝓝 0) := by
  apply tendsto_integral_abs_sub_of_eventual_lower (μ := volume.restrict (Ioi (0:ℝ)))
    (m := sphereGaussianMajorant8 4)
    e8GaussianRieszProfile8_integrable
    (fun k => sphereGaussianCenteredScaled8_weighted_integrable (hN k) (X k))
    (sphereGaussianMajorant8_integrable (by norm_num) (by norm_num))
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact sphereGaussianCenteredScaled8_weighted_lower (hN k) hα (X k)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact sphereGaussianCenteredScaled8_weighted_profile_eventually hN X hα (hp α hα)
  · intro ε hε
    have hc : (0:ℝ) < Real.sqrt 210/8 := by positivity
    filter_upwards [hE (ε*(Real.sqrt 210/8)) (by positivity)] with k hk
    have h1 := normalizedEnergy_gaussian_mellin_four (hN k) (X k)
    rw [sphereGaussianArea8_coarse_coefficient] at h1
    have h2 := predictedCoefficient_eq_gaussian_profile_factor
    rw [sphereGaussianArea8_coarse_coefficient] at h2
    rw [e8GaussianRieszProfile8_integral]
    have h3 : Real.sqrt 210/8*(∫ α : ℝ in Ioi 0, α*sphereGaussianCenteredScaled8 α (X k)) ≤
        Real.sqrt 210/8*(-5/6+ε) := by
      rw [← h1]
      nlinarith
    exact le_of_mul_le_mul_left h3 hc

theorem setIntegral_Ioi_zero_split {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ α in Ioi 0, f α = (∫ α in Ioc 0 a, f α)+(∫ α in Ioc a b, f α)+∫ α in Ioi b, f α := by
  have h1 : Ioi (0:ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have h2 : Ioi a = Ioc a b ∪ Ioi b := (Ioc_union_Ioi_eq_Ioi hab).symm
  have hfa : IntegrableOn f (Ioi a) := hf.mono_set (Ioi_subset_Ioi ha.le)
  have e1 : ∫ α in Ioi 0, f α = (∫ α in Ioc 0 a, f α)+∫ α in Ioi a, f α := by
    conv_lhs => rw [h1]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) hfa
  have e2 : ∫ α in Ioi a, f α = (∫ α in Ioc a b, f α)+∫ α in Ioi b, f α := by
    conv_lhs => rw [h2]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hfa.mono_set Ioc_subset_Ioi_self) (hfa.mono_set (Ioi_subset_Ioi hab))
  rw [e1, e2]
  ring

theorem tendsto_setIntegral_Ioc_zero_inv {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc 0 1)) :
    Tendsto (fun n : ℕ => ∫ α in Ioc 0 (1/((n:ℝ)+1)), g α) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => Ioc (0:ℝ) (1/((n:ℝ)+1))) := by
    intro m n hmn x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := g)
    (fun n : ℕ => measurableSet_Ioc) hanti ⟨0, by simpa using hg⟩
  have hempty : (⋂ n : ℕ, Ioc (0:ℝ) (1/((n:ℝ)+1))) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_empty_iff_false, iff_false, not_forall]
    by_cases hx : 0 < x
    · obtain ⟨n, hn⟩ := exists_nat_gt (1/x)
      refine ⟨n, fun h => ?_⟩
      have h1 : 1/((n:ℝ)+1) < x := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hx] at hn
        nlinarith
      linarith [h.2]
    · exact ⟨0, fun h => hx h.1⟩
  rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h

theorem tendsto_setIntegral_Ioi_nat {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 1)) :
    Tendsto (fun n : ℕ => ∫ α in Ioi ((n:ℝ)+1), g α) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => Ioi ((n:ℝ)+1)) := by
    intro m n hmn x hx
    have hx' : (n:ℝ)+1 < x := hx
    show (m:ℝ)+1 < x
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := g)
    (fun n : ℕ => measurableSet_Ioi) hanti ⟨0, by simpa using hg⟩
  have hempty : (⋂ n : ℕ, Ioi ((n:ℝ)+1)) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, by linarith⟩
  rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h

theorem rpow_le_add_of_mem_Ioc {e a b α : ℝ} (ha : 0 < a) (hα : α ∈ Ioc a b) :
    α^e ≤ a^e+b^e := by
  have hα0 : 0 < α := ha.trans hα.1
  rcases le_or_gt 0 e with he | he
  · have := Real.rpow_le_rpow hα0.le hα.2 he
    linarith [Real.rpow_nonneg ha.le e]
  · have := Real.rpow_le_rpow_of_nonpos ha hα.1.le he.le
    linarith [Real.rpow_nonneg (hα0.le.trans hα.2) e]

/-- The Mellin weight on a compact window, relative to the `s = 4` weight. -/
theorem weighted_profile_window_bound {s a b α F : ℝ} (ha : 0 < a) (hα : α ∈ Ioc a b) :
    |α^(s/2-1)*F-e8GaussianRieszProfileRpow8 s α| ≤
      (a^(s/2-2)+b^(s/2-2))*|α*F-e8GaussianRieszProfile8 α| := by
  have hα0 : 0 < α := ha.trans hα.1
  have hw : α^(s/2-1) = α^(s/2-2)*α := by
    rw [show s/2-1 = (s/2-2)+1 by ring, Real.rpow_add_one hα0.ne']
  have he : α^(s/2-1)*F-e8GaussianRieszProfileRpow8 s α =
      α^(s/2-2)*(α*F-e8GaussianRieszProfile8 α) := by
    unfold e8GaussianRieszProfileRpow8 e8GaussianRieszProfile8
    rw [hw]
    ring
  rw [he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hα0 _)]
  exact mul_le_mul_of_nonneg_right (rpow_le_add_of_mem_Ioc ha hα) (abs_nonneg _)

/-- General transfer: `L¹` convergence of the `s = 4` weighted profiles plus control of the two
ends gives the sharp upper bound for exponent `s`. -/
theorem normalizedEnergyRpow_eventually_le_of_L1_tails {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hL1 : Tendsto (fun k => ∫ α in Ioi (0:ℝ),
      |α*sphereGaussianCenteredScaled8 α (X k)-e8GaussianRieszProfile8 α|) atTop (𝓝 0))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η := by
  intro η hη
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set c := Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2) with hcdef
  have hc : 0 < c := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < (sphereArea8.real univ)^(-(s/8)) := Real.rpow_pos_of_pos hA _
    positivity
  set ε := η/(6*c) with hεdef
  have hε : 0 < ε := by positivity
  set P := e8GaussianRieszProfileRpow8 s with hPdef
  have hPi : IntegrableOn P (Ioi 0) := e8GaussianRieszProfileRpow8_integrable hs hs8
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
  set G : ℝ → ℝ := fun α => α^(s/2-1)*F α with hGdef
  have hGi : IntegrableOn G (Ioi 0) :=
    sphereGaussianCenteredScaled8_weighted_integrable_rpow hs hs8 (hN k) (X k)
  have hGp : IntegrableOn (fun α => max (G α) 0) (Ioi 0) := hGi.pos_part
  -- the two ends
  have hend1 : ∫ α in Ioc 0 a, G α ≤ ε := by
    have h1 : ∫ α in Ioc 0 a, G α ≤ ∫ α in Ioc 0 a, max (G α) 0 :=
      setIntegral_mono_on (hGi.mono_set Ioc_subset_Ioi_self) (hGp.mono_set Ioc_subset_Ioi_self)
        measurableSet_Ioc (fun α _ => le_max_left _ _)
    have h2 : ∫ α in Ioc 0 a, max (G α) 0 ≤ ∫ α in Ioc 0 (1/((n₁:ℝ)+1)), max (G α) 0 := by
      apply setIntegral_mono_set (hGp.mono_set Ioc_subset_Ioi_self)
      · exact Eventually.of_forall fun α => le_max_right _ _
      · exact (Ioc_subset_Ioc_right hsub1).eventuallyLE
    linarith
  have hend2 : ∫ α in Ioi b, G α ≤ ε := by
    have h1 : ∫ α in Ioi b, G α ≤ ∫ α in Ioi b, max (G α) 0 :=
      setIntegral_mono_on (hGi.mono_set (Ioi_subset_Ioi (ha.le.trans hab)))
        (hGp.mono_set (Ioi_subset_Ioi (ha.le.trans hab))) measurableSet_Ioi
        (fun α _ => le_max_left _ _)
    have h2 : ∫ α in Ioi b, max (G α) 0 ≤ ∫ α in Ioi ((n₂:ℝ)+1), max (G α) 0 := by
      apply setIntegral_mono_set (hGp.mono_set (Ioi_subset_Ioi (by positivity)))
      · exact Eventually.of_forall fun α => le_max_right _ _
      · exact (Ioi_subset_Ioi hsub2).eventuallyLE
    linarith
  -- the window
  have hwin : (∫ α in Ioc a b, G α) ≤ (∫ α in Ioc a b, P α)+ε := by
    have hdi : IntegrableOn (fun α => |α*F α-e8GaussianRieszProfile8 α|) (Ioi 0) :=
      ((sphereGaussianCenteredScaled8_weighted_integrable (hN k) (X k)).sub
        e8GaussianRieszProfile8_integrable).abs
    have h1 : ∫ α in Ioc a b, (G α-P α) ≤ ∫ α in Ioc a b, C*|α*F α-e8GaussianRieszProfile8 α| := by
      apply setIntegral_mono_on (IntegrableOn.mono_set (hGi.sub hPi) (Ioc_subset_Ioi_self.trans
        (Ioi_subset_Ioi ha.le))) (IntegrableOn.mono_set (hdi.const_mul C) (Ioc_subset_Ioi_self.trans
        (Ioi_subset_Ioi ha.le))) measurableSet_Ioc
      intro α hα
      exact (le_abs_self _).trans (weighted_profile_window_bound ha hα)
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
  rw [normalizedEnergyRpow_gaussian_mellin hs hs8 (hN k) (X k)]
  unfold sphereRieszCoefficient8
  have h8 := mul_le_mul_of_nonneg_left htot hc.le
  have h9 : c*(5*ε) ≤ η := by
    rw [hεdef]
    field_simp
    linarith
  calc c*(∫ α in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k))
      = c*(∫ α in Ioi 0, G α) := rfl
    _ ≤ c*((∫ α in Ioi 0, P α)+5*ε) := h8
    _ ≤ c*(∫ α in Ioi 0, P α)+η := by nlinarith

theorem integrableOn_rpow_mul_inv_sq_Ioc {s K₁ K₂ : ℝ} (hs4 : 4 < s) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*(K₁+K₂*(α^2)⁻¹)) (Ioc 0 1) := by
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

theorem sphereGaussianCenteredScaled8_le_of_energy_bound {N : ℕ} (hN : 0 < N)
    (X : Configuration N) {E₀ : ℝ} (hE : normalizedEnergy X ≤ E₀) {α : ℝ} (hα : 0 < α) :
    sphereGaussianCenteredScaled8 α X ≤
      Real.sqrt 2^9+Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))*(α^2)⁻¹ := by
  have h := sphereGaussianCenteredScaled8_le_inv_sq hN X hα
  have hr : (0:ℝ) < Real.sqrt 210 := by positivity
  have hk : (8/Real.sqrt 210)*normalizedEnergy X+1 ≤ (8/Real.sqrt 210)*E₀+1 := by
    have := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ 8/Real.sqrt 210)
    linarith
  have hα2 : 0 < α^2 := by positivity
  have hq : (2/3)*((8/Real.sqrt 210)*normalizedEnergy X+1)/α^2 ≤
      (2/3)*((8/Real.sqrt 210)*E₀+1)*(α^2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hα2.le)
  have h9 : 0 < Real.sqrt 2^9 := pow_pos (Real.sqrt_pos.mpr (by norm_num)) 9
  nlinarith

/-- For `4 < s` the small-scale end is automatic from a bound on the normalized `s = 4` energy. -/
theorem sphereGaussianCenteredScaled8_small_tail_four_lt {s : ℝ} (hs4 : 4 < s)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k)) {E₀ : ℝ}
    (hE : ∀ k, normalizedEnergy (X k) ≤ E₀) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε := by
  intro ε hε
  set K₁ := Real.sqrt 2^9 with hK₁
  set K₂ := max (Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))) 0 with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := le_max_right _ _
  have hg : IntegrableOn (fun α : ℝ => α^(s/2-1)*(K₁+K₂*(α^2)⁻¹)) (Ioc 0 1) :=
    integrableOn_rpow_mul_inv_sq_Ioc hs4
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (tendsto_setIntegral_Ioc_zero_inv hg)) ε hε)
  refine ⟨n₀, Eventually.of_forall fun k => ?_⟩
  have hsub : Ioc (0:ℝ) (1/((n₀:ℝ)+1)) ⊆ Ioc 0 1 := by
    apply Ioc_subset_Ioc_right
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
    linarith
  have hI := hn₀ n₀ le_rfl
  rw [Real.dist_eq, sub_zero] at hI
  calc ∫ α in Ioc 0 (1/((n₀:ℝ)+1)), max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0
      ≤ ∫ α in Ioc 0 (1/((n₀:ℝ)+1)), α^(s/2-1)*(K₁+K₂*(α^2)⁻¹) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun α => le_max_right _ _)
          (hg.mono_set hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
        have hα0 : 0 < α := hα.1
        have hw := Real.rpow_pos_of_pos hα0 (s/2-1)
        have hb := sphereGaussianCenteredScaled8_le_of_energy_bound (hN k) (X k) (hE k) hα0
        have hb' : sphereGaussianCenteredScaled8 α (X k) ≤ K₁+K₂*(α^2)⁻¹ := by
          have : Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))*(α^2)⁻¹ ≤ K₂*(α^2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (sq_nonneg α))
          linarith
        apply max_le
        · exact mul_le_mul_of_nonneg_left hb' hw.le
        · exact mul_nonneg hw.le (add_nonneg hK₁0 (mul_nonneg hK₂0 (inv_nonneg.mpr (sq_nonneg α))))
    _ ≤ ε := (le_abs_self _).trans hI.le

theorem sphereGaussianFullScaled8_antitone {N : ℕ} (X : Configuration N) {β β' : ℝ}
    (hββ : β ≤ β') :
    sphereGaussianFullScaled8 β' X ≤ sphereGaussianFullScaled8 β X := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hc : 0 ≤ ((N:ℝ)/sphereArea8.real univ)^(1/4:ℝ) := Real.rpow_nonneg (by positivity) _
  have ht : sphereGaussianScale8 N β ≤ sphereGaussianScale8 N β' := by
    unfold sphereGaussianScale8
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hββ Real.pi_pos.le) hc
  unfold sphereGaussianFullScaled8
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold sphereGaussianKernel8
  apply Real.exp_le_exp.mpr
  have := sq_nonneg (dist (X i) (X j))
  nlinarith

/-- The `L¹`-to-window comparison used by both averaging bounds. -/
theorem setIntegral_weighted_le_of_lower {F m : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Ioi 0)
    (hlow : ∀ β, 0 < β → -m β ≤ β*F β) (hm0 : ∀ β, 0 < β → 0 ≤ m β)
    (hFi : IntegrableOn (fun β => β*F β) (Ioi 0)) (hmi : IntegrableOn m (Ioi 0)) :
    ∫ β in S, β*F β ≤ (∫ β in Ioi 0, β*F β)+∫ β in Ioi 0, m β := by
  have hsplit := integral_inter_add_sdiff (μ := volume) hS hFi
  rw [inter_eq_right.mpr hSsub] at hsplit
  have h1 : ∫ β in Ioi 0 \ S, -m β ≤ ∫ β in Ioi 0 \ S, β*F β :=
    setIntegral_mono_on (hmi.mono_set sdiff_subset).neg (hFi.mono_set sdiff_subset)
      (measurableSet_Ioi.diff hS) (fun β hβ => hlow β hβ.1)
  have h2 : ∫ β in Ioi 0 \ S, m β ≤ ∫ β in Ioi 0, m β := by
    apply setIntegral_mono_set hmi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with β hβ
      exact hm0 β hβ
    · exact (sdiff_subset (s := Ioi (0:ℝ)) (t := S)).eventuallyLE
  rw [integral_neg] at h1
  linarith

/-- Large-scale bound from the `s = 4` energy: the full Gaussian sum is antitone in the scale. -/
theorem sphereGaussianCenteredScaled8_large_scale_bound {N : ℕ} (hN : 0 < N)
    (X : Configuration N) {α : ℝ} (hα : 0 < α) :
    sphereGaussianCenteredScaled8 α X*(3/8*α^2) ≤
      (8/Real.sqrt 210)*normalizedEnergy X+1+6/α^2 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hr : (0:ℝ) < Real.sqrt 210 := by positivity
  have hpt : ∀ β ∈ Ioc (α/2) α,
      β*(sphereGaussianCenteredScaled8 α X-16/α^4) ≤ β*sphereGaussianCenteredScaled8 β X := by
    intro β hβ
    have hβ0 : 0 < β := lt_trans (by positivity) hβ.1
    have hB0 : 0 ≤ (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) :=
      mul_nonneg hNR.le (sphereGaussianBackground8_nonneg _)
    have hcap := sphereGaussianBackground8_scaled_cap hN hβ0
    have hanti := sphereGaussianFullScaled8_antitone X hβ.2
    have hinv : (β^4)⁻¹ ≤ 16/α^4 := by
      have h1 : (α/2)^4 ≤ β^4 := pow_le_pow_left₀ (by positivity) hβ.1.le 4
      have h2 : 0 < (α/2)^4 := by positivity
      calc (β^4)⁻¹ ≤ ((α/2)^4)⁻¹ := inv_anti₀ h2 h1
        _ = 16/α^4 := by field_simp; ring
    have hF : sphereGaussianCenteredScaled8 α X-16/α^4 ≤ sphereGaussianCenteredScaled8 β X := by
      unfold sphereGaussianCenteredScaled8
      unfold sphereGaussianFullScaled8 at hanti
      linarith
    exact mul_le_mul_of_nonneg_left hF hβ0.le
  have hS : Ioc (α/2) α ⊆ Ioi 0 := fun β hβ => lt_trans (by positivity) hβ.1
  have hFi := sphereGaussianCenteredScaled8_weighted_integrable hN X
  have hle := setIntegral_weighted_le_of_lower (F := fun β => sphereGaussianCenteredScaled8 β X)
    (m := sphereGaussianMajorant8 4) measurableSet_Ioc hS
    (fun β hβ => sphereGaussianCenteredScaled8_weighted_lower hN hβ X)
    (fun β hβ => sphereGaussianMajorant8_nonneg 4 hβ) hFi
    (sphereGaussianMajorant8_integrable (by norm_num) (by norm_num))
  rw [sphereGaussianMajorant8_four_integral] at hle
  have hE : (∫ β in Ioi 0, β*sphereGaussianCenteredScaled8 β X) =
      (8/Real.sqrt 210)*normalizedEnergy X := by
    rw [normalizedEnergy_gaussian_mellin_four hN X, sphereGaussianArea8_coarse_coefficient]
    field_simp
  rw [hE] at hle
  have hci : IntegrableOn (fun β : ℝ => β*(sphereGaussianCenteredScaled8 α X-16/α^4))
      (Ioc (α/2) α) :=
    (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmono : ∫ β in Ioc (α/2) α, β*(sphereGaussianCenteredScaled8 α X-16/α^4) ≤
      ∫ β in Ioc (α/2) α, β*sphereGaussianCenteredScaled8 β X :=
    setIntegral_mono_on hci (hFi.mono_set hS) measurableSet_Ioc hpt
  have hid : ∫ β in Ioc (α/2) α, β*(sphereGaussianCenteredScaled8 α X-16/α^4) =
      (sphereGaussianCenteredScaled8 α X-16/α^4)*(3/8*α^2) := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith), integral_id]
    ring
  rw [hid] at hmono
  have h6 : 16/α^4*(3/8*α^2) = 6/α^2 := by field_simp; ring
  nlinarith

theorem integrableOn_rpow_inv_sq_add_inv_four_Ioi {s K₃ : ℝ} (hs4 : s < 4) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*(K₃*(α^2)⁻¹+16*(α^4)⁻¹)) (Ioi 1) := by
  have h1 : IntegrableOn (fun α : ℝ => α^(s/2-3)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have h2 : IntegrableOn (fun α : ℝ => α^(s/2-5)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  apply IntegrableOn.congr_fun ((h1.const_mul K₃).add (h2.const_mul 16)) _ measurableSet_Ioi
  intro α hα
  have hα0 : (0:ℝ) < α := lt_trans zero_lt_one hα
  have r2 : α^(s/2-3) = α^(s/2-1)*(α^2)⁻¹ := by
    rw [show s/2-3 = (s/2-1)+(-2:ℝ) by ring, Real.rpow_add hα0, Real.rpow_neg hα0.le,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have r4 : α^(s/2-5) = α^(s/2-1)*(α^4)⁻¹ := by
    rw [show s/2-5 = (s/2-1)+(-4:ℝ) by ring, Real.rpow_add hα0, Real.rpow_neg hα0.le,
      show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  simp only [Pi.add_apply]
  rw [r2, r4]
  ring

/-- For `s < 4` the large-scale end is automatic from a bound on the normalized `s = 4` energy. -/
theorem sphereGaussianCenteredScaled8_large_tail_lt_four {s : ℝ} (hs4 : s < 4)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k)) {E₀ : ℝ}
    (hE : ∀ k, normalizedEnergy (X k) ≤ E₀) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε := by
  intro ε hε
  have hr : (0:ℝ) < Real.sqrt 210 := by positivity
  set K₃ := max ((8/3)*((8/Real.sqrt 210)*E₀+1)) 0 with hK₃
  have hK₃0 : 0 ≤ K₃ := le_max_right _ _
  have hg : IntegrableOn (fun α : ℝ => α^(s/2-1)*(K₃*(α^2)⁻¹+16*(α^4)⁻¹)) (Ioi 1) :=
    integrableOn_rpow_inv_sq_add_inv_four_Ioi hs4
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (tendsto_setIntegral_Ioi_nat hg)) ε hε)
  refine ⟨n₀, Eventually.of_forall fun k => ?_⟩
  have hsub : Ioi ((n₀:ℝ)+1) ⊆ Ioi 1 := by
    apply Ioi_subset_Ioi
    have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
    linarith
  have hI := hn₀ n₀ le_rfl
  rw [Real.dist_eq, sub_zero] at hI
  calc ∫ α in Ioi ((n₀:ℝ)+1), max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0
      ≤ ∫ α in Ioi ((n₀:ℝ)+1), α^(s/2-1)*(K₃*(α^2)⁻¹+16*(α^4)⁻¹) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun α => le_max_right _ _)
          (hg.mono_set hsub)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        have hα0 : 0 < α := lt_of_le_of_lt (by positivity) hα
        have hw := Real.rpow_pos_of_pos hα0 (s/2-1)
        have hb := sphereGaussianCenteredScaled8_large_scale_bound (hN k) (X k) hα0
        have hEk : (8/Real.sqrt 210)*normalizedEnergy (X k) ≤ (8/Real.sqrt 210)*E₀ :=
          mul_le_mul_of_nonneg_left (hE k) (by positivity)
        have hα2 : 0 < α^2 := by positivity
        have hb' : sphereGaussianCenteredScaled8 α (X k) ≤ K₃*(α^2)⁻¹+16*(α^4)⁻¹ := by
          have h1 : sphereGaussianCenteredScaled8 α (X k) ≤
              ((8/Real.sqrt 210)*E₀+1+6/α^2)/(3/8*α^2) := by
            rw [le_div_iff₀ (by positivity)]
            linarith
          have h2 : ((8/Real.sqrt 210)*E₀+1+6/α^2)/(3/8*α^2) =
              (8/3)*((8/Real.sqrt 210)*E₀+1)*(α^2)⁻¹+16*(α^4)⁻¹ := by
            field_simp
            ring
          have h3 : (8/3)*((8/Real.sqrt 210)*E₀+1)*(α^2)⁻¹ ≤ K₃*(α^2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hα2.le)
          linarith
        apply max_le
        · exact mul_le_mul_of_nonneg_left hb' hw.le
        · exact mul_nonneg hw.le (add_nonneg (mul_nonneg hK₃0 (inv_nonneg.mpr hα2.le))
            (mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity))))
    _ ≤ ε := (le_abs_self _).trans hI.le

/-- `4 < s < 8`: a sharp `s = 4` sequence under the G8 lower profile, with bounded `s = 4` energy
and a uniformly controlled short-range end, is sharp for `s`. -/
theorem sphere8_riesz_upper_of_sharp_four_lt {s : ℝ} (hs4 : 4 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε)
    {E₀ : ℝ} (hE₀ : ∀ k, normalizedEnergy (X k) ≤ E₀)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η :=
  normalizedEnergyRpow_eventually_le_of_L1_tails (by linarith) hs8 hN X
    (sphereGaussianCenteredScaled8_L1_tendsto_of_sharp hN X hp hE)
    (sphereGaussianCenteredScaled8_small_tail_four_lt hs4 hN X hE₀) hlarge

/-- `0 < s < 4`: the same with a uniformly controlled macroscopic end. -/
theorem sphere8_riesz_upper_of_sharp_lt_four {s : ℝ} (hs : 0 < s) (hs4 : s < 4)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε)
    {E₀ : ℝ} (hE₀ : ∀ k, normalizedEnergy (X k) ≤ E₀)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η :=
  normalizedEnergyRpow_eventually_le_of_L1_tails hs (by linarith) hN X
    (sphereGaussianCenteredScaled8_L1_tendsto_of_sharp hN X hp hE) hsmall
    (sphereGaussianCenteredScaled8_large_tail_lt_four hs4 hN X hE₀)

/-- Under the CKMRV Laplace–sine contract (`4 < s < 8`). -/
theorem sphere8_riesz_upper_four_lt_of_laplaceSineData (D : E8LaplaceSineData8) {s : ℝ}
    (hs4 : 4 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε)
    {E₀ : ℝ} (hE₀ : ∀ k, normalizedEnergy (X k) ≤ E₀)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η :=
  sphere8_riesz_upper_of_sharp_four_lt hs4 hs8 hN X
    (fun α hα => sphereGaussianSharpProfileLower8_of_schwartz_input
      (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩)) N hNt hN X α hα)
    hE hE₀ hlarge

/-- Under the CKMRV Laplace–sine contract (`0 < s < 4`). -/
theorem sphere8_riesz_upper_lt_four_of_laplaceSineData (D : E8LaplaceSineData8) {s : ℝ}
    (hs : 0 < s) (hs4 : s < 4)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε)
    {E₀ : ℝ} (hE₀ : ∀ k, normalizedEnergy (X k) ≤ E₀)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow s (X k) ≤ sphereRieszCoefficient8 s+η :=
  sphere8_riesz_upper_of_sharp_lt_four hs hs4 hN X
    (fun α hα => sphereGaussianSharpProfileLower8_of_schwartz_input
      (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩)) N hNt hN X α hα)
    hE hE₀ hsmall

end SphericalRiesz
