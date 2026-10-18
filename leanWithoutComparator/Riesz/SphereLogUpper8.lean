import Riesz.NegAllN8
import Riesz.SphereLogConstPair8

/-! The logarithmic energy on `S⁸`, upper bound and two-sided asymptotics (stage LOG).

With `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα` and the E8 log profile
`P(α) = α⁻¹ (Θ(α) - α⁻⁴ - 1 + 1_{(0,1)}(α))`, the difference of the integrands is
`α⁻² (α F_N(α) - α(Θ(α) - α⁻⁴ - 1))` for every `α > 0`, so on `(a, ∞)` it is bounded by
`a⁻² |α F_N - R_{E8}|`, whose integral tends to `0` along any sharp `s = 4` sequence (the `L¹`
convergence of the Gaussian profiles). The remaining end `(0, a]` is the macroscopic end with
exponent `p = -1`, which the negative-exponent construction makes small for every large `N`.
Hence `J_N ≤ J_∞ + o(1)`, i.e. `(E_log - W N² + (N/8) log N)/N ≤ C_log + η` for some configuration
of every large size, matching the universal lower bound: the two-sided logarithmic asymptotics
`C_log = -60 Re ζ'(-3) + (5/8) log 2 - (1/8) log 105`, under the CKMRV contract and the
exact-mass stratification hypotheses. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

/-- Along a sharp `s = 4` sequence with a small macroscopic end at exponent `-1`, the normalized
logarithmic energy is eventually at most `C_log + η`. -/
theorem normalizedEnergyLog8_eventually_le_of_L1 {N : ℕ → ℕ} (hN : ∀ k, 0 < N k)
    (X : ∀ k, Configuration (N k))
    (hL1 : Tendsto (fun k => ∫ α in Ioi (0:ℝ),
      |α*sphereGaussianCenteredScaled8 α (X k)-e8GaussianRieszProfile8 α|) atTop (𝓝 0))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      α^(-1:ℝ)*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyLog8 (X k) ≤ sphereLogCoefficient8+η := by
  intro η hη
  set ε := η/4 with hεdef
  have hε : 0 < ε := by positivity
  set P := e8GaussianLogProfile8 with hPdef
  have hPi : IntegrableOn P (Ioi 0) := e8GaussianLogProfile8_integrable
  obtain ⟨n₁, hn₁⟩ := hsmall ε hε
  have hPs := tendsto_setIntegral_Ioc_zero_inv (hPi.mono_set Ioc_subset_Ioi_self)
  obtain ⟨n, hn12, hsP⟩ := ((eventually_ge_atTop (max n₁ 1)).and
    (Metric.tendsto_nhds.mp hPs ε hε)).exists
  rw [Real.dist_eq, sub_zero] at hsP
  set a : ℝ := 1/((n:ℝ)+1) with hadef
  have ha : 0 < a := by positivity
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn12
  have ha1 : a < 1 := by
    rw [hadef, div_lt_one (by positivity)]
    linarith
  have hsub1 : a ≤ 1/((n₁:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (n₁:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn12
    linarith
  set C := (a^2)⁻¹ with hCdef
  have hC : 0 ≤ C := by positivity
  have hL1' : ∀ᶠ k in atTop, C*∫ α in Ioi (0:ℝ),
      |α*sphereGaussianCenteredScaled8 α (X k)-e8GaussianRieszProfile8 α| ≤ ε := by
    have ht := hL1.const_mul C
    rw [mul_zero] at ht
    exact ht.eventually (ge_mem_nhds hε)
  filter_upwards [hn₁, hL1'] with k hk1 hk3
  set F : ℝ → ℝ := fun α => sphereGaussianCenteredScaled8 α (X k) with hFdef
  set G : ℝ → ℝ := fun α => α⁻¹*(F α+(Ioo (0:ℝ) 1).indicator 1 α) with hGdef
  have hGi : IntegrableOn G (Ioi 0) := sphereGaussianCenteredScaled8_log_integrable (hN k) (X k)
  -- the macroscopic end
  have hne1 : ∀ᵐ α : ℝ ∂(volume.restrict (Ioc 0 1)), α ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 1), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    exact ht
  have hHi : IntegrableOn (fun α : ℝ => α^(-1:ℝ)*(F α+1)) (Ioc 0 1) := by
    refine (hGi.mono_set Ioc_subset_Ioi_self).congr_fun_ae ?_
    filter_upwards [hne1, ae_restrict_mem measurableSet_Ioc] with α hα1 hα
    have hlt : α < 1 := lt_of_le_of_ne hα.2 hα1
    have hin : α ∈ Ioo (0:ℝ) 1 := ⟨hα.1, hlt⟩
    simp only [hGdef, indicator_of_mem hin, Pi.one_apply, Real.rpow_neg_one]
  have hH0 : ∀ α ∈ Ioi (0:ℝ), 0 ≤ α^(-1:ℝ)*(F α+1) := fun α hα =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hα) _)
      (sphereGaussianCenteredScaled8_add_one_nonneg (hN k) (le_of_lt hα) (X k))
  have hn₁1 : 1/((n₁:ℝ)+1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg n₁ : (0:ℝ) ≤ n₁)
    linarith
  have hend : ∫ α in Ioc 0 a, G α ≤ ε := by
    have heq : ∫ α in Ioc 0 a, G α = ∫ α in Ioc 0 a, α^(-1:ℝ)*(F α+1) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro α hα
      have hin : α ∈ Ioo (0:ℝ) 1 := ⟨hα.1, lt_of_le_of_lt hα.2 ha1⟩
      simp only [hGdef, indicator_of_mem hin, Pi.one_apply, Real.rpow_neg_one]
    have h2 : ∫ α in Ioc 0 a, α^(-1:ℝ)*(F α+1) ≤
        ∫ α in Ioc 0 (1/((n₁:ℝ)+1)), α^(-1:ℝ)*(F α+1) := by
      apply setIntegral_mono_set (hHi.mono_set (Ioc_subset_Ioc_right hn₁1))
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
        exact hH0 α hα.1
      · exact (Ioc_subset_Ioc_right hsub1).eventuallyLE
    rw [heq]
    linarith
  -- the rest, by the `L¹` convergence
  have hdi : IntegrableOn (fun α => |α*F α-e8GaussianRieszProfile8 α|) (Ioi 0) :=
    ((sphereGaussianCenteredScaled8_weighted_integrable (hN k) (X k)).sub
      e8GaussianRieszProfile8_integrable).abs
  have hrest : (∫ α in Ioi a, G α) ≤ (∫ α in Ioi a, P α)+ε := by
    have h1 : ∫ α in Ioi a, (G α-P α) ≤ ∫ α in Ioi a, C*|α*F α-e8GaussianRieszProfile8 α| := by
      apply setIntegral_mono_on ((hGi.sub hPi).mono_set (Ioi_subset_Ioi ha.le))
        (IntegrableOn.mono_set (hdi.const_mul C) (Ioi_subset_Ioi ha.le)) measurableSet_Ioi
      intro α hα
      have hα0 : 0 < α := ha.trans hα
      have hdiff : G α-P α = (α^2)⁻¹*(α*F α-e8GaussianRieszProfile8 α) := by
        simp only [hGdef, hPdef, e8GaussianLogProfile8, e8GaussianRieszProfile8]
        field_simp
        ring
      simp only [Pi.sub_apply]
      rw [hdiff]
      have hle : (α^2)⁻¹ ≤ C := by
        rw [hCdef]
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_left₀ ha.le hα.le 2
      calc (α^2)⁻¹*(α*F α-e8GaussianRieszProfile8 α)
          ≤ (α^2)⁻¹*|α*F α-e8GaussianRieszProfile8 α| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ C*|α*F α-e8GaussianRieszProfile8 α| :=
            mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    have h2 : ∫ α in Ioi a, C*|α*F α-e8GaussianRieszProfile8 α| ≤
        C*∫ α in Ioi (0:ℝ), |α*F α-e8GaussianRieszProfile8 α| := by
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ hC
      apply setIntegral_mono_set hdi
      · exact Eventually.of_forall fun α => abs_nonneg _
      · exact (Ioi_subset_Ioi ha.le).eventuallyLE
    have h3 : ∫ α in Ioi a, (G α-P α) = (∫ α in Ioi a, G α)-∫ α in Ioi a, P α :=
      integral_sub (hGi.mono_set (Ioi_subset_Ioi ha.le)) (hPi.mono_set (Ioi_subset_Ioi ha.le))
    linarith
  have hsplitG := setIntegral_Ioi_zero_split hGi ha le_rfl
  have hsplitP := setIntegral_Ioi_zero_split hPi ha le_rfl
  have hempty : ∀ f : ℝ → ℝ, ∫ α in Ioc a a, f α = 0 := by
    intro f
    simp
  rw [hempty, add_zero] at hsplitG hsplitP
  have htot : (∫ α in Ioi 0, G α) ≤ (∫ α in Ioi 0, P α)+3*ε := by
    have h4 := neg_abs_le (∫ α in Ioc 0 a, P α)
    linarith
  rw [normalizedEnergyLog8_gaussian_mellin (hN k) (X k)]
  unfold sphereLogCoefficient8
  change (1/2)*((∫ α in Ioi 0, G α)+logGaussianConst-Real.log Real.pi+
      (1/4)*Real.log (sphereArea8.real univ)) ≤
    (1/2)*((∫ α in Ioi 0, P α)+logGaussianConst-Real.log Real.pi+
      (1/4)*Real.log (sphereArea8.real univ))+η
  linarith

/-- Configurations of every large size with logarithmic energy at most `C_log + η`, under the
CKMRV contract and the stratification hypotheses. -/
theorem sphere8_log_upper_allN (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      normalizedEnergyLog8 Y ≤ sphereLogCoefficient8+η := by
  have hp : (-2:ℝ) < -1 := by norm_num
  have hp3 : (0:ℝ) < -1+3 := by norm_num
  obtain ⟨C₂, hC₂, hC⟩ := sphere8_neg_sharp_allN (sphere8_lower4_of_laplaceSineData D) hB hstrat
    hsphere hp
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+1/((j:ℝ)+1) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1/2 →
        ∫ α in Ioc 0 t, α^(-1:ℝ)*(sphereGaussianCenteredScaled8 α Y+1) ≤
          C₂*(t^((-1:ℝ)+3)/((-1:ℝ)+3))+15*(1/((j:ℝ)+1)) := by
    intro j
    apply hC _ (by positivity)
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
    linarith
  obtain ⟨J, hJ, hev⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  have hstep : ∀ k : ℕ, ∃ Y : Configuration (k+N₁+1),
      normalizedEnergy Y < predictedCoefficient+1/((J (k+N₁+1):ℝ)+1) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1/2 →
        ∫ α in Ioc 0 t, α^(-1:ℝ)*(sphereGaussianCenteredScaled8 α Y+1) ≤
          C₂*(t^((-1:ℝ)+3)/((-1:ℝ)+3))+15*(1/((J (k+N₁+1):ℝ)+1)) :=
    fun k => hN₁ (k+N₁+1) (by omega)
  choose X hX using hstep
  have hNt : Tendsto (fun k : ℕ => k+N₁+1) atTop atTop :=
    tendsto_atTop_mono (fun k => (by omega : k ≤ k+N₁+1)) tendsto_id
  have hNpos : ∀ k, 0 < k+N₁+1 := fun k => by omega
  have hJt : Tendsto (fun k : ℕ => J (k+N₁+1)) atTop atTop := hJ.comp hNt
  have hinv : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1/((J (k+N₁+1):ℝ)+1) ≤ ε := fun ε hε =>
    hJt.eventually (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε))
  have hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, normalizedEnergy (X k) ≤ predictedCoefficient+ε :=
    fun ε hε => by
      filter_upwards [hinv ε hε] with k hk
      linarith [(hX k).1]
  have hprof : SphereGaussianSharpProfileLower8 :=
    sphereGaussianSharpProfileLower8_of_schwartz_input
      (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩))
  have hL1 := sphereGaussianCenteredScaled8_L1_tendsto_of_sharp hNpos X (hprof _ hNt hNpos X) hE
  have hmain := normalizedEnergyLog8_eventually_le_of_L1 hNpos X hL1
    (fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (show 0 < ε*((-1:ℝ)+3)/(2*(C₂+1)) by positivity)
      refine ⟨n₀+1, ?_⟩
      filter_upwards [hinv (ε/30) (by positivity)] with k hk
      have hn1 : (1:ℝ) ≤ ((n₀+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n₀)
      set x : ℝ := 1/(((n₀+1:ℕ):ℝ)+1) with hx
      have hx0 : 0 < x := by positivity
      have hx2 : x ≤ 1/2 := by
        rw [hx]
        apply one_div_le_one_div_of_le (by norm_num)
        linarith
      have hxn : x ≤ 1/((n₀:ℝ)+1) := by
        rw [hx]
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      have hb := (hX k).2 x hx0 hx2
      have hxq : x^((-1:ℝ)+3) ≤ x := by
        have h := Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith)
          (show (1:ℝ) ≤ (-1:ℝ)+3 by norm_num)
        rwa [Real.rpow_one] at h
      have hterm : C₂*(x^((-1:ℝ)+3)/((-1:ℝ)+3)) ≤ ε/2 := by
        have h1 : C₂*(x^((-1:ℝ)+3)/((-1:ℝ)+3)) ≤ C₂*(x/((-1:ℝ)+3)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxq hp3.le) hC₂
        have h2 : x < ε*((-1:ℝ)+3)/(2*(C₂+1)) := lt_of_le_of_lt hxn hn₀
        have h3 : C₂*(x/((-1:ℝ)+3)) ≤ ε/2 := by
          rw [mul_div_assoc', div_le_iff₀ hp3]
          have h4 : x*(2*(C₂+1)) < ε*((-1:ℝ)+3) := by
            rwa [lt_div_iff₀ (by positivity)] at h2
          nlinarith
        linarith
      have h15 : 15*(1/((J (k+N₁+1):ℝ)+1)) ≤ ε/2 := by linarith
      linarith)
  intro η hη
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hmain η hη)
  refine ⟨k₀+N₁+1, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = k+N₁+1 := ⟨N-N₁-1, by omega⟩
  exact ⟨X k, hk₀ k (by omega)⟩

/-- The two-sided logarithmic asymptotics on `S⁸` in conjecture form:
`(E_log - W N² + (N/8) log N)/N → C_log = -60 Re ζ'(-3) + (5/8) log 2 - (1/8) log 105`
(all configurations above, some configuration below), under the CKMRV contract and the exact-mass
stratification hypotheses. -/
theorem sphere8_log_sharp_asymptotic (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105-η ≤
        (energyLog X-(∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyLog Y-(∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ) ≤
        -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105+η) := by
  refine ⟨sphere8_log_lower_conjecture_form D, fun η hη => ?_⟩
  obtain ⟨N₀, h⟩ := sphere8_log_upper_allN D hB hstrat hsphere η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rw [← sphereLogConst8_eq_pair_integral, ← sphereLogCoefficient8_eq_zeta]
  exact hY

#print axioms normalizedEnergyLog8_eventually_le_of_L1
#print axioms sphere8_log_upper_allN
#print axioms sphere8_log_sharp_asymptotic

end SphericalRiesz
