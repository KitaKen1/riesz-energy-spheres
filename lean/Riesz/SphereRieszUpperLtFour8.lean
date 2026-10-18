import Riesz.SphereLongRangeAllN8
import Riesz.SphereRieszUpperFourLtAllN8
import Riesz.SphereRieszSharpFourLt8
import Riesz.SphereSharpUpperAllN8
import Riesz.E8EpsteinTwo8

/-! The sharp upper bound for `0 < s < 4` and two-sided asymptotics for every `0 < s < 8`.

With `p = s/4 - 1` and `θ = s/4`, the long-range block of a configuration is
`N ∫₀¹ α^p (F(α)+1) dα`.  Since `F + 1 ≥ 0` and `α^{s/2-1} = α^θ α^p ≤ δ^θ α^p` on `(0,δ]`,

  `∫₀^δ max(α^{s/2-1} F(α), 0) dα ≤ δ^θ · block/N`,

so a uniform bound on the normalized long-range block gives the macroscopic end of the
known-answer transfer.  The all-`N` configurations of `sphere8_joint_sharp_longRange_allN` and a
diagonal choice give the upper bound for every large `N`; with the checked lower bound and the
`s = 4`, `4 < s < 8` cases this is the two-sided second-order asymptotics for every `0 < s < 8`
under the CKMRV Laplace–sine contract. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem longRange_profile_integral {N : ℕ} (hN : 0 < N) (Y : Configuration N) {p : ℝ}
    (hp : -1 < p) :
    kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => Y i) univ N =
      (N:ℝ)*∫ α in Ioc (0:ℝ) 1, α^p*(sphereGaussianCenteredScaled8 α Y+1) := by
  have hc := sphereGaussianDensityFactor8_pos hN
  rw [longRangeBlock8_eq hc.le hp, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro α hα
  simp only
  rw [← sphereGaussianScale8_eq_factor, gaussianKernelBlock8_config hN hα.1.le]
  ring

theorem profile_weighted_integrable {N : ℕ} (hN : 0 < N) (Y : Configuration N) {p b : ℝ}
    (hp : -1 < p) (hb : 0 ≤ b) :
    IntegrableOn (fun α : ℝ => α^p*(sphereGaussianCenteredScaled8 α Y+1)) (Ioc 0 b) := by
  have hc := sphereGaussianDensityFactor8_pos hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have h := weighted_bounded_integrable_Ioc hp hb
    (gaussianBlock_alpha_measurable (sphereGaussianDensityFactor8 N) (fun i => Y i) univ N)
    (fun α hα => gaussianBlock_abs_le (mul_nonneg hc.le hα.1.le) (fun i => Y i) univ N)
  refine IntegrableOn.congr_fun (h.const_mul ((N:ℝ)⁻¹)) (fun α hα => ?_) measurableSet_Ioc
  show (N:ℝ)⁻¹*(α^p*kernelBlock8 (sphereGaussianKernel8 (sphereGaussianDensityFactor8 N*α))
    (fun i => Y i) univ N) = α^p*(sphereGaussianCenteredScaled8 α Y+1)
  rw [← sphereGaussianScale8_eq_factor, gaussianKernelBlock8_config hN hα.1.le]
  field_simp

/-- The macroscopic end from a uniform bound on the normalized long-range block. -/
theorem hsmall_of_longRange {s : ℝ} (hs : 0 < s) {N : ℕ → ℕ} (hN : ∀ k, 0 < N k)
    (X : ∀ k, Configuration (N k)) {C : ℝ}
    (hL : ∀ k, kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 (N k)) (s/4-1))
      (fun i => X k i) univ (N k)/(N k:ℝ) ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioc 0 (1/((n₀:ℝ)+1)),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε := by
  set p := s/4-1 with hpdef
  set θ := s/4 with hθdef
  have hp : -1 < p := by rw [hpdef]; linarith
  have hθ : 0 < θ := by rw [hθdef]; linarith
  have hθp : θ+p = s/2-1 := by rw [hθdef, hpdef]; ring
  intro ε hε
  set C₀ := max C 0+1 with hC₀
  have hC₀0 : 0 < C₀ := by rw [hC₀]; have := le_max_right C 0; linarith
  have hlim : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))^θ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.comp h1
    rw [Real.zero_rpow hθ.ne'] at h2
    exact h2
  obtain ⟨n₀, hn₀⟩ := (hlim.eventually (gt_mem_nhds (div_pos hε hC₀0))).exists
  refine ⟨n₀, Eventually.of_forall fun k => ?_⟩
  set δ := 1/((n₀:ℝ)+1) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
    linarith
  have hNk : (0:ℝ) < N k := by exact_mod_cast hN k
  have hg := profile_weighted_integrable (hN k) (X k) hp zero_le_one
  have hgδ := profile_weighted_integrable (hN k) (X k) hp hδ0.le
  have hF : ∀ α ∈ Ioc (0:ℝ) 1, 0 ≤ sphereGaussianCenteredScaled8 α (X k)+1 :=
    fun α hα => sphereGaussianCenteredScaled8_add_one_nonneg (hN k) hα.1.le (X k)
  have hpt : ∀ α ∈ Ioc (0:ℝ) δ, max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤
      δ^θ*(α^p*(sphereGaussianCenteredScaled8 α (X k)+1)) := by
    intro α hα
    have hα1 : α ∈ Ioc (0:ℝ) 1 := ⟨hα.1, hα.2.trans hδ1⟩
    have hF1 := hF α hα1
    have hαs : α^(s/2-1) = α^θ*α^p := by rw [← Real.rpow_add hα.1, hθp]
    have hαθ : α^θ ≤ δ^θ := Real.rpow_le_rpow hα.1.le hα.2 hθ.le
    have h0 : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
    have h0θ : 0 ≤ α^θ := Real.rpow_nonneg hα.1.le _
    have hmax : max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤
        α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) := by
      have hx : 0 ≤ α^(s/2-1) := Real.rpow_nonneg hα.1.le _
      apply max_le
      · nlinarith
      · exact mul_nonneg hx hF1
    calc max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0
        ≤ α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) := hmax
      _ = α^θ*(α^p*(sphereGaussianCenteredScaled8 α (X k)+1)) := by rw [hαs]; ring
      _ ≤ δ^θ*(α^p*(sphereGaussianCenteredScaled8 α (X k)+1)) :=
          mul_le_mul_of_nonneg_right hαθ (mul_nonneg h0 hF1)
  have hstep1 : ∫ α in Ioc 0 δ, max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤
      ∫ α in Ioc 0 δ, δ^θ*(α^p*(sphereGaussianCenteredScaled8 α (X k)+1)) := by
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun α => le_max_right _ _
    · exact hgδ.const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact hpt α hα
  have hstep2 : ∫ α in Ioc 0 δ, α^p*(sphereGaussianCenteredScaled8 α (X k)+1) ≤
      ∫ α in Ioc 0 1, α^p*(sphereGaussianCenteredScaled8 α (X k)+1) := by
    apply setIntegral_mono_set hg
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact mul_nonneg (Real.rpow_nonneg hα.1.le _) (hF α hα)
    · exact Eventually.of_forall (Ioc_subset_Ioc_right hδ1)
  have hblock := longRange_profile_integral (hN k) (X k) hp
  have hint_le : ∫ α in Ioc 0 1, α^p*(sphereGaussianCenteredScaled8 α (X k)+1) ≤ max C 0 := by
    have h := hL k
    rw [hblock, mul_div_cancel_left₀ _ hNk.ne'] at h
    exact h.trans (le_max_left _ _)
  have hδθ : δ^θ ≤ ε/C₀ := (hn₀).le
  have hδθ0 : 0 ≤ δ^θ := Real.rpow_nonneg hδ0.le _
  calc ∫ α in Ioc 0 δ, max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0
      ≤ ∫ α in Ioc 0 δ, δ^θ*(α^p*(sphereGaussianCenteredScaled8 α (X k)+1)) := hstep1
    _ = δ^θ*∫ α in Ioc 0 δ, α^p*(sphereGaussianCenteredScaled8 α (X k)+1) := integral_const_mul _ _
    _ ≤ δ^θ*max C 0 := mul_le_mul_of_nonneg_left (hstep2.trans hint_le) hδθ0
    _ ≤ (ε/C₀)*max C 0 := mul_le_mul_of_nonneg_right hδθ (le_max_right _ _)
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hC₀0]
        have := le_max_right C 0
        nlinarith

/-- The sharp upper bound for every exponent `0 < s < 4` and every large `N`, under the CKMRV
contract. -/
theorem sphere8_riesz_upper_lt_four (D : E8LaplaceSineData8) {s : ℝ} (hs : 0 < s) (hs4 : s < 4) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      normalizedEnergyRpow s Y ≤ sphereRieszCoefficient8 s+η := by
  have hp1 : -1 < s/4-1 := by linarith
  obtain ⟨C', hC'⟩ := sphere8_joint_sharp_longRange_allN (sphere8_lower4_of_laplaceSineData D) hp1
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+1/((j:ℝ)+1) ∧
      kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) (s/4-1)) (fun i => Y i)
        univ N/(N:ℝ) ≤ C' := by
    intro j
    apply hC' _ (by positivity)
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
    linarith
  obtain ⟨J, hJ, hev⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  have hstep : ∀ k : ℕ, ∃ Y : Configuration (k+N₁+1),
      normalizedEnergy Y < predictedCoefficient+1/((J (k+N₁+1):ℝ)+1) ∧
      kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 (k+N₁+1)) (s/4-1))
        (fun i => Y i) univ ((k+N₁+1:ℕ):ℝ)/((k+N₁+1:ℕ):ℝ) ≤ C' := fun k => hN₁ (k+N₁+1) (by omega)
  choose X hX using hstep
  have hNt : Tendsto (fun k : ℕ => k+N₁+1) atTop atTop := by
    apply tendsto_atTop_mono (fun k => (by omega : k ≤ k+N₁+1)) tendsto_id
  have hNpos : ∀ k, 0 < k+N₁+1 := fun k => by omega
  have hJt : Tendsto (fun k : ℕ => J (k+N₁+1)) atTop atTop := hJ.comp hNt
  have hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1/((J (k+N₁+1):ℝ)+1) ≤ ε := fun ε hε =>
    hJt.eventually (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε))
  have hmain := sphere8_riesz_upper_lt_four_of_laplaceSineData D hs hs4 hNt hNpos X
    (E₀ := predictedCoefficient+1)
    (fun ε hε => by
      filter_upwards [hsm ε hε] with k hk
      linarith [(hX k).1])
    (fun k => by
      have h1 : 1/((J (k+N₁+1):ℝ)+1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := (Nat.cast_nonneg (J (k+N₁+1)) : (0:ℝ) ≤ J (k+N₁+1))
        linarith
      linarith [(hX k).1])
    (hsmall_of_longRange hs hNpos X (fun k => (hX k).2))
  intro η hη
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hmain η hη)
  refine ⟨k₀+N₁+1, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = k+N₁+1 := ⟨N-N₁-1, by omega⟩
  exact ⟨X k, hk₀ k (by omega)⟩

/-- The sharp upper bound for every `0 < s < 8` and every large `N`, under the CKMRV contract. -/
theorem sphere8_riesz_upper (D : E8LaplaceSineData8) {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      normalizedEnergyRpow s Y ≤ sphereRieszCoefficient8 s+η := by
  rcases lt_trichotomy s 4 with h | h | h
  · exact sphere8_riesz_upper_lt_four D hs h
  · subst h
    intro η hη
    obtain ⟨N₀, -, hN₀⟩ := sphere8_inverse_fourth_sharp_upper η hη
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨Y, hY⟩ := hN₀ N hN
    refine ⟨Y, ?_⟩
    rw [normalizedEnergyRpow_four, sphereRieszCoefficient8_four]
    exact hY
  · exact sphere8_riesz_upper_four_lt D h hs8

/-- Two-sided sharp asymptotics for every `0 < s < 8`, `s ≠ 2`, in conjecture form, under the
CKMRV contract. -/
theorem sphere8_riesz_sharp_asymptotic (D : E8LaplaceSineData8) {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    (hs2 : s ≠ 2) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyRpow s Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re+η) := by
  refine ⟨sphere8_riesz_sharp_lower_conjecture_form D hs hs8 hs2, fun η hη => ?_⟩
  obtain ⟨N₀, h⟩ := sphere8_riesz_upper D hs hs8 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyRpow, sphereRieszConst8_eq_pair_integral hs hs8,
    sphereRieszCoefficient8_eq_epstein hs hs8 hs2] at hY


/-- Two-sided sharp asymptotics for every `0 < s < 8` with the Mellin coefficient and the actual
uniform double integral, under the CKMRV contract. -/
theorem sphere8_riesz_sharp_asymptotic_all (D : E8LaplaceSineData8) {s : ℝ} (hs : 0 < s)
    (hs8 : s < 8) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      sphereRieszCoefficient8 s-η ≤
        (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyRpow s Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        sphereRieszCoefficient8 s+η) := by
  refine ⟨fun η hη => ?_, fun η hη => ?_⟩
  · obtain ⟨N₀, h⟩ := sphere8_riesz_sharp_lower_of_laplaceSineData D hs hs8 η hη
    refine ⟨N₀, fun N hN X => ?_⟩
    have := h N hN X
    rwa [normalizedEnergyRpow, sphereRieszConst8_eq_pair_integral hs hs8] at this
  · obtain ⟨N₀, h⟩ := sphere8_riesz_upper D hs hs8 η hη
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨Y, hY⟩ := h N hN
    refine ⟨Y, ?_⟩
    rwa [normalizedEnergyRpow, sphereRieszConst8_eq_pair_integral hs hs8] at hY

/-- Two-sided sharp asymptotics at the removable point `s = 2`, with the coefficient
`A₈^(-1/4)·120·Re ζ'(-2)`, under the CKMRV contract. -/
theorem sphere8_riesz_sharp_asymptotic_two (D : E8LaplaceSineData8) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (sphereArea8.real univ)^(-((2:ℝ)/8))*(120*(deriv riemannZeta (-2)).re)-η ≤
        (energyRpow 2 X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-(2:ℝ))
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+(2:ℝ)/8)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyRpow 2 Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-(2:ℝ))
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+(2:ℝ)/8) ≤
        (sphereArea8.real univ)^(-((2:ℝ)/8))*(120*(deriv riemannZeta (-2)).re)+η) := by
  have h := sphere8_riesz_sharp_asymptotic_all D (s := 2) (by norm_num) (by norm_num)
  rw [sphereRieszCoefficient8_two] at h
  exact h

end SphericalRiesz
