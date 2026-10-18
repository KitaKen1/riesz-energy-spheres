import Riesz.E8EpsteinNeg8

/-! The universal sharp bound for negative exponents `-2 < s < 0` (stage NEG, first half).

For `-2 < s < 0` every configuration satisfies, for all large `N`,
`(E_s(X) - I_s N²)/N^(1+s/8) ≤ A₈^(-s/8) Re ζ_E8(s) + η`, where `E_s(X) = Σ_{i≠j} |x_i-x_j|^|s|`
and `I_s` is the actual double integral of `|x-y|^|s|`. In the Brauchart–Hardin–Saff sign
convention (`k_s = sgn(s) r^(-s)`) this is the sharp lower bound for the minimal energy.
The integrand `α^(s/2-1)(F_N(α)+1)` is nonnegative (positive definiteness), so Fatou needs no
majorant; the prefactor `π^(s/2) A₈^(-s/8)/Γ(s/2)` is negative, which turns the Fatou lower bound
for the Mellin integral into an upper bound for the energy. The deep input is the same sharp
sphere Gaussian profile (G8 / CKMRV Laplace–sine contract) as for positive exponents. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem sphereGaussianCenteredScaled8_neg_profile_eventually (s : ℝ)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianRieszProfileNeg8 s α-ε ≤
        α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1) := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  filter_upwards [hp (ε/α^(s/2-1)) (div_pos hε hw)] with k hk
  have hb := sphereGaussianCenteredScaled8_ge_flat (hN k) hα (X k)
  have he : α^(s/2-1)*(ε/α^(s/2-1)) = ε := mul_div_cancel₀ _ hw.ne'
  unfold e8GaussianRieszProfileNeg8
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_integral_lower_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ}
    (hC : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1)) ≤ C) :
    (∫ α : ℝ in Ioi 0, e8GaussianRieszProfileNeg8 s α) ≤ C :=
  integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := e8GaussianRieszProfileNeg8 s) (M := fun _ => 0)
    (f := fun k α => α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1))
    (e8GaussianRieszProfileNeg8_integrable hs0)
    (fun k => sphereGaussianCenteredScaled8_neg_integrable hs hs0 (hN k) (X k))
    (integrable_zero _ _ _)
    (Eventually.of_forall (fun _ => le_refl 0))
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      have hα0 : (0:ℝ) < α := hα
      rw [neg_zero]
      exact mul_nonneg (Real.rpow_nonneg hα0.le _)
        (sphereGaussianCenteredScaled8_add_one_nonneg (hN k) hα0.le (X k)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_neg_profile_eventually s hN X hα (hp α hα))
    hC

theorem sphereRieszNegPrefactor8_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2) < 0 := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h2 : 0 < (sphereArea8.real univ)^(-(s/8)) := Real.rpow_pos_of_pos hA _
  exact div_neg_of_pos_of_neg (mul_pos h1 h2) (real_Gamma_neg_strip (by linarith) (by linarith))

theorem sphereGaussianSequence_energy_upper_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ} (hC : ∀ k, C ≤ normalizedEnergyNeg8 s (X k)) :
    C ≤ sphereRieszCoefficientNeg8 s := by
  have hK := sphereRieszNegPrefactor8_neg hs hs0
  set K := Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2) with hKdef
  have hi : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled8 α (X k)+1)) ≤
      C/K := by
    intro k
    rw [le_div_iff_of_neg hK, mul_comm]
    rw [← normalizedEnergyNeg8_gaussian_mellin hs hs0 (hN k) (X k)]
    exact hC k
  have h := sphereGaussianSequence_integral_lower_neg hs hs0 hN X hp hi
  rw [le_div_iff_of_neg hK] at h
  unfold sphereRieszCoefficientNeg8
  rw [← hKdef]
  linarith

/-- Universal sharp bound for every `-2 < s < 0` from the pointwise sharp sphere Gaussian
profile. -/
theorem sphere8_riesz_neg_upper_of_gaussian_profile (hp : SphereGaussianSharpProfileLower8)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, normalizedEnergyNeg8 s X ≤ sphereRieszCoefficientNeg8 s+η := by
  classical
  intro η hη
  by_contra h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : Configuration N, sphereRieszCoefficientNeg8 s+η < normalizedEnergyNeg8 s X := by
    intro k
    by_contra hk
    apply h
    refine ⟨k+1, fun N hN X => ?_⟩
    by_contra hX
    exact hk ⟨N, hN, X, lt_of_not_ge hX⟩
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  have hc := sphereGaussianSequence_energy_upper_neg hs hs0 hN0 X
    (hp N ht hN0 X) (fun k => (hX k).le)
  linarith

/-- The universal bound under the G8 input. -/
theorem sphere8_riesz_neg_upper_of_schwartz_input (hG8 : E8SharpGaussianSchwartzInput8)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, normalizedEnergyNeg8 s X ≤ sphereRieszCoefficientNeg8 s+η :=
  sphere8_riesz_neg_upper_of_gaussian_profile
    (sphereGaussianSharpProfileLower8_of_schwartz_input hG8) hs hs0

/-- The universal bound under the CKMRV Laplace–sine contract. -/
theorem sphere8_riesz_neg_upper_of_laplaceSineData (D : E8LaplaceSineData8)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, normalizedEnergyNeg8 s X ≤ sphereRieszCoefficientNeg8 s+η :=
  sphere8_riesz_neg_upper_of_schwartz_input
    (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩)) hs hs0

/-- The negative-exponent continuous constant is the actual double integral of `|x-y|^|s|`. -/
theorem sphereRieszConstNeg8_eq_pair_integral {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    sphereRieszConstNeg8 s =
      ∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
        ∂(sphereProbability8.prod sphereProbability8) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  set μ := sphereProbability8.prod sphereProbability8 with hμ
  set ν := volume.restrict (Ioi (0:ℝ)) with hν
  set f : Sphere8 × Sphere8 → ℝ → ℝ :=
    fun p t => t^(s/2-1)*(sphereGaussianKernel8 t p.1 p.2-1) with hf
  have hdom1 : IntegrableOn (fun t : ℝ => 4*(t^(s/2-1)*min t 1)) (Ioi 0) := by
    apply integrableOn_Ioi_of_rpow_min_bound (C := 4) (a := s/2) (by linarith) (by linarith)
    · intro t ht
      have ht0 : (0:ℝ) < t := ht
      exact (continuousAt_const.mul ((Real.continuousAt_rpow_const t (s/2-1)
        (Or.inl ht0.ne')).mul (continuous_id.min continuous_const).continuousAt)).continuousWithinAt
    · intro t ht
      have h0 : 0 ≤ 4*(t^(s/2-1)*min t 1) :=
        mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ht.le _)
          (le_min ht.le zero_le_one))
      rw [abs_of_nonneg h0]
  have hdom : Integrable (fun z : (Sphere8 × Sphere8) × ℝ => (1:ℝ)*(4*(z.2^(s/2-1)*min z.2 1)))
      (μ.prod ν) := Integrable.mul_prod (integrable_const (1:ℝ)) hdom1
  have hmeas : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun z : (Sphere8 × Sphere8) × ℝ => z.2^(s/2-1)) :=
      measurable_snd.pow_const _
    have h2 : Continuous (fun z : (Sphere8 × Sphere8) × ℝ =>
        Real.exp (-(z.2*(dist z.1.1 z.1.2)^2))-1) := by fun_prop
    exact h1.mul h2.measurable
  have hpos : ∀ᵐ z ∂(μ.prod ν), z.2 ∈ Ioi (0:ℝ) :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd)
      (ae_restrict_mem measurableSet_Ioi)
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hpos] with z hz
    have ht0 : (0:ℝ) < z.2 := hz
    have hd := sphere8_dist_le_two z.1.1 z.1.2
    have hd0 : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
    obtain ⟨hb1, hb2⟩ := one_sub_exp_neg_bounds
      (mul_nonneg ht0.le (sq_nonneg (dist z.1.1 z.1.2)))
    have hw : 0 ≤ z.2^(s/2-1) := Real.rpow_nonneg ht0.le _
    have hd2 : (dist z.1.1 z.1.2)^2 ≤ 4 := by nlinarith
    have hm : min (z.2*(dist z.1.1 z.1.2)^2) 1 ≤ 4*min z.2 1 := by
      rcases le_total z.2 1 with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hd2 ht0.le])
      · rw [min_eq_right h]
        linarith [min_le_right (z.2*(dist z.1.1 z.1.2)^2) 1]
    change ‖z.2^(s/2-1)*(Real.exp (-(z.2*(dist z.1.1 z.1.2)^2))-1)‖ ≤
      1*(4*(z.2^(s/2-1)*min z.2 1))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub,
      one_mul]
    calc z.2^(s/2-1)*(1-Real.exp (-(z.2*(dist z.1.1 z.1.2)^2)))
        ≤ z.2^(s/2-1)*(4*min z.2 1) := mul_le_mul_of_nonneg_left (hb2.trans hm) hw
      _ = 4*(z.2^(s/2-1)*min z.2 1) := by ring
  have hswap := integral_integral_swap hint
  have hleft : (∫ p, (∫ t, f p t ∂ν) ∂μ) =
      Real.Gamma (s/2)*∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    exact (sphereGaussianPair8_mellin_neg hs hs0 p.1 p.2).2
  have hright : (∫ t, (∫ p, f p t ∂μ) ∂ν) =
      ∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianBackground8 t-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    simp only [hf]
    rw [integral_const_mul, integral_sub (sphereGaussianKernel8_pair_integrable ht0)
      (integrable_const (1:ℝ))]
    simp [sphereGaussianBackground8]
  rw [hleft, hright] at hswap
  unfold sphereRieszConstNeg8
  rw [← hswap]
  field_simp

/-- Conjecture form of the universal sharp bound for `-2 < s < 0` with the actual double
integral and the explicit E8 Epstein coefficient, under the CKMRV Laplace–sine contract. -/
theorem sphere8_riesz_neg_upper_conjecture_form (D : E8LaplaceSineData8) {s : ℝ}
    (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere8_riesz_neg_upper_of_laplaceSineData D hs hs0 η hη
  refine ⟨N₀, fun N hN X => ?_⟩
  have hX := h N hN X
  rwa [normalizedEnergyNeg8, sphereRieszConstNeg8_eq_pair_integral hs hs0,
    sphereRieszCoefficientNeg8_eq_epstein hs hs0] at hX

/-- The same statement in the Brauchart–Hardin–Saff sign convention `k_s = sgn(s) r^(-s)`:
the minimal signed energy `-Σ_{i≠j} |x_i-x_j|^|s|` is at least
`-I_s N² - (A₈^(-s/8) Re ζ_E8(s) + η) N^(1+s/8)` for all large `N` and all configurations. -/
theorem sphere8_riesz_neg_signed_lower_conjecture_form (D : E8LaplaceSineData8) {s : ℝ}
    (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      -((sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re)-η ≤
        (-energyRpow s X-(-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8)))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere8_riesz_neg_upper_conjecture_form D hs hs0 η hη
  refine ⟨N₀, fun N hN X => ?_⟩
  have hX := h N hN X
  have he : (-energyRpow s X-(-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8)))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) =
      -((energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8)) := by
    rw [← neg_div]
    congr 1
    ring
  rw [he]
  linarith

#print axioms sphereGaussianCenteredScaled8_neg_profile_eventually
#print axioms sphereGaussianSequence_integral_lower_neg
#print axioms sphereRieszNegPrefactor8_neg
#print axioms sphereGaussianSequence_energy_upper_neg
#print axioms sphere8_riesz_neg_upper_of_gaussian_profile
#print axioms sphere8_riesz_neg_upper_of_schwartz_input
#print axioms sphere8_riesz_neg_upper_of_laplaceSineData
#print axioms sphereRieszConstNeg8_eq_pair_integral
#print axioms sphere8_riesz_neg_upper_conjecture_form
#print axioms sphere8_riesz_neg_signed_lower_conjecture_form

end SphericalRiesz
