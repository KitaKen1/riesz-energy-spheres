import Riesz.SphereRieszMellinRpow8
import Riesz.E8CKMRVContract8

/-! Sharp lower bound for every exponent `0 < s < 8` on the actual unit S⁸ (stage HP, lower half).

The same pointwise sharp sphere Gaussian profile that closes `s = 4` gives, by the general Mellin
weight `α^(s/2-1)`, the existing configuration-uniform majorant and the generic Fatou truncation,
`liminf (E_s - I_s N²)/N^(1+s/8) ≥ C_s` uniformly over configurations, with
`C_s = π^(s/2) A₈^(-s/8)/Γ(s/2) * ∫ α^(s/2-1)(Θ_E8(α) - α⁻⁴ - 1) dα`.
Consequently the bound holds under the G8 input and under the CKMRV Laplace–sine contract.
At `s = 4` the constant is `predictedCoefficient`. Identifying `C_s` with the Epstein value
`A₈^(-s/8) * 240 * 2^(-s/2) ζ(s/2) ζ(s/2-3)` and the matching upper bound are separate. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The weighted E8 Gaussian profile `α^(s/2-1)(Θ(α) - α⁻⁴ - 1)`. -/
def e8GaussianRieszProfileRpow8 (s α : ℝ) : ℝ :=
  α^(s/2-1)*(e8GaussianThetaReal8 α-(α^4)⁻¹-1)

theorem e8GaussianRieszProfileRpow8_eq_re (s : ℝ) {α : ℝ} (hα : 0 < α) :
    e8GaussianRieszProfileRpow8 s α =
      ((α:ℂ)^(((s/2:ℝ):ℂ)-1) • e8ThetaRegularized α).re := by
  have hc : (α:ℂ)^(((s/2:ℝ):ℂ)-1) = ((α^(s/2-1):ℝ):ℂ) := by
    rw [Complex.ofReal_cpow hα.le]
    push_cast
    ring_nf
  rw [hc, smul_eq_mul, Complex.re_ofReal_mul]
  simp only [e8GaussianRieszProfileRpow8, e8GaussianThetaReal8, e8ThetaRegularized, e8ThetaTail,
    Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re]
  ring

theorem e8GaussianRieszProfileRpow8_integrable {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    IntegrableOn (e8GaussianRieszProfileRpow8 s) (Ioi 0) := by
  have h := e8ThetaRegularized_mellinConvergent (s := ((s/2:ℝ):ℂ))
    (by simp; linarith) (by simp; linarith)
  have hre := h.re
  apply hre.congr_fun _ measurableSet_Ioi
  intro α hα
  exact (e8GaussianRieszProfileRpow8_eq_re s hα).symm

theorem e8GaussianRieszProfileRpow8_four (α : ℝ) :
    e8GaussianRieszProfileRpow8 4 α = e8GaussianRieszProfile8 α := by
  rw [e8GaussianRieszProfileRpow8, e8GaussianRieszProfile8, show (4:ℝ)/2-1 = 1 by norm_num,
    Real.rpow_one]

/-- The conjectured second-order coefficient for exponent `s`, as a Gaussian profile integral. -/
def sphereRieszCoefficient8 (s : ℝ) : ℝ :=
  (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
    ∫ α : ℝ in Ioi 0, e8GaussianRieszProfileRpow8 s α

theorem sphereRieszCoefficient8_four : sphereRieszCoefficient8 4 = predictedCoefficient := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  rw [predictedCoefficient_eq_gaussian_profile_factor, sphereRieszCoefficient8]
  have hint : (∫ α : ℝ in Ioi 0, e8GaussianRieszProfileRpow8 4 α) = -5/6 := by
    rw [← e8GaussianRieszProfile8_integral]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro α _
    exact e8GaussianRieszProfileRpow8_four α
  have hΓ : Real.Gamma (4/2) = 1 := by norm_num
  have hpi : Real.pi^((4:ℝ)/2) = Real.pi^2 := by
    rw [show (4:ℝ)/2 = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hsq : (sphereArea8.real univ)^(-((4:ℝ)/8)) = (Real.sqrt (sphereArea8.real univ))⁻¹ := by
    rw [Real.rpow_neg hA.le, Real.sqrt_eq_rpow, show (4:ℝ)/8 = 1/2 by norm_num]
  rw [hint, hΓ, hpi, hsq, div_one]
  ring

theorem sphereGaussianCenteredScaled8_weighted_lower_rpow {N : ℕ} (hN : 0 < N)
    (s : ℝ) {α : ℝ} (hα : 0 < α) (X : Configuration N) :
    -sphereGaussianMajorant8 s α ≤ α^(s/2-1)*sphereGaussianCenteredScaled8 α X := by
  simpa only [sphereGaussianCenteredScaled8] using
    sphereGaussianCentered8_weighted_common_lower hN s hα X

theorem sphereGaussianCenteredScaled8_weighted_profile_eventually_rpow (s : ℝ)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianRieszProfileRpow8 s α-ε ≤ α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k) := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  filter_upwards [hp (ε/α^(s/2-1)) (div_pos hε hw)] with k hk
  have hb := sphereGaussianCenteredScaled8_ge_flat (hN k) hα (X k)
  have he : α^(s/2-1)*(ε/α^(s/2-1)) = ε := mul_div_cancel₀ _ hw.ne'
  unfold e8GaussianRieszProfileRpow8
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_integral_lower_of_profile_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ}
    (hC : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) ≤ C) :
    (∫ α : ℝ in Ioi 0, e8GaussianRieszProfileRpow8 s α) ≤ C :=
  integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := e8GaussianRieszProfileRpow8 s) (M := sphereGaussianMajorant8 s)
    (f := fun k α => α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k))
    (e8GaussianRieszProfileRpow8_integrable hs hs8)
    (fun k => sphereGaussianCenteredScaled8_weighted_integrable_rpow hs hs8 (hN k) (X k))
    (sphereGaussianMajorant8_integrable hs hs8)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianMajorant8_nonneg s hα)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_weighted_lower_rpow (hN k) s hα (X k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_weighted_profile_eventually_rpow s hN X hα (hp α hα))
    hC

theorem sphereGaussianSequence_energy_bound_of_profile_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ} (hC : ∀ k, normalizedEnergyRpow s (X k) ≤ C) :
    sphereRieszCoefficient8 s ≤ C := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have hc : 0 < Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2) := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < (sphereArea8.real univ)^(-(s/8)) := Real.rpow_pos_of_pos hA _
    positivity
  have hi : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) ≤
      C/(Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2)) := by
    intro k
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm, ← normalizedEnergyRpow_gaussian_mellin hs hs8 (hN k) (X k)]
    exact hC k
  have h := sphereGaussianSequence_integral_lower_of_profile_rpow hs hs8 hN X hp hi
  unfold sphereRieszCoefficient8
  have hh := mul_le_mul_of_nonneg_left h hc.le
  rwa [mul_div_cancel₀ C hc.ne'] at hh

/-- Uniform sharp lower bound for every exponent `0 < s < 8`, from the pointwise sharp sphere
Gaussian profile. -/
theorem sphere8_riesz_sharp_lower_of_gaussian_profile_rpow (hp : SphereGaussianSharpProfileLower8)
    {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, sphereRieszCoefficient8 s-η ≤ normalizedEnergyRpow s X := by
  classical
  intro η hη
  by_contra h
  push_neg at h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : Configuration N, normalizedEnergyRpow s X < sphereRieszCoefficient8 s-η :=
    fun k => h (k+1)
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  have hc := sphereGaussianSequence_energy_bound_of_profile_rpow hs hs8 hN0 X
    (hp N ht hN0 X) (fun k => (hX k).le)
  linarith

/-- The all-exponent sharp lower bound under the G8 input. -/
theorem sphere8_riesz_sharp_lower_of_schwartz_input (hG8 : E8SharpGaussianSchwartzInput8)
    {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, sphereRieszCoefficient8 s-η ≤ normalizedEnergyRpow s X :=
  sphere8_riesz_sharp_lower_of_gaussian_profile_rpow
    (sphereGaussianSharpProfileLower8_of_schwartz_input hG8) hs hs8

/-- The all-exponent sharp lower bound under the CKMRV Laplace–sine contract. -/
theorem sphere8_riesz_sharp_lower_of_laplaceSineData (D : E8LaplaceSineData8)
    {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, sphereRieszCoefficient8 s-η ≤ normalizedEnergyRpow s X :=
  sphere8_riesz_sharp_lower_of_schwartz_input
    (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩)) hs hs8

#print axioms e8GaussianRieszProfileRpow8_eq_re
#print axioms e8GaussianRieszProfileRpow8_integrable
#print axioms e8GaussianRieszProfileRpow8_four
#print axioms sphereRieszCoefficient8_four
#print axioms sphereGaussianCenteredScaled8_weighted_lower_rpow
#print axioms sphereGaussianCenteredScaled8_weighted_profile_eventually_rpow
#print axioms sphereGaussianSequence_integral_lower_of_profile_rpow
#print axioms sphereGaussianSequence_energy_bound_of_profile_rpow
#print axioms sphere8_riesz_sharp_lower_of_gaussian_profile_rpow
#print axioms sphere8_riesz_sharp_lower_of_schwartz_input
#print axioms sphere8_riesz_sharp_lower_of_laplaceSineData

end SphericalRiesz
