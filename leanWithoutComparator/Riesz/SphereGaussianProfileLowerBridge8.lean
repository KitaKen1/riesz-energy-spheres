import Riesz.RealFatouTruncation
import Riesz.E8GaussianRealProfile8
import Riesz.SphereGaussianMellinScale8
import Riesz.SphereSharpUpperAllN8

/-! The actual one-sided integral bridge from a sharp sphere Gaussian profile
to the original inverse-fourth energy. The pointwise sharp Gaussian premise
is explicit and remains unproved; this file is not an unconditional target. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

def sphereGaussianFullScaled8 {N : ℕ} (α : ℝ) (X : Configuration N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N,
    sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))/(N:ℝ)

/-- This is the missing actual sphere localization output, not a supplied axiom. -/
def SphereGaussianSharpProfileLower8 : Prop :=
  ∀ (N : ℕ → ℕ), Tendsto N atTop atTop → (∀ k, 0 < N k) →
    ∀ (X : ∀ k, Configuration (N k)) (α : ℝ), 0 < α →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k)

theorem sphereGaussianCenteredScaled8_ge_flat {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : Configuration N) :
    sphereGaussianFullScaled8 α X-(α^4)⁻¹-1 ≤ sphereGaussianCenteredScaled8 α X :=
  sphereGaussianCentered8_flat_baseline_lower hN hα X

theorem sphereGaussianCenteredScaled8_weighted_profile_eventually
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianRieszProfile8 α-ε ≤ α*sphereGaussianCenteredScaled8 α (X k) := by
  intro ε hε
  filter_upwards [hp (ε/α) (div_pos hε hα)] with k hk
  have hb := sphereGaussianCenteredScaled8_ge_flat (hN k) hα (X k)
  have he : α*(ε/α) = ε := mul_div_cancel₀ _ hα.ne'
  unfold e8GaussianRieszProfile8
  nlinarith [mul_le_mul_of_nonneg_left hk hα.le,mul_le_mul_of_nonneg_left hb hα.le]

theorem sphereGaussianSequence_integral_lower_of_profile
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ}
    (hC : ∀ k, (∫ α : ℝ in Ioi 0, α*sphereGaussianCenteredScaled8 α (X k)) ≤ C) :
    -5/6 ≤ C := by
  have h := integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := e8GaussianRieszProfile8) (M := sphereGaussianMajorant8 4)
    (f := fun k α => α*sphereGaussianCenteredScaled8 α (X k))
    e8GaussianRieszProfile8_integrable
    (fun k => sphereGaussianCenteredScaled8_weighted_integrable (hN k) (X k))
    (sphereGaussianMajorant8_integrable (s := 4) (by norm_num) (by norm_num))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianMajorant8_nonneg 4 hα)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_weighted_lower (hN k) hα (X k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_weighted_profile_eventually hN X hα (hp α hα))
    hC
  rwa [e8GaussianRieszProfile8_integral] at h

theorem predictedCoefficient_eq_gaussian_profile_factor :
    predictedCoefficient = (Real.pi^2/Real.sqrt (sphereArea8.real univ))*(-5/6:ℝ) := by
  rw [predictedCoefficient_area_normalization]
  ring

theorem sphereGaussianSequence_energy_bound_of_profile
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ} (hC : ∀ k, normalizedEnergy (X k) ≤ C) :
    predictedCoefficient ≤ C := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hc : 0 < Real.pi^2/Real.sqrt (sphereArea8.real univ) := by positivity
  have hi : ∀ k, (∫ α : ℝ in Ioi 0, α*sphereGaussianCenteredScaled8 α (X k)) ≤
      C/(Real.pi^2/Real.sqrt (sphereArea8.real univ)) := by
    intro k
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm,← normalizedEnergy_gaussian_mellin_four (hN k) (X k)]
    exact hC k
  have h := sphereGaussianSequence_integral_lower_of_profile hN X hp hi
  rw [predictedCoefficient_eq_gaussian_profile_factor]
  have hh := mul_le_mul_of_nonneg_left h hc.le
  rwa [mul_div_cancel₀ C hc.ne'] at hh

theorem sphere8_inverse_fourth_sharp_lower_of_gaussian_profile
    (hp : SphereGaussianSharpProfileLower8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, predictedCoefficient-η ≤ normalizedEnergy X := by
  classical
  intro η hη
  by_contra h
  push_neg at h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : Configuration N, normalizedEnergy X < predictedCoefficient-η :=
    fun k => h (k+1)
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  have hc := sphereGaussianSequence_energy_bound_of_profile hN0 X
    (hp N ht hN0 X) (fun k => (hX k).le)
  linarith

theorem S8s4Target_of_gaussian_profile (hp : SphereGaussianSharpProfileLower8) : S8s4Target :=
  S8s4Target_of_sharp_lower (sphere8_inverse_fourth_sharp_lower_of_gaussian_profile hp)

end SphericalRiesz
