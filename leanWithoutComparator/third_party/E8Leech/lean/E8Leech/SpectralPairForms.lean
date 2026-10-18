import E8Leech.SpectralFiniteForms

/-!
# Finite-window spectral positivity and diagonal removal

The real part of an inverse transform of a nonnegative integrable density has a
nonnegative finite pair form. Local finiteness identifies that form with the
actual point-process double integral. The original finite Riesz energy supplies
expectation integrability; no independent second-moment hypothesis is added.
The resulting off-diagonal bound is the finite-window diagonal correction only,
not the sharp stationary zero-frequency lower bound.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def realSpectralKernel {d : ℕ} (ν : Measure (Ambient d)) (g : Ambient d → ℝ)
    (x : Ambient d) : ℝ :=
  (inverseSpectralKernel ν g x).re

theorem continuous_realSpectralKernel {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) : Continuous (realSpectralKernel ν g) :=
  Complex.continuous_re.comp (continuous_inverseSpectralKernel ν g hg)

@[simp] theorem realSpectralKernel_zero {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) : realSpectralKernel ν g 0 = ∫ ξ, g ξ ∂ν := by
  simp only [realSpectralKernel, inverseSpectralKernel_zero, Complex.ofReal_re]

theorem continuous_realSpectralKernel_difference {d : ℕ} (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) :
    Continuous (Function.uncurry (fun x y => realSpectralKernel ν g (x - y))) :=
  (continuous_realSpectralKernel ν g hg).comp (continuous_fst.sub continuous_snd)

theorem finite_real_spectral_pair_eq_integral_square {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (S : Finset (Ambient d)) :
    (∑ x ∈ S, ∑ y ∈ S, realSpectralKernel ν g (x - y)) =
      ∫ ξ, g ξ * Complex.normSq (∑ x ∈ S, spectralPhase ξ x) ∂ν := by
  have he := congrArg Complex.re
    (finite_spectral_quadratic_eq_integral_normSq ν g hg S id (fun _ => 1))
  simpa only [Complex.re_sum, map_one, one_mul, mul_one, id_eq,
    realSpectralKernel, Complex.ofReal_re] using he

theorem finite_real_spectral_pair_nonneg {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ) (S : Finset (Ambient d)) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S, realSpectralKernel ν g (x - y) := by
  rw [finite_real_spectral_pair_eq_integral_square ν g hg S]
  apply integral_nonneg_of_ae
  filter_upwards [hgnonneg] with ξ hξ
  exact mul_nonneg hξ (Complex.normSq_nonneg _)

theorem realLocalized_spectral_pair_eq_integral_square {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (c : Configuration (Ambient d)) {W : Set (Ambient d)}
    (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W =
      ∫ ξ, g ξ * Complex.normSq
        (∑ x ∈ windowPointFinset c W hbW, spectralPhase ξ x) ∂ν := by
  rw [realLocalizedPairIntegral_eq_sum _ c hW hbW hW hbW]
  exact finite_real_spectral_pair_eq_integral_square ν g hg _

theorem realLocalized_spectral_pair_nonneg {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    0 ≤ realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y)) c W W := by
  rw [realLocalizedPairIntegral_eq_sum _ c hW hbW hW hbW]
  exact finite_real_spectral_pair_nonneg ν g hg hgnonneg _

theorem realLocalized_spectral_offDiagonal_lower {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℝ) (hg : Integrable g ν)
    (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ) (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    -(∫ ξ, g ξ ∂ν) * (c.count W).toReal ≤
      realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c W W := by
  have hp := realLocalized_spectral_pair_nonneg ν g hg hgnonneg c hW hbW
  rw [realLocalizedPairIntegral_difference_split _ c hW hbW,
    realSpectralKernel_zero] at hp
  linarith

theorem integrable_realLocalized_spectral_pair_of_riesz {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν)
    {W : Set (Ambient d)} (hW : MeasurableSet W) (hbW : Bornology.IsBounded W) :
    Integrable (fun c => realLocalizedPairIntegral
      (fun x y => realSpectralKernel ν g (x - y)) c W W) μ :=
  integrable_realLocalizedPairIntegral_of_continuous hs μ hμ ρ hρ hρtop henergy _
    (continuous_realSpectralKernel_difference ν g hg) hW hbW hW hbW

theorem integrable_realLocalized_spectral_unit_offDiagonal_of_riesz
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) :
    Integrable (fun c => realLocalizedPairIntegral
      (fun x y => if y = x then 0 else realSpectralKernel ν g (x - y))
      c (unitWindow d) (unitWindow d)) μ := by
  have hfull := integrable_realLocalized_spectral_pair_of_riesz hs μ hμ ρ hρ hρtop
    henergy ν g hg (measurable_unitWindow d) (isBounded_unitWindow d)
  have hdiag := integrable_realLocalizedPairIntegral_unit_diagonal μ ρ hρ hρtop (∫ ξ, g ξ ∂ν)
  apply (hfull.sub hdiag).congr
  filter_upwards with c
  simp only [Pi.sub_apply]
  rw [realLocalizedPairIntegral_difference_split _ c (measurable_unitWindow d)
    (isBounded_unitWindow d), realSpectralKernel_zero,
    realLocalizedPairIntegral_const_diagonal _ c (measurable_unitWindow d)
      (isBounded_unitWindow d)]
  simp

theorem integral_realLocalized_spectral_unit_diagonal_split
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) :
    (∫ c, realLocalizedPairIntegral (fun x y => realSpectralKernel ν g (x - y))
      c (unitWindow d) (unitWindow d) ∂μ) =
    (∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
      else realSpectralKernel ν g (x - y)) c (unitWindow d) (unitWindow d) ∂μ) +
        (∫ ξ, g ξ ∂ν) * ρ.toReal := by
  have hoff := integrable_realLocalized_spectral_unit_offDiagonal_of_riesz
    hs μ hμ ρ hρ hρtop henergy ν g hg
  have hdiag := integrable_realLocalizedPairIntegral_unit_diagonal μ ρ hρ hρtop (∫ ξ, g ξ ∂ν)
  calc
    _ = ∫ c, (realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c (unitWindow d) (unitWindow d) +
        realLocalizedPairIntegral (fun x y => if y = x then (∫ ξ, g ξ ∂ν) else 0)
          c (unitWindow d) (unitWindow d)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with c
      rw [realLocalizedPairIntegral_difference_split _ c (measurable_unitWindow d)
        (isBounded_unitWindow d), realSpectralKernel_zero,
        realLocalizedPairIntegral_const_diagonal _ c (measurable_unitWindow d)
          (isBounded_unitWindow d)]
    _ = _ := by rw [integral_add hoff hdiag,
      integral_realLocalizedPairIntegral_unit_diagonal μ ρ hρ hρtop]

theorem integral_realLocalized_spectral_unit_offDiagonal_lower
    {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (henergy : rieszEnergy s μ ≠ ∞) (ν : Measure (Ambient d))
    (g : Ambient d → ℝ) (hg : Integrable g ν) (hgnonneg : ∀ᵐ ξ ∂ν, 0 ≤ g ξ) :
    -(∫ ξ, g ξ ∂ν) * ρ.toReal ≤
      ∫ c, realLocalizedPairIntegral (fun x y => if y = x then 0
        else realSpectralKernel ν g (x - y)) c (unitWindow d) (unitWindow d) ∂μ := by
  have hp : 0 ≤ ∫ c, realLocalizedPairIntegral
      (fun x y => realSpectralKernel ν g (x - y)) c (unitWindow d) (unitWindow d) ∂μ :=
    integral_nonneg fun c => realLocalized_spectral_pair_nonneg ν g hg hgnonneg c
      (measurable_unitWindow d) (isBounded_unitWindow d)
  rw [integral_realLocalized_spectral_unit_diagonal_split
    hs μ hμ ρ hρ hρtop henergy ν g hg] at hp
  linarith

end E8Leech
