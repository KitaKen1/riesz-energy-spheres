import E8Leech.SchwartzFourierLP
import E8Leech.GaussianParameterNormalization
import E8Leech.GaussianPotentialMixtures
import E8Leech.LeechGeometry

/-!
# Positive origin slack without a modular special-value formula

The user-supplied paper proof, Section 2.1, proposes inversion + positivity +
lattice calibration + Gaussian duality. Inversion and the single-vector
lattice lower bound are proved here for the actual Mathlib Fourier transform
and actual local Gaussian energy. Calibration and duality for the actual
CKMRV auxiliary family remain explicit hypotheses, not imported axioms.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform

theorem schwartzMap_origin_re_eq_integral_fourier {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0) :
    (f 0).re = ∫ ξ, (𝓕 f ξ).re := by
  have h := congrArg Complex.re (inverseSpectralKernel_fourier_schwartzMap_re f him 0)
  simp only [inverseSpectralKernel, spectralPhase_zero, mul_one] at h
  rw [integral_complex_ofReal, Complex.ofReal_re] at h
  exact h.symm

theorem schwartzMap_origin_re_nonneg_of_fourier_nonneg {d : ℕ}
    (f : 𝓢(Ambient d, ℂ)) (him : ∀ ξ, (𝓕 f ξ).im = 0)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re) : 0 ≤ (f 0).re := by
  rw [schwartzMap_origin_re_eq_integral_fourier f him]
  exact integral_nonneg_of_ae hnonneg

theorem fourier_origin_lower_of_calibration {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re) {L : ℝ}
    (hcalib : (𝓕 f (0 : Ambient d)).re - (f 0).re = L) :
    L ≤ (𝓕 f (0 : Ambient d)).re := by
  have h := schwartzMap_origin_re_nonneg_of_fourier_nonneg f him hnonneg
  linarith only [h, hcalib]

theorem origin_slack_lower_of_duality_calibration {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re) {L pref slack : ℝ}
    (hcalib : (𝓕 f (0 : Ambient d)).re - (f 0).re = L)
    (hpref : 0 ≤ pref) (hdual : slack = pref * (𝓕 f (0 : Ambient d)).re) :
    pref * L ≤ slack := by
  rw [hdual]
  exact mul_le_mul_of_nonneg_left (fourier_origin_lower_of_calibration f him hnonneg hcalib)
    hpref

theorem origin_slack_pos_of_duality_calibration {d : ℕ} (f : 𝓢(Ambient d, ℂ))
    (him : ∀ ξ, (𝓕 f ξ).im = 0)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 f ξ).re) {L pref slack : ℝ}
    (hcalib : (𝓕 f (0 : Ambient d)).re - (f 0).re = L)
    (hL : 0 < L) (hpref : 0 < pref) (hdual : slack = pref * (𝓕 f (0 : Ambient d)).re) :
    0 < slack :=
  (mul_pos hpref hL).trans_le
    (origin_slack_lower_of_duality_calibration f him hnonneg hcalib hpref.le hdual)

/-- One nonzero vector suffices; no theta series or shell enumeration is needed. -/
theorem gaussian_lattice_single_vector_lower {d : ℕ} {Λ : Set (Ambient d)}
    {β : ℝ} {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : latticePotentialEnergy Λ (gaussianPotential β) ≠ ∞) :
    gaussianKernel β z ≤ (latticePotentialEnergy Λ (gaussianPotential β)).toReal := by
  have h := ENNReal.le_tsum (f := fun y : Λ =>
    if (y : Ambient d) = 0 then 0 else gaussianPotential β 0 (y : Ambient d)) ⟨z, hz⟩
  change (if z = 0 then 0 else gaussianPotential β 0 z) ≤
    latticePotentialEnergy Λ (gaussianPotential β) at h
  simp only [if_neg hne, gaussianPotential, gaussianKernel, zero_sub, norm_neg] at h
  have ht := ENNReal.toReal_mono hfinite h
  simpa only [gaussianKernel, ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht

theorem gaussian_lattice_single_vector_uniform_lower {d : ℕ} {Λ : Set (Ambient d)}
    {β r : ℝ} {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0) (hnorm : ‖z‖ = r)
    (hβ : β ≤ 4 * Real.pi)
    (hfinite : latticePotentialEnergy Λ (gaussianPotential β) ≠ ∞) :
    Real.exp (-4 * Real.pi * r ^ 2) ≤
      (latticePotentialEnergy Λ (gaussianPotential β)).toReal := by
  apply le_trans _ (gaussian_lattice_single_vector_lower hz hne hfinite)
  unfold gaussianKernel
  rw [hnorm]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hβ (sq_nonneg r)]

theorem gaussian_dual_parameter_block_upper {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) : Real.pi ^ 2 / α ≤ 4 * Real.pi := by
  have h := mul_le_mul_of_nonneg_left (gaussian_dual_compact_interval hα).2 Real.pi_pos.le
  have he : Real.pi * (Real.pi / α) = Real.pi ^ 2 / α := by ring
  rw [he] at h
  nlinarith only [h]

theorem e8_gaussian_lattice_compact_lower {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hfinite : latticePotentialEnergy e8Set (gaussianPotential (Real.pi ^ 2 / α)) ≠ ∞) :
    Real.exp (-8 * Real.pi) ≤
      (latticePotentialEnergy e8Set (gaussianPotential (Real.pi ^ 2 / α))).toReal := by
  obtain ⟨z, hz, hne, hnorm⟩ := e8Set_minimum_attained
  have h := gaussian_lattice_single_vector_uniform_lower hz hne hnorm
    (gaussian_dual_parameter_block_upper hα) hfinite
  simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    show -4 * Real.pi * 2 = -8 * Real.pi by ring] using h

theorem leech_gaussian_lattice_compact_lower {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hfinite : latticePotentialEnergy leechSet (gaussianPotential (Real.pi ^ 2 / α)) ≠ ∞) :
    Real.exp (-16 * Real.pi) ≤
      (latticePotentialEnergy leechSet (gaussianPotential (Real.pi ^ 2 / α))).toReal := by
  obtain ⟨z, hz, hne, hnorm⟩ := leechSet_minimum_attained
  have h := gaussian_lattice_single_vector_uniform_lower hz hne hnorm
    (gaussian_dual_parameter_block_upper hα) hfinite
  simpa only [show -4 * Real.pi * (2 : ℝ) ^ 2 = -16 * Real.pi by ring] using h

theorem origin_slack_compact_lower {d : ℕ} {Λ : Set (Ambient d)}
    (f : ℝ → 𝓢(Ambient d, ℂ)) {α r : ℝ} (m : ℕ) {z : Ambient d}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hz : z ∈ Λ) (hne : z ≠ 0) (hnorm : ‖z‖ = r)
    (him : ∀ ξ, (𝓕 (f (Real.pi ^ 2 / α)) ξ).im = 0)
    (hnonneg : ∀ᵐ ξ ∂volume, 0 ≤ (𝓕 (f (Real.pi ^ 2 / α)) ξ).re)
    (hfinite : latticePotentialEnergy Λ (gaussianPotential (Real.pi ^ 2 / α)) ≠ ∞)
    (hcalib : (𝓕 (f (Real.pi ^ 2 / α)) (0 : Ambient d)).re -
      (f (Real.pi ^ 2 / α) 0).re =
      (latticePotentialEnergy Λ (gaussianPotential (Real.pi ^ 2 / α))).toReal)
    (hdual : gaussianKernel α (0 : Ambient d) - (f α 0).re =
      (Real.pi / α) ^ m * (𝓕 (f (Real.pi ^ 2 / α)) (0 : Ambient d)).re) :
    3 ^ m * Real.exp (-4 * Real.pi * r ^ 2) ≤ gaussianKernel α (0 : Ambient d) - (f α 0).re := by
  have ha := gaussian_compact_interval_pos hα
  have hL := gaussian_lattice_single_vector_uniform_lower hz hne hnorm
    (gaussian_dual_parameter_block_upper hα) hfinite
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
    (gaussian_dual_compact_interval hα).1 m
  have hl := origin_slack_lower_of_duality_calibration (f (Real.pi ^ 2 / α)) him hnonneg
    hcalib (by positivity : 0 ≤ (Real.pi / α) ^ m) hdual
  exact (mul_le_mul hp hL (Real.exp_pos _).le (by positivity)).trans hl

end E8Leech
