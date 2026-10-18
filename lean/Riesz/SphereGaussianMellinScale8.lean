import Riesz.SphereGaussianMellinEnergy8
import Riesz.SphereGaussianMajorant8
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual density-scale Mellin normalization and a coarse energy lower bound.
The coarse bound diagnoses the normalization; it does not give the sharp E8
coefficient or the main target. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def sphereGaussianDensityFactor8 (N : ℕ) : ℝ := sphereGaussianScale8 N 1

theorem sphereGaussianDensityFactor8_pos {N : ℕ} (hN : 0 < N) :
    0 < sphereGaussianDensityFactor8 N :=
  sphereGaussianScale8_pos hN zero_lt_one

theorem sphereGaussianScale8_eq_factor (N : ℕ) (α : ℝ) :
    sphereGaussianScale8 N α = sphereGaussianDensityFactor8 N*α := by
  unfold sphereGaussianDensityFactor8 sphereGaussianScale8
  ring

theorem sphereGaussianDensityFactor8_coefficient {N : ℕ} (hN : 0 < N) :
    (sphereGaussianDensityFactor8 N)^2/Real.sqrt (N:ℝ) =
      Real.pi^2/Real.sqrt (sphereArea8.real univ) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hρ : 0 ≤ (N:ℝ)/sphereArea8.real univ := (div_pos hNR hA).le
  have hp : (((N:ℝ)/sphereArea8.real univ)^(1/4:ℝ))^2 =
      Real.sqrt ((N:ℝ)/sphereArea8.real univ) := by
    rw [← Real.rpow_mul_natCast hρ, Real.sqrt_eq_rpow]
    norm_num
  simp only [sphereGaussianDensityFactor8,sphereGaussianScale8,mul_one,mul_pow,hp]
  rw [Real.sqrt_div hNR.le]
  field_simp [(Real.sqrt_pos.mpr hNR).ne',(Real.sqrt_pos.mpr hA).ne'] <;> ring

theorem sphereGaussianRieszDefect8_scaled_weighted_integrable {N : ℕ}
    (X : Configuration N) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun α : ℝ => α*sphereGaussianRieszDefect8 (c*α) X) (Ioi 0) := by
  have hi : IntegrableOn
      (fun α : ℝ => (c*α)*sphereGaussianRieszDefect8 (c*α) X) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => t*sphereGaussianRieszDefect8 t X) 0 hc).mpr
    simpa only [mul_zero] using sphereGaussianRieszDefect8_weighted_integrable X
  have hh : IntegrableOn
      (fun α : ℝ => c⁻¹*((c*α)*sphereGaussianRieszDefect8 (c*α) X)) (Ioi 0) :=
    hi.const_mul c⁻¹
  apply hh.congr_fun _ measurableSet_Ioi
  intro α _
  field_simp [hc.ne'] <;> ring

theorem sphereGaussianRieszDefect8_scaled_mellin_four {N : ℕ}
    (X : Configuration N) {c : ℝ} (hc : 0 < c) :
    c^2*(∫ α : ℝ in Ioi 0, α*sphereGaussianRieszDefect8 (c*α) X) =
      energy4 X-(7/16:ℝ)*(N:ℝ)^2 := by
  have h := integral_comp_mul_left_Ioi'
    (fun t : ℝ => t*sphereGaussianRieszDefect8 t X) 0 hc
  simp only [mul_zero,smul_eq_mul] at h
  have he : (fun α : ℝ => (c*α)*sphereGaussianRieszDefect8 (c*α) X) =
      (fun α : ℝ => c*(α*sphereGaussianRieszDefect8 (c*α) X)) := by
    ext α
    ring
  rw [he,integral_const_mul,sphereGaussianRieszDefect8_mellin_four] at h
  simpa only [pow_two,mul_assoc] using h

def sphereGaussianCenteredScaled8 {N : ℕ} (α : ℝ) (X : Configuration N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))/(N:ℝ)-
    (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α)-1

theorem sphereGaussianCenteredScaled8_defect {N : ℕ} (hN : 0 < N)
    (α : ℝ) (X : Configuration N) :
    sphereGaussianRieszDefect8 (sphereGaussianScale8 N α) X =
      (N:ℝ)*sphereGaussianCenteredScaled8 α X := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sphereGaussianRieszDefect8_eq_full]
  unfold sphereGaussianCenteredScaled8
  field_simp [hNR] <;> ring

theorem sphereGaussianCenteredScaled8_weighted_integrable {N : ℕ} (hN : 0 < N)
    (X : Configuration N) :
    IntegrableOn (fun α : ℝ => α*sphereGaussianCenteredScaled8 α X) (Ioi 0) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : IntegrableOn
      (fun α : ℝ => (N:ℝ)⁻¹*(α*sphereGaussianRieszDefect8 (sphereGaussianDensityFactor8 N*α) X))
      (Ioi 0) := (sphereGaussianRieszDefect8_scaled_weighted_integrable X
        (sphereGaussianDensityFactor8_pos hN)).const_mul (N:ℝ)⁻¹
  apply hi.congr_fun _ measurableSet_Ioi
  intro α _
  change (N:ℝ)⁻¹*(α*sphereGaussianRieszDefect8 (sphereGaussianDensityFactor8 N*α) X) =
    α*sphereGaussianCenteredScaled8 α X
  rw [← sphereGaussianScale8_eq_factor,sphereGaussianCenteredScaled8_defect hN]
  field_simp [hNR] <;> ring

theorem normalizedEnergy_gaussian_mellin_four {N : ℕ} (hN : 0 < N)
    (X : Configuration N) :
    normalizedEnergy X = (Real.pi^2/Real.sqrt (sphereArea8.real univ))*
      (∫ α : ℝ in Ioi 0, α*sphereGaussianCenteredScaled8 α X) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have h := sphereGaussianRieszDefect8_scaled_mellin_four X
    (sphereGaussianDensityFactor8_pos hN)
  have he : (fun α : ℝ => α*sphereGaussianRieszDefect8 (sphereGaussianDensityFactor8 N*α) X) =
      (fun α : ℝ => (N:ℝ)*(α*sphereGaussianCenteredScaled8 α X)) := by
    ext α
    rw [← sphereGaussianScale8_eq_factor,sphereGaussianCenteredScaled8_defect hN]
    ring
  rw [he,integral_const_mul] at h
  unfold normalizedEnergy
  rw [← h]
  calc
    _ = ((sphereGaussianDensityFactor8 N)^2/Real.sqrt (N:ℝ))*
        (∫ α : ℝ in Ioi 0, α*sphereGaussianCenteredScaled8 α X) := by
      field_simp [hNR.ne',(Real.sqrt_pos.mpr hNR).ne'] <;> ring
    _ = _ := by rw [sphereGaussianDensityFactor8_coefficient hN]

theorem sphereGaussianMajorant8_four_ae :
    sphereGaussianMajorant8 4 =ᵐ[volume.restrict (Ioi 0)]
      (fun α : ℝ => (Ioo 0 1).indicator (fun α : ℝ => α) α+
        (Ioi 1).indicator (fun α : ℝ => α^(-3:ℝ)) α) := by
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1:ℝ)) :
      ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ∈ ({1}:Set ℝ)ᶜ)
    intro α hα
    simpa using hα
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with α hα hne1
  have hα0 : 0 < α := hα
  rcases lt_or_gt_of_ne hne1 with hsmall | hlarge
  · rw [sphereGaussianMajorant8_small 4 hα0 hsmall.le,
      indicator_of_mem (show α ∈ Ioo 0 1 from ⟨hα0,hsmall⟩),
      indicator_of_notMem (show α ∉ Ioi 1 by simpa using hsmall.le)]
    norm_num
  · rw [sphereGaussianMajorant8_large 4 hlarge.le,
      indicator_of_notMem (notMem_Ioo_of_ge hlarge.le),
      indicator_of_mem (show α ∈ Ioi 1 from hlarge)]
    norm_num

theorem sphereGaussianMajorant8_four_integral :
    (∫ α : ℝ in Ioi 0, sphereGaussianMajorant8 4 α) = 1 := by
  have hs : IntegrableOn (fun α : ℝ => α) (Ioo 0 1) :=
    continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hl : IntegrableOn (fun α : ℝ => α^(-3:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hsmall : (∫ α : ℝ in Ioi 0, (Ioo 0 1).indicator (fun α : ℝ => α) α) = 1/2 := by
    rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le zero_le_one,
      integral_id]
    norm_num
  have hlarge : (∫ α : ℝ in Ioi 0, (Ioi 1).indicator (fun α : ℝ => α^(-3:ℝ)) α) = 1/2 := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1)),
      integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) zero_lt_one]
    norm_num
  rw [integral_congr_ae sphereGaussianMajorant8_four_ae,
    integral_add ((hs.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi 0))
      ((hl.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)),hsmall,hlarge]
  norm_num

theorem sphereGaussianCenteredScaled8_weighted_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : Configuration N) :
    -sphereGaussianMajorant8 4 α ≤ α*sphereGaussianCenteredScaled8 α X := by
  simpa only [show (4:ℝ)/2-1 = 1 by norm_num,Real.rpow_one,sphereGaussianCenteredScaled8]
    using sphereGaussianCentered8_weighted_common_lower hN 4 hα X

theorem sphereGaussianCenteredScaled8_integral_lower {N : ℕ} (hN : 0 < N)
    (X : Configuration N) :
    -1 ≤ ∫ α : ℝ in Ioi 0, α*sphereGaussianCenteredScaled8 α X := by
  have h := integral_mono_ae
    ((sphereGaussianMajorant8_integrable (s := 4) (by norm_num) (by norm_num)).neg)
    (sphereGaussianCenteredScaled8_weighted_integrable hN X)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_weighted_lower hN hα X)
  rw [integral_neg',sphereGaussianMajorant8_four_integral] at h
  exact h

theorem sphereGaussianArea8_coarse_coefficient :
    Real.pi^2/Real.sqrt (sphereArea8.real univ) = Real.sqrt 210/8 := by
  have h := predictedCoefficient_area_normalization
  unfold predictedCoefficient at h
  have he : (-5*Real.pi^2/6)/Real.sqrt (sphereArea8.real univ) =
      -(5/6:ℝ)*(Real.pi^2/Real.sqrt (sphereArea8.real univ)) := by ring
  rw [he] at h
  linarith

theorem normalizedEnergy_coarse_lower {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    -Real.sqrt 210/8 ≤ normalizedEnergy X := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have h := mul_le_mul_of_nonneg_left (sphereGaussianCenteredScaled8_integral_lower hN X)
    (by positivity : 0 ≤ Real.pi^2/Real.sqrt (sphereArea8.real univ))
  rw [← normalizedEnergy_gaussian_mellin_four hN X,sphereGaussianArea8_coarse_coefficient] at h
  simpa only [mul_neg_one,neg_div] using h

end SphericalRiesz
