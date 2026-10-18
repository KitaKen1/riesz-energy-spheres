import Riesz.SphereGaussianPolynomial8
import Riesz.SphereGaussianCommonLower8
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A genuine N-independent integrable common lower for every 0<s<8.
The scale and the background are the actual unit-sphere ones. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def sphereGaussianScale8 (N : ℕ) (α : ℝ) : ℝ :=
  Real.pi*α*((N:ℝ)/sphereArea8.real univ)^(1/4:ℝ)

theorem sphereGaussianScale8_pos {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    0 < sphereGaussianScale8 N α := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  unfold sphereGaussianScale8
  positivity

theorem sphereGaussianScale8_pow_four {N : ℕ} (hN : 0 < N) (α : ℝ) :
    (sphereGaussianScale8 N α)^4 = Real.pi^4*α^4*((N:ℝ)/sphereArea8.real univ) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hρ : 0 ≤ (N:ℝ)/sphereArea8.real univ := (div_pos hNR hA).le
  have hp : (((N:ℝ)/sphereArea8.real univ)^(1/4:ℝ))^4 =
      (N:ℝ)/sphereArea8.real univ := by
    rw [← Real.rpow_mul_natCast hρ]
    norm_num
  simp only [sphereGaussianScale8, mul_pow, hp]

theorem sphereGaussianBackground8_scaled_cap {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) :
    (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) ≤ (α^4)⁻¹ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have h := mul_le_mul_of_nonneg_left
    (sphereGaussianBackground8_area_decay (sphereGaussianScale8_pos hN hα)) hNR.le
  calc
    _ ≤ (N:ℝ)*(Real.pi^4/sphereArea8.real univ)/(sphereGaussianScale8 N α)^4 := by
      simpa only [mul_div_assoc] using h
    _ = _ := by
      rw [sphereGaussianScale8_pow_four hN]
      field_simp [Real.pi_pos.ne',hA.ne',hNR.ne',hα.ne']

theorem sphereGaussianCentered8_scaled_common_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : Configuration N) :
    -min 1 ((α^4)⁻¹) ≤
      (∑ i, ∑ j, sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) - 1 :=
  sphereGaussianCentered8_common_lower_of_bound hN (sphereGaussianScale8_pos hN hα).le X _
    (sphereGaussianBackground8_scaled_cap hN hα)

/-- A one-sided background replacement; no background asymptotic is a premise. -/
theorem sphereGaussianCentered8_flat_baseline_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : Configuration N) :
    (∑ i, ∑ j, sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))/(N:ℝ) -
        (α^4)⁻¹ - 1 ≤
      (∑ i, ∑ j, sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) - 1 := by
  linarith [sphereGaussianBackground8_scaled_cap hN hα]

def sphereGaussianMajorant8 (s α : ℝ) : ℝ := α^(s/2-1)*min 1 ((α^4)⁻¹)

theorem sphereGaussianMajorant8_small (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    sphereGaussianMajorant8 s α = α^(s/2-1) := by
  have hp : (0:ℝ) < α^4 := pow_pos hα _
  have hle : α^4 ≤ 1 := pow_le_one₀ hα.le hα1
  rw [sphereGaussianMajorant8, min_eq_left ((one_le_inv₀ hp).mpr hle), mul_one]

theorem sphereGaussianMajorant8_large (s : ℝ) {α : ℝ} (hα1 : 1 ≤ α) :
    sphereGaussianMajorant8 s α = α^(s/2-5) := by
  have hα : 0 < α := lt_of_lt_of_le zero_lt_one hα1
  have hp : (0:ℝ) < α^4 := pow_pos hα _
  have hle : 1 ≤ α^4 := one_le_pow₀ hα1
  have hpow : α^(s/2-5) = α^(s/2-1)*(α^4)⁻¹ := by
    have he : s/2-5 = (s/2-1)-(4:ℝ) := by ring
    rw [he,Real.rpow_sub hα,Real.rpow_ofNat,div_eq_mul_inv]
  rw [sphereGaussianMajorant8,min_eq_right ((inv_le_one₀ hp).mpr hle),hpow]

theorem sphereGaussianMajorant8_nonneg (s : ℝ) {α : ℝ} (hα : 0 < α) :
    0 ≤ sphereGaussianMajorant8 s α := by
  unfold sphereGaussianMajorant8
  exact mul_nonneg (Real.rpow_nonneg hα.le _) (le_min zero_le_one (by positivity))

theorem sphereGaussianMajorant8_integrable {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    IntegrableOn (sphereGaussianMajorant8 s) (Ioi 0) := by
  have hsmall : IntegrableOn (fun α : ℝ => α^(s/2-1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  have hlarge : IntegrableOn (fun α : ℝ => α^(s/2-5)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hi := ((hsmall.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi (0:ℝ))).add
    ((hlarge.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi (0:ℝ)))
  apply hi.congr
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1:ℝ)) :
      ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ∈ ({1}:Set ℝ)ᶜ)
    intro α hα
    simpa using hα
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with α hα hne1
  have hα0 : 0 < α := hα
  simp only [Pi.add_apply]
  rcases lt_or_gt_of_ne hne1 with hsmall | hlarge
  · rw [sphereGaussianMajorant8_small s hα0 hsmall.le,
      indicator_of_mem (show α ∈ Ioo 0 1 from ⟨hα0,hsmall⟩),
      indicator_of_notMem (show α ∉ Ioi 1 by simpa using hsmall.le)]
    simp
  · rw [sphereGaussianMajorant8_large s hlarge.le,
      indicator_of_notMem (notMem_Ioo_of_ge hlarge.le),
      indicator_of_mem (show α ∈ Ioi 1 from hlarge)]
    simp

theorem sphereGaussianCentered8_weighted_common_lower {N : ℕ} (hN : 0 < N)
    (s : ℝ) {α : ℝ} (hα : 0 < α) (X : Configuration N) :
    -sphereGaussianMajorant8 s α ≤ α^(s/2-1)*
      ((∑ i, ∑ j, sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) - 1) := by
  have h := mul_le_mul_of_nonneg_left (sphereGaussianCentered8_scaled_common_lower hN hα X)
    (Real.rpow_nonneg hα.le (s/2-1))
  simpa only [sphereGaussianMajorant8,mul_neg] using h

end SphericalRiesz
