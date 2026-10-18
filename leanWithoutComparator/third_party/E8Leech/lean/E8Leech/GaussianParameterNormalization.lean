import E8Leech.ComplexGaussianFourier

/-!
# Exact Gaussian parameters and a separated compact dual interval

The real Gaussian exp(-alpha * norm(x)^2) has upper-half-plane parameter
I * alpha / pi. Its Fourier dual parameter is I * pi / alpha.
On [pi/4, pi/3] the dual imaginary coordinate lies in [3,4], separated from
the positive Laplace block [1,2]. This arithmetic separation does not assert
that a modular j denominator has no zeros or removable singularities.
-/

noncomputable section

namespace E8Leech

open Set
open scoped FourierTransform

def gaussianUpperParameter (α : ℝ) : ℂ := Complex.I * (α / Real.pi : ℝ)

theorem gaussianUpperParameter_re (α : ℝ) : (gaussianUpperParameter α).re = 0 := by
  simp [gaussianUpperParameter]

theorem gaussianUpperParameter_im (α : ℝ) :
    (gaussianUpperParameter α).im = α / Real.pi := by
  simp [gaussianUpperParameter]

theorem gaussianUpperParameter_pos {α : ℝ} (hα : 0 < α) :
    0 < (gaussianUpperParameter α).im := by
  rw [gaussianUpperParameter_im]
  exact div_pos hα Real.pi_pos

theorem continuous_gaussianUpperParameter : Continuous gaussianUpperParameter := by
  unfold gaussianUpperParameter
  fun_prop

theorem upperGaussian_gaussianUpperParameter {d : ℕ} (α : ℝ) (x : Ambient d) :
    upperGaussian (gaussianUpperParameter α) x = (gaussianKernel α x : ℂ) := by
  rw [upperGaussian, gaussianUpperParameter, gaussianKernel, Complex.ofReal_exp]
  congr 1
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp [Complex.I_sq]

theorem neg_inv_gaussianUpperParameter {α : ℝ} (hα : 0 < α) :
    -(gaussianUpperParameter α)⁻¹ = gaussianUpperParameter (Real.pi ^ 2 / α) := by
  have ha : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold gaussianUpperParameter
  push_cast
  field_simp
  simp [Complex.I_sq]

theorem gaussianUpperParameter_fourth_inv {α : ℝ} (hα : 0 < α) :
    ((gaussianUpperParameter α) ^ 4)⁻¹ = ((Real.pi / α) ^ 4 : ℝ) := by
  have ha : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold gaussianUpperParameter
  push_cast
  simp only [mul_pow, Complex.I_pow_four, one_mul, div_pow]
  field_simp

theorem gaussianUpperParameter_twelfth_inv {α : ℝ} (hα : 0 < α) :
    ((gaussianUpperParameter α) ^ 12)⁻¹ = ((Real.pi / α) ^ 12 : ℝ) := by
  have ha : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold gaussianUpperParameter
  push_cast
  simp only [mul_pow, Complex.I_pow_eq_pow_mod, show 12 % 4 = 0 from rfl,
    pow_zero, one_mul, div_pow]
  field_simp

theorem fourier_gaussianKernel_eight_normalized {α : ℝ} (hα : 0 < α) (ξ : Ambient 8) :
    𝓕 (fun x : Ambient 8 => (gaussianKernel α x : ℂ)) ξ =
      (((Real.pi / α) ^ 4 : ℝ) : ℂ) * (gaussianKernel (Real.pi ^ 2 / α) ξ : ℂ) := by
  have h := fourier_upperGaussian_eight (gaussianUpperParameter_pos hα) ξ
  have hf : upperGaussian (d := 8) (gaussianUpperParameter α) =
      fun x => (gaussianKernel α x : ℂ) := funext (upperGaussian_gaussianUpperParameter α)
  rw [hf] at h
  simpa only [upperGaussian_gaussianUpperParameter, neg_inv_gaussianUpperParameter hα,
    gaussianUpperParameter_fourth_inv hα] using h

theorem fourier_gaussianKernel_twentyFour_normalized {α : ℝ} (hα : 0 < α)
    (ξ : Ambient 24) :
    𝓕 (fun x : Ambient 24 => (gaussianKernel α x : ℂ)) ξ =
      (((Real.pi / α) ^ 12 : ℝ) : ℂ) * (gaussianKernel (Real.pi ^ 2 / α) ξ : ℂ) := by
  have h := fourier_upperGaussian_twentyFour (gaussianUpperParameter_pos hα) ξ
  have hf : upperGaussian (d := 24) (gaussianUpperParameter α) =
      fun x => (gaussianKernel α x : ℂ) := funext (upperGaussian_gaussianUpperParameter α)
  rw [hf] at h
  simpa only [upperGaussian_gaussianUpperParameter, neg_inv_gaussianUpperParameter hα,
    gaussianUpperParameter_twelfth_inv hα] using h

theorem gaussian_compact_interval_pos {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) : 0 < α := by
  have hp := Real.pi_pos
  linarith [hα.1]

theorem gaussian_dual_compact_interval {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) :
    Real.pi / α ∈ Icc (3 : ℝ) 4 := by
  have ha := gaussian_compact_interval_pos hα
  constructor
  · apply (le_div_iff₀ ha).mpr
    linarith [hα.2]
  · apply (div_le_iff₀ ha).mpr
    linarith [hα.1]

theorem gaussian_dual_block_separated {α v : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : v ∈ Icc (1 : ℝ) 2) :
    1 ≤ Real.pi / α - v := by
  have hq := gaussian_dual_compact_interval hα
  linarith [hq.1, hv.2]

theorem gaussian_eight_prefactor_lower {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) :
    81 ≤ (Real.pi / α) ^ 4 := by
  have hq := gaussian_dual_compact_interval hα
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hq.1 4
  norm_num at h ⊢
  exact h

theorem gaussian_twentyFour_prefactor_lower {α : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) :
    531441 ≤ (Real.pi / α) ^ 12 := by
  have hq := gaussian_dual_compact_interval hα
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hq.1 12
  norm_num at h ⊢
  exact h

end E8Leech
