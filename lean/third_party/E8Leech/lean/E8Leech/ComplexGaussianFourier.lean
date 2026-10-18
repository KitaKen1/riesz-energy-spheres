import E8Leech.GaussianFourier

/-!
# Complex Gaussian seeds for modular Fourier constructions

The actual seed is exp(pi * I * z * norm(x)^2), for Im z > 0.
The pinned Gaussian Fourier theorem yields the modular parameter inversion.
In dimensions eight and twenty-four the prefactor is an ordinary reciprocal
integer power, so no logarithm-branch argument is needed in later contours.
This constructs seeds, not the final CKMRV weight, interpolation or signs.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical FourierTransform

def upperGaussian {d : ℕ} (z : ℂ) (x : Ambient d) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * z * (‖x‖ : ℂ) ^ 2)

theorem continuous_upperGaussian_joint {d : ℕ} :
    Continuous (fun p : ℂ × Ambient d => upperGaussian p.1 p.2) := by
  unfold upperGaussian
  fun_prop

theorem upperGaussian_zero {d : ℕ} (z : ℂ) : upperGaussian z (0 : Ambient d) = 1 := by
  simp [upperGaussian]

theorem upperGaussian_even {d : ℕ} (z : ℂ) (x : Ambient d) :
    upperGaussian z (-x) = upperGaussian z x := by
  simp [upperGaussian]

theorem upperGaussian_ne_zero {d : ℕ} (z : ℂ) (x : Ambient d) :
    upperGaussian z x ≠ 0 := Complex.exp_ne_zero _

theorem norm_upperGaussian {d : ℕ} (z : ℂ) (x : Ambient d) :
    ‖upperGaussian z x‖ = gaussianKernel (Real.pi * z.im) x := by
  rw [upperGaussian, Complex.norm_exp]
  unfold gaussianKernel
  congr 1
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem integrable_upperGaussian {d : ℕ} {z : ℂ} (hz : 0 < z.im) :
    Integrable (@upperGaussian d z) volume := by
  have hb : 0 < (-(Real.pi : ℂ) * Complex.I * z).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.pi_pos]
  have hi := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Ambient d) hb 0 (0 : Ambient d)
  change Integrable (fun x : Ambient d =>
    Complex.exp ((Real.pi : ℂ) * Complex.I * z * (‖x‖ : ℂ) ^ 2)) volume
  simpa only [mul_zero, zero_mul, add_zero, neg_mul, neg_neg, mul_assoc] using hi

theorem hasRapidDecay_norm_upperGaussian {d : ℕ} {z : ℂ} (hz : 0 < z.im) :
    HasRapidDecay (fun x : Ambient d => ‖upperGaussian z x‖) := by
  simp_rw [norm_upperGaussian]
  exact hasRapidDecay_gaussianKernel (mul_pos Real.pi_pos hz)

theorem neg_inv_upper_parameter_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (-z⁻¹).im := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  rw [Complex.neg_im, Complex.inv_im]
  simp only [neg_div, neg_neg]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

theorem fourier_upperGaussian {d : ℕ} {z : ℂ} (hz : 0 < z.im) (ξ : Ambient d) :
    𝓕 (upperGaussian z) ξ =
      (Complex.I / z) ^ ((d : ℂ) / 2) * upperGaussian (-z⁻¹) ξ := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb : 0 < (-(Real.pi : ℂ) * Complex.I * z).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.pi_pos]
  have hfun : upperGaussian (d := d) z =
      fun x => Complex.exp (-(-(Real.pi : ℂ) * Complex.I * z) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    unfold upperGaussian
    congr 1
    ring
  rw [hfun, fourier_gaussian_innerProductSpace hb]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin]
  have hp : (Real.pi : ℂ) / (-(Real.pi : ℂ) * Complex.I * z) = Complex.I / z := by
    field_simp
    simp [Complex.I_sq]
  rw [hp]
  congr 1
  unfold upperGaussian
  congr 1
  field_simp
  simp [Complex.I_sq]

theorem fourier_upperGaussian_eight {z : ℂ} (hz : 0 < z.im) (ξ : Ambient 8) :
    𝓕 (upperGaussian z) ξ = (z ^ 4)⁻¹ * upperGaussian (-z⁻¹) ξ := by
  have h := fourier_upperGaussian hz ξ
  rw [show ((8 : ℕ) : ℂ) / 2 = (4 : ℕ) by norm_num, Complex.cpow_natCast] at h
  simpa only [div_pow, Complex.I_pow_four, one_div] using h

theorem fourier_upperGaussian_twentyFour {z : ℂ} (hz : 0 < z.im) (ξ : Ambient 24) :
    𝓕 (upperGaussian z) ξ = (z ^ 12)⁻¹ * upperGaussian (-z⁻¹) ξ := by
  have h := fourier_upperGaussian hz ξ
  rw [show ((24 : ℕ) : ℂ) / 2 = (12 : ℕ) by norm_num, Complex.cpow_natCast] at h
  simpa only [div_pow, Complex.I_pow_eq_pow_mod, show 12 % 4 = 0 from rfl,
    pow_zero, one_div] using h

end E8Leech
