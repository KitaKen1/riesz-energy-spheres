import E8Leech.CKMRVMinusBasis
import E8Leech.CKMRVPlusInversion
import E8Leech.CKMRVLaplace

/-!
# The kernels `𝒦 = (K₊ + K₋)/2` and `𝒦̂ = (K₊ − K₋)/2` and the `τ`-side `S` relation

CKMRV (5.1)/(5.2) use `F = e^{πiτr²} + 4 sin²(πr²/2) ∫ 𝒦(τ, it) e^{−πr²t} dt` and
`F̃ = 4 sin²(πr²/2) ∫ 𝒦̂(τ, it) e^{−πr²t} dt`. From `K₋|τ S = K₋` and `K₊|τ S = −K₊` (weights
`d/2 = 4, 12`) we get `𝒦(Sτ, z) = −τ^{d/2} 𝒦̂(τ, z)`. On the imaginary axis this is
`𝒦(iy, z) = −y^{−d/2} 𝒦̂(i/y, z)`. So Lemma 6.2's minorant sign `𝒦(iy, it) ≤ 0` is the kernel
positivity `𝒦̂(i/y, it) ≥ 0` (CKMRV (6.4)(1)).
-/

noncomputable section

namespace E8Leech

open UpperHalfPlane hiding I
open Complex

/-- `𝒦⁽⁸⁾ = (K₊ + K₋)/2`. -/
def ckmrvEightKernel (τ z : ℍ) : ℂ := (ckmrvEightPlusKernel τ z + ckmrvEightMinusKernel τ z) / 2

/-- `𝒦̂⁽⁸⁾ = (K₊ − K₋)/2`. -/
def ckmrvEightHatKernel (τ z : ℍ) : ℂ :=
  (ckmrvEightPlusKernel τ z - ckmrvEightMinusKernel τ z) / 2

/-- `𝒦⁽²⁴⁾ = (K₊ + K₋)/2`. -/
def ckmrvLeechKernel (τ z : ℍ) : ℂ := (ckmrvLeechPlusKernel τ z + ckmrvLeechMinusKernel τ z) / 2

/-- `𝒦̂⁽²⁴⁾ = (K₊ − K₋)/2`. -/
def ckmrvLeechHatKernel (τ z : ℍ) : ℂ :=
  (ckmrvLeechPlusKernel τ z - ckmrvLeechMinusKernel τ z) / 2

theorem ckmrvEightKernel_S (τ z : ℍ) :
    ckmrvEightKernel (ModularGroup.S • τ) z = -(τ : ℂ) ^ 4 * ckmrvEightHatKernel τ z := by
  rw [ckmrvEightKernel, ckmrvEightHatKernel, ckmrvEightPlusKernel_S, ckmrvEightMinusKernel_S]
  ring

theorem ckmrvEightHatKernel_S (τ z : ℍ) :
    ckmrvEightHatKernel (ModularGroup.S • τ) z = -(τ : ℂ) ^ 4 * ckmrvEightKernel τ z := by
  rw [ckmrvEightKernel, ckmrvEightHatKernel, ckmrvEightPlusKernel_S, ckmrvEightMinusKernel_S]
  ring

theorem ckmrvLeechKernel_S (τ z : ℍ) :
    ckmrvLeechKernel (ModularGroup.S • τ) z = -(τ : ℂ) ^ 12 * ckmrvLeechHatKernel τ z := by
  rw [ckmrvLeechKernel, ckmrvLeechHatKernel, ckmrvLeechPlusKernel_S, ckmrvLeechMinusKernel_S]
  ring

theorem ckmrvLeechHatKernel_S (τ z : ℍ) :
    ckmrvLeechHatKernel (ModularGroup.S • τ) z = -(τ : ℂ) ^ 12 * ckmrvLeechKernel τ z := by
  rw [ckmrvLeechKernel, ckmrvLeechHatKernel, ckmrvLeechPlusKernel_S, ckmrvLeechMinusKernel_S]
  ring

/-- **On the imaginary axis**, `𝒦(iy, z) = −y^{−4} 𝒦̂(i/y, z)`. -/
theorem ckmrvEightKernel_imagPt {y : ℝ} (hy : 0 < y) (z : ℍ) :
    ckmrvEightKernel (imagPt y) z = -((y : ℂ) ^ 4)⁻¹ * ckmrvEightHatKernel (imagPt y⁻¹) z := by
  rw [← S_smul_imagPt_inv hy, ckmrvEightKernel_S, coe_imagPt (inv_pos.mpr hy)]
  have hI : (I : ℂ) ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  rw [mul_pow, hI, one_mul]
  push_cast
  rw [inv_pow]

/-- On the imaginary axis, `𝒦̂(iy, z) = −y^{−4} 𝒦(i/y, z)`. -/
theorem ckmrvEightHatKernel_imagPt {y : ℝ} (hy : 0 < y) (z : ℍ) :
    ckmrvEightHatKernel (imagPt y) z = -((y : ℂ) ^ 4)⁻¹ * ckmrvEightKernel (imagPt y⁻¹) z := by
  rw [← S_smul_imagPt_inv hy, ckmrvEightHatKernel_S, coe_imagPt (inv_pos.mpr hy)]
  have hI : (I : ℂ) ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  rw [mul_pow, hI, one_mul]
  push_cast
  rw [inv_pow]

/-- **On the imaginary axis**, `𝒦⁽²⁴⁾(iy, z) = −y^{−12} 𝒦̂⁽²⁴⁾(i/y, z)`. -/
theorem ckmrvLeechKernel_imagPt {y : ℝ} (hy : 0 < y) (z : ℍ) :
    ckmrvLeechKernel (imagPt y) z = -((y : ℂ) ^ 12)⁻¹ * ckmrvLeechHatKernel (imagPt y⁻¹) z := by
  rw [← S_smul_imagPt_inv hy, ckmrvLeechKernel_S, coe_imagPt (inv_pos.mpr hy)]
  have hI : (I : ℂ) ^ 12 = 1 := by rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, I_sq]; norm_num
  rw [mul_pow, hI, one_mul]
  push_cast
  rw [inv_pow]

/-- On the imaginary axis, `𝒦̂⁽²⁴⁾(iy, z) = −y^{−12} 𝒦⁽²⁴⁾(i/y, z)`. -/
theorem ckmrvLeechHatKernel_imagPt {y : ℝ} (hy : 0 < y) (z : ℍ) :
    ckmrvLeechHatKernel (imagPt y) z =
      -((y : ℂ) ^ 12)⁻¹ * ckmrvLeechKernel (imagPt y⁻¹) z := by
  rw [← S_smul_imagPt_inv hy, ckmrvLeechHatKernel_S, coe_imagPt (inv_pos.mpr hy)]
  have hI : (I : ℂ) ^ 12 = 1 := by rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, I_sq]; norm_num
  rw [mul_pow, hI, one_mul]
  push_cast
  rw [inv_pow]

end E8Leech
