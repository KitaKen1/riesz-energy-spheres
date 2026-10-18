import E8Leech.LeechContourCauchy
import E8Leech.LeechCuspContour

/-!
# The `x`-side integrands of the Leech contour identity on the sides of the triangles

With `f(t) = e^{2πt}(A t + B)` the growing part of `𝒦⁽²⁴⁾(iy, it)` and `γ(a) = a⁻¹² e^{−πρ/a}`:

* `(𝒦 − f)(t) γ(t − i) = −i e^{−iπρ} ((𝒦̂ − P₁) E)(v(t)) v'(t)` on the semicircle of `(0, 1, ∞)`
  (`leech_kernel_gaussHat_sub_I`, from `𝒦̂ = 𝒦 |_{−10} STS`);
* `(𝒦 − f)(t) γ(t + i) = −i e^{iπρ} ((𝒦̂ − P₋₁) E)(u(t)) u'(t)` on the semicircle of `(−1, 0, ∞)`
  (`leech_kernel_gaussHat_add_I`, from `𝒦̂ = 𝒦 |_{−10} TST`);
* after `t ↦ 1/s`, `(𝒦 − f)(t) γ(t)` becomes
  `(𝒦̂ E)(is) − (e^{−iπρ} ((𝒦̂ − P₁) E)(1 + is) + e^{iπρ} ((𝒦̂ − P₋₁) E)(is − 1))/2`
  (`leech_kernel_gaussHat_inv`, from the right relation one and `f(t + i) + f(t − i) = 2 f(t)`).

The subtraction of `f` on the `x`-side is exactly the subtraction of the cusp parts on the two
triangles.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set MeasureTheory
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

theorem gaussHat_twentyFour' {a : ℂ} (ha : a ≠ 0) (r : ℝ) :
    gaussHat 24 a r = (a ^ 12)⁻¹ * cexp (-(π * (r : ℂ) ^ 2) / a) := by
  rw [gaussHat_twentyFour ha, gaussGam]
  push_cast
  rfl

theorem neg_I_pow_twelve : (-I : ℂ) ^ 12 = 1 := by
  rw [show (-I : ℂ) ^ 12 = (I ^ 2) ^ 6 by ring, Complex.I_sq]
  norm_num

theorem I_pow_twelve : (I : ℂ) ^ 12 = 1 := by
  rw [show (I : ℂ) ^ 12 = (I ^ 2) ^ 6 by ring, Complex.I_sq]
  norm_num

/-! ## The `t ∓ i` terms are semicircle integrals -/

/-- `(𝒦 − f)(t) (t − i)⁻¹² e^{−πρ/(t−i)} = −i e^{−iπρ} ((𝒦̂ − P₁) E)(v) v'`. -/
theorem leech_kernel_gaussHat_sub_I (y r : ℝ) {t : ℝ} (ht : 0 < t) :
    (ckmrvLeechKernel (imagPt y) (imagPt t) -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) t) * gaussHat 24 ((t : ℂ) - I) r =
      -I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (leechPlusF y (r ^ 2) (vPath t) * vPath' t) := by
  have hD := one_add_I_mul_ne_zero t
  have htI : (t : ℂ) - I = -I * (1 + I * t) := by linear_combination (t : ℂ) * Complex.I_sq
  have hne : (t : ℂ) - I ≠ 0 := by rw [htI]; exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hD
  have hvim : 0 < (vPath t).im := by rw [im_vPath]; positivity
  have hexp : cexp (-(π * (r : ℂ) ^ 2) / ((t : ℂ) - I)) =
      cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * gaussE (r ^ 2) (vPath t) := by
    rw [gaussE, ← Complex.exp_add]
    congr 1
    have e1 : -(π * (r : ℂ) ^ 2) / ((t : ℂ) - I) = -(π * I * (r : ℂ) ^ 2) / (1 + I * t) := by
      rw [htI, div_eq_div_iff (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hD) hD]
      linear_combination (-((π : ℂ) * (r : ℂ) ^ 2 * (1 + I * t))) * Complex.I_sq
    rw [e1, vPath]
    push_cast
    field_simp
    ring
  have h12 : (-I * (1 + I * (t : ℂ))) ^ 12 = (1 + I * t) ^ 12 := by
    rw [mul_pow, neg_I_pow_twelve, one_mul]
  rw [gaussHat_twentyFour' hne, hexp, leechPlusF_eq_STS hvim, vPath_div_one_sub,
    rightC_I_mul _ _ ht, htI, h12, vPath_sub_one, vPath',
    show -I * (I * (t : ℂ)) = (t : ℂ) by linear_combination (-(t : ℂ)) * Complex.I_sq]
  generalize (1 + I * (t : ℂ)) = D at hD
  field_simp
  linear_combination ((ckmrvLeechKernel (imagPt y) (imagPt t) -
    growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) t) * gaussE (r ^ 2) (vPath t)) *
      Complex.I_sq

/-- `(𝒦 − f)(t) (t + i)⁻¹² e^{−πρ/(t+i)} = −i e^{iπρ} ((𝒦̂ − P₋₁) E)(u) u'`. -/
theorem leech_kernel_gaussHat_add_I (y r : ℝ) {t : ℝ} (ht : 0 < t) :
    (ckmrvLeechKernel (imagPt y) (imagPt t) -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) t) * gaussHat 24 ((t : ℂ) + I) r =
      -I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * (leechMinusF y (r ^ 2) (uPath t) * uPath' t) := by
  have hE := one_sub_I_mul_ne_zero t
  have htI : (t : ℂ) + I = I * (1 - I * t) := by linear_combination (t : ℂ) * Complex.I_sq
  have hne : (t : ℂ) + I ≠ 0 := by rw [htI]; exact mul_ne_zero I_ne_zero hE
  have huim : 0 < (uPath t).im := by rw [im_uPath]; positivity
  have hexp : cexp (-(π * (r : ℂ) ^ 2) / ((t : ℂ) + I)) =
      cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * gaussE (r ^ 2) (uPath t) := by
    rw [gaussE, ← Complex.exp_add]
    congr 1
    have e1 : -(π * (r : ℂ) ^ 2) / ((t : ℂ) + I) = π * I * (r : ℂ) ^ 2 / (1 - I * t) := by
      rw [htI, div_eq_div_iff (mul_ne_zero I_ne_zero hE) hE]
      linear_combination (-((π : ℂ) * (r : ℂ) ^ 2 * (1 - I * t))) * Complex.I_sq
    rw [e1, uPath]
    push_cast
    field_simp
    ring
  have h12 : (I * (1 - I * (t : ℂ))) ^ 12 = (1 - I * t) ^ 12 := by
    rw [mul_pow, I_pow_twelve, one_mul]
  rw [gaussHat_twentyFour' hne, hexp, leechMinusF_eq_TST huim, uPath_div_add_one,
    rightC_I_mul _ _ ht, htI, h12, uPath_add_one, uPath',
    show -I * (I * (t : ℂ)) = (t : ℂ) by linear_combination (-(t : ℂ)) * Complex.I_sq]
  generalize (1 - I * (t : ℂ)) = E at hE
  field_simp
  linear_combination ((ckmrvLeechKernel (imagPt y) (imagPt t) -
    growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) t) * gaussE (r ^ 2) (uPath t)) *
      Complex.I_sq

/-! ## The `2t⁻¹²e^{−πρ/t}` term: `t ↦ 1/s` and the right relation one -/

/-- `2s¹⁰ 𝒦(τ, i/s) = 2𝒦̂(τ, is) − 𝒦̂(τ, is + 1) − 𝒦̂(τ, is − 1)`. -/
theorem leech_kernel_imagPt_inv (τ : ℍ) {s : ℝ} (hs : 0 < s) :
    2 * (s : ℂ) ^ 10 * ckmrvLeechKernel τ (imagPt s⁻¹) =
      2 * rightC ckmrvLeechHatKernel τ (I * s) - rightC ckmrvLeechHatKernel τ (1 + I * s) -
        rightC ckmrvLeechHatKernel τ (I * s - 1) := by
  have hP := congrFun (ckmrvLeechPlusKernel_right_rel_one τ) (imagPt s)
  have hM := congrFun (ckmrvLeechMinusKernel_right_rel_one τ) (imagPt s)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrv_slash_T_apply_smul, slash_T_inv_apply', ckmrv_slash_S_apply, neg_neg, zpow_ofNat,
    S_smul_imagPt hs, coe_imagPt hs, mul_pow, I_pow_ten] at hP hM
  have e2 : (1 : ℂ) + I * s = ((ModularGroup.T • imagPt s : ℍ) : ℂ) := by
    rw [coe_T_smul, coe_imagPt hs]; ring
  have e3 : I * (s : ℂ) - 1 = ((ModularGroup.T⁻¹ • imagPt s : ℍ) : ℂ) := by
    rw [coe_T_inv_smul', coe_imagPt hs]
  rw [rightC_I_mul _ _ hs, e2, e3, rightC_coe, rightC_coe]
  simp only [ckmrvLeechKernel, ckmrvLeechHatKernel]
  linear_combination (hP - hM) / 2

/-- The same with the growing part subtracted: the cusp parts appear on the lines `Re z = ±1`. -/
theorem leech_kernel_sub_growth_imagPt_inv (y : ℝ) {s : ℝ} (hs : 0 < s) :
    2 * (s : ℂ) ^ 10 * (ckmrvLeechKernel (imagPt y) (imagPt s⁻¹) -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) ((s⁻¹ : ℝ) : ℂ)) =
      2 * rightC ckmrvLeechHatKernel (imagPt y) (I * s) -
        (rightC ckmrvLeechHatKernel (imagPt y) (1 + I * s) -
          cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (1 + I * s)) -
        (rightC ckmrvLeechHatKernel (imagPt y) (I * s - 1) -
          cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (I * s - 1)) := by
  have h1 := leech_kernel_imagPt_inv (imagPt y) hs
  have h2 := cuspPart_add_cuspPart (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) hs.ne'
  linear_combination h1 - h2

/-- The `t ↦ 1/s` integrand:
`s⁻² (𝒦 − f)(1/s) γ(1/s) = (𝒦̂E)(is) − (e^{−iπρ} F₊(1 + is) + e^{iπρ} F₋(is − 1))/2`. -/
theorem leech_kernel_gaussHat_inv (y r : ℝ) {s : ℝ} (hs : 0 < s) :
    |(-(s ^ 2)⁻¹ : ℝ)| • ((ckmrvLeechKernel (imagPt y) (imagPt s⁻¹) -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) ((s⁻¹ : ℝ) : ℂ)) *
        gaussHat 24 ((s⁻¹ : ℝ) : ℂ) r) =
      leechHatF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
          leechPlusF y (r ^ 2) (1 + I * s) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * leechMinusF y (r ^ 2) (I * s - 1)) / 2 := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsi : ((s⁻¹ : ℝ) : ℂ) ≠ 0 := by push_cast; exact inv_ne_zero hs0
  have hK := leech_kernel_sub_growth_imagPt_inv y hs
  have hX : gaussE (r ^ 2) (I * s) = cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) :=
    gaussE_I_mul _ _
  have hg : cexp (-(π * (r : ℂ) ^ 2) / ((s⁻¹ : ℝ) : ℂ)) =
      cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) := by
    congr 1; rw [Complex.ofReal_inv, div_inv_eq_mul]; push_cast; ring
  have hss : (((s ^ 2)⁻¹ : ℝ) : ℂ) * ((((s⁻¹ : ℝ) : ℂ)) ^ 12)⁻¹ = (s : ℂ) ^ 10 := by
    push_cast
    rw [inv_pow, inv_inv, inv_mul_eq_div, div_eq_iff (pow_ne_zero 2 hs0)]
    ring
  have hpm := cexp_neg_mul_cexp (π * I * ((r ^ 2 : ℝ) : ℂ))
  rw [abs_neg, abs_of_pos (by positivity), Complex.real_smul, gaussHat_twentyFour' hsi, hg]
  simp only [leechHatF, leechPlusF, leechMinusF, gaussE_one_add, gaussE_sub_one, hX]
  linear_combination (cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) / 2) * hK +
    (cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) / 2 *
      ((rightC ckmrvLeechHatKernel (imagPt y) (1 + I * s) -
          cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (1 + I * s)) +
        (rightC ckmrvLeechHatKernel (imagPt y) (I * s - 1) -
          cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (I * s - 1)))) * hpm +
    ((ckmrvLeechKernel (imagPt y) (imagPt s⁻¹) -
      growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) ((s⁻¹ : ℝ) : ℂ)) *
        cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s))) * hss

end E8Leech
