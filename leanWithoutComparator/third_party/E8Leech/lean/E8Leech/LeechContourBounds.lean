import E8Leech.CKMRVContourIdentity
import E8Leech.LeechSchwartzProfile

/-!
# Growth of the Leech kernels in the right variable

For fixed `τ`, the kernels `K±⁽²⁴⁾(τ, w)` have the cusp expansion (CKMRV (4.38))
`e^{−2πiw}(a w + b) + (c w + d) + O(|w|² e^{−π Im w})`, uniformly in `Re w`. With `t = −iw` this is the
cusp profile `e^{2πt}(A t + B) + C t + D` of `LeechSchwartzProfile` with a complex argument
(`cuspProfileC`, `ckmrvLeechPlusG_eq`, `ckmrvLeechMinusG_eq`). Hence, in a vertical strip and for
`Im w` large,

* `(K₊ + s K₋)/2 − e^{2πt}(A t + B)` grows at most linearly (`exists_bound_leech_sub_growth`): this
  is what remains of the kernel at a cusp after the growing part has been subtracted;
* `(K₊ + s K₋)/2` is `O((1 + Im w) e^{2π Im w})` (`exists_bound_leech_top`).

At the cusp `0` the kernels are bounded (`exists_bound_leechKernels_S`, CKMRV (4.39)).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The cusp profile with a complex argument -/

/-- The cusp profile `e^{2πt}(A t + B) + C t + D` with a complex argument. -/
def cuspProfileC (A B C D : ℂ) (t : ℂ) : ℂ := cexp (2 * π * t) * (A * t + B) + (C * t + D)

/-- The growing part `e^{2πt}(A t + B)` of the cusp profile, with a complex argument. -/
def growthC (A B : ℂ) (t : ℂ) : ℂ := cexp (2 * π * t) * (A * t + B)

theorem differentiable_growthC (A B : ℂ) : Differentiable ℂ (growthC A B) := by
  unfold growthC
  fun_prop

theorem cuspProfileC_eq (A B C D : ℂ) (t : ℂ) :
    cuspProfileC A B C D t = growthC A B t + (C * t + D) := rfl

theorem cuspProfileC_combo (s A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : ℂ) (t : ℂ) :
    cuspProfileC ((A₁ + s * A₂) / 2) ((B₁ + s * B₂) / 2) ((C₁ + s * C₂) / 2)
        ((D₁ + s * D₂) / 2) t =
      (cuspProfileC A₁ B₁ C₁ D₁ t + s * cuspProfileC A₂ B₂ C₂ D₂ t) / 2 := by
  simp only [cuspProfileC]
  ring

/-- `f(t + i) + f(t − i) = 2 f(t)` for the growing part. -/
theorem growthC_add_I_add_sub_I (A B : ℂ) (t : ℂ) :
    growthC A B (t + I) + growthC A B (t - I) = 2 * growthC A B t := by
  have h1 : cexp (2 * π * (t + I)) = cexp (2 * π * t) := by
    rw [mul_add, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h2 : cexp (2 * π * (t - I)) = cexp (2 * π * t) := by
    rw [mul_sub, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  simp only [growthC, h1, h2]
  ring

theorem growthC_ofReal (A B : ℂ) (t : ℝ) :
    growthC A B (t : ℂ) =
      A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ) := by
  rw [growthC, Complex.ofReal_exp]
  push_cast
  ring

theorem norm_growthC (A B : ℂ) (t : ℂ) :
    ‖growthC A B t‖ = Real.exp (2 * π * t.re) * ‖A * t + B‖ := by
  rw [growthC, norm_mul, Complex.norm_exp]
  congr 2
  rw [show (2 : ℂ) * π * t = ((2 * π : ℝ) : ℂ) * t by push_cast; ring, Complex.re_ofReal_mul]

theorem cuspS_sq_inv (z : ℍ) : (cuspS z ^ 2)⁻¹ = cexp (2 * π * (-I * z)) := by
  rw [cuspS, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- `G₊⁽²⁴⁾(τ, z)` is the cusp profile at `t = −iz`. -/
theorem ckmrvLeechPlusG_eq (τ z : ℍ) :
    ckmrvLeechPlusG τ z = cuspProfileC (leechPlusCusp τ 0) (leechPlusCusp τ 1)
      (leechPlusCusp τ 2) (leechPlusCusp τ 3) (-I * z) := by
  rw [ckmrvLeechPlusG, cuspS_sq_inv, cuspProfileC]
  simp only [leechPlusCusp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination ((1728 * ckmrvPlusScale)⁻¹ *
    (cexp (2 * π * (-I * z)) * ((z : ℂ) * leechPlusM1a τ) + (z : ℂ) * leechPlusM1c τ)) *
      Complex.I_sq

/-- `G₋⁽²⁴⁾(τ, z)` is the cusp profile at `t = −iz`. -/
theorem ckmrvLeechMinusG_eq (τ z : ℍ) :
    ckmrvLeechMinusG τ z = cuspProfileC (leechMinusCusp τ 0) (leechMinusCusp τ 1)
      (leechMinusCusp τ 2) (leechMinusCusp τ 3) (-I * z) := by
  rw [ckmrvLeechMinusG, cuspS_sq_inv, cuspProfileC, ckmrvEll]
  simp only [leechMinusCusp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-! ## Bounds in a vertical strip -/

theorem one_add_sq_mul_exp_neg_le (v : ℝ) (hv : 0 ≤ v) :
    (1 + v) ^ 2 * Real.exp (-π * v) ≤ 1 := by
  have h1 : 1 + v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have h2 : (1 + v) ^ 2 ≤ Real.exp v ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : Real.exp v ^ 2 = Real.exp (2 * v) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h4 : Real.exp (2 * v) ≤ Real.exp (π * v) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have h5 : Real.exp (-π * v) = (Real.exp (π * v))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [h5, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
  linarith

/-- In a vertical strip, `(K₊ + s K₋)/2 (iβ, w)` minus its cusp profile at `t = −iw` is bounded
for `Im w` large. -/
theorem exists_bound_leech_sub_cusp (s : ℂ) (β : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ w : ℍ, V ≤ w.im → |(w : ℂ).re| ≤ R →
      ‖(ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
        cuspProfileC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2)
          (leechAxisCusp s β 3) (-I * w)‖ ≤ C := by
  obtain ⟨c₁, V₁, hc₁, h₁⟩ :=
    exists_bound_of_isBigO_atImInfty (isBigO_ckmrvLeechPlusKernel_sub_G (imagPt β))
  obtain ⟨c₂, V₂, hc₂, h₂⟩ :=
    exists_bound_of_isBigO_atImInfty (isBigO_ckmrvLeechMinusKernel_sub_G (imagPt β))
  refine ⟨(c₁ * (R + 1) ^ 2 + ‖s‖ * (c₂ * (R + 1))) / 2, max V₁ V₂, by positivity,
    fun w hw hre => ?_⟩
  have hV₁ : V₁ ≤ w.im := le_trans (le_max_left _ _) hw
  have hV₂ : V₂ ≤ w.im := le_trans (le_max_right _ _) hw
  have hv : 0 ≤ w.im := w.im_pos.le
  have hzn := norm_coe_le_of_re w hre
  have hn0 := norm_nonneg (w : ℂ)
  have e : (ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
      cuspProfileC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2)
        (leechAxisCusp s β 3) (-I * w) =
      ((ckmrvLeechPlusKernel (imagPt β) w - ckmrvLeechPlusG (imagPt β) w) +
        s * (ckmrvLeechMinusKernel (imagPt β) w - ckmrvLeechMinusG (imagPt β) w)) / 2 := by
    rw [ckmrvLeechPlusG_eq, ckmrvLeechMinusG_eq]
    simp only [leechAxisCusp]
    rw [cuspProfileC_combo]
    ring
  have b₁ := h₁ w hV₁
  have b₂ := h₂ w hV₂
  rw [Real.norm_of_nonneg (by positivity)] at b₁ b₂
  have hE := one_add_sq_mul_exp_neg_le w.im hv
  have hpos := Real.exp_pos (-π * w.im)
  have hw1 : ‖(w : ℂ)‖ ≤ (R + 1) * (1 + w.im) := by nlinarith
  have k₁ : ‖(w : ℂ)‖ ^ 2 * Real.exp (-π * w.im) ≤ (R + 1) ^ 2 := by
    calc ‖(w : ℂ)‖ ^ 2 * Real.exp (-π * w.im)
        ≤ ((R + 1) * (1 + w.im)) ^ 2 * Real.exp (-π * w.im) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn0 hw1 2) hpos.le
      _ = (R + 1) ^ 2 * ((1 + w.im) ^ 2 * Real.exp (-π * w.im)) := by ring
      _ ≤ (R + 1) ^ 2 * 1 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (R + 1) ^ 2 := mul_one _
  have k₂ : ‖(w : ℂ)‖ * Real.exp (-π * w.im) ≤ R + 1 := by
    have h1 : 1 + w.im ≤ (1 + w.im) ^ 2 := by nlinarith
    calc ‖(w : ℂ)‖ * Real.exp (-π * w.im)
        ≤ (R + 1) * (1 + w.im) * Real.exp (-π * w.im) := mul_le_mul_of_nonneg_right hw1 hpos.le
      _ = (R + 1) * ((1 + w.im) * Real.exp (-π * w.im)) := by ring
      _ ≤ (R + 1) * ((1 + w.im) ^ 2 * Real.exp (-π * w.im)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hpos.le) (by positivity)
      _ ≤ (R + 1) * 1 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = R + 1 := mul_one _
  have hn : ‖(ckmrvLeechPlusKernel (imagPt β) w - ckmrvLeechPlusG (imagPt β) w) +
      s * (ckmrvLeechMinusKernel (imagPt β) w - ckmrvLeechMinusG (imagPt β) w)‖ ≤
        c₁ * (R + 1) ^ 2 + ‖s‖ * (c₂ * (R + 1)) := by
    refine (norm_add_le _ _).trans
      (add_le_add (b₁.trans (mul_le_mul_of_nonneg_left k₁ hc₁.le)) ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b₂.trans (mul_le_mul_of_nonneg_left k₂ hc₂.le))
      (norm_nonneg s)
  rw [e, norm_div, Complex.norm_ofNat]
  gcongr

/-- **After the growing part has been subtracted, the kernel grows at most linearly at a cusp.** -/
theorem exists_bound_leech_sub_growth (s : ℂ) (β : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ w : ℍ, V ≤ w.im → |(w : ℂ).re| ≤ R →
      ‖(ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
        growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w)‖ ≤ C * (1 + w.im) := by
  obtain ⟨C₀, V, hC₀, h⟩ := exists_bound_leech_sub_cusp s β hR
  refine ⟨C₀ + ‖leechAxisCusp s β 2‖ * (R + 1) + ‖leechAxisCusp s β 3‖, V, by positivity,
    fun w hw hre => ?_⟩
  have hv : 0 ≤ w.im := w.im_pos.le
  have hzn := norm_coe_le_of_re w hre
  have b := h w hw hre
  have e : (ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
      growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w) =
      ((ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
        cuspProfileC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (leechAxisCusp s β 2)
          (leechAxisCusp s β 3) (-I * w)) +
        (leechAxisCusp s β 2 * (-I * w) + leechAxisCusp s β 3) := by
    rw [cuspProfileC_eq]
    ring
  have hlin : ‖leechAxisCusp s β 2 * (-I * w) + leechAxisCusp s β 3‖ ≤
      ‖leechAxisCusp s β 2‖ * (R + w.im) + ‖leechAxisCusp s β 3‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hzn (norm_nonneg _)) le_rfl
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 := norm_nonneg (leechAxisCusp s β 2)
  have h3 := norm_nonneg (leechAxisCusp s β 3)
  nlinarith [mul_nonneg hC₀ hv, mul_nonneg h3 hv, mul_nonneg (mul_nonneg h2 hR) hv,
    mul_nonneg h2 hv]

/-- **Growth of the kernels at `i∞` in a vertical strip**: `O((1 + Im w) e^{2π Im w})`. -/
theorem exists_bound_leech_top (s : ℂ) (β : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ w : ℍ, V ≤ w.im → |(w : ℂ).re| ≤ R →
      ‖(ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2‖ ≤
        C * (1 + w.im) * Real.exp (2 * π * w.im) := by
  obtain ⟨C₀, V, hC₀, h⟩ := exists_bound_leech_sub_growth s β hR
  refine ⟨C₀ + ‖leechAxisCusp s β 0‖ * (R + 1) + ‖leechAxisCusp s β 1‖, V, by positivity,
    fun w hw hre => ?_⟩
  have hv : 0 ≤ w.im := w.im_pos.le
  have hzn := norm_coe_le_of_re w hre
  have b := h w hw hre
  have hA := norm_nonneg (leechAxisCusp s β 0)
  have hB := norm_nonneg (leechAxisCusp s β 1)
  have hre' : (-I * (w : ℂ)).re = w.im := by simp
  have hg : ‖growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w)‖ ≤
      Real.exp (2 * π * w.im) * (‖leechAxisCusp s β 0‖ * (R + w.im) + ‖leechAxisCusp s β 1‖) := by
    rw [norm_growthC, hre']
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hzn hA) le_rfl
  have hK : ‖(ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2‖ ≤
      ‖(ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
        growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w)‖ +
      ‖growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w)‖ := by
    have := norm_add_le
      ((ckmrvLeechPlusKernel (imagPt β) w + s * ckmrvLeechMinusKernel (imagPt β) w) / 2 -
        growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w))
      (growthC (leechAxisCusp s β 0) (leechAxisCusp s β 1) (-I * w))
    simpa using this
  have hexp : 1 ≤ Real.exp (2 * π * w.im) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) hv)
  have hlin : ‖leechAxisCusp s β 0‖ * (R + w.im) + ‖leechAxisCusp s β 1‖ ≤
      (‖leechAxisCusp s β 0‖ * (R + 1) + ‖leechAxisCusp s β 1‖) * (1 + w.im) := by
    nlinarith [mul_nonneg hB hv, mul_nonneg (mul_nonneg hA hR) hv, mul_nonneg hA hv]
  have h1v : (0 : ℝ) ≤ 1 + w.im := by linarith
  calc _ ≤ C₀ * (1 + w.im) + Real.exp (2 * π * w.im) *
        (‖leechAxisCusp s β 0‖ * (R + w.im) + ‖leechAxisCusp s β 1‖) :=
        hK.trans (add_le_add b hg)
    _ ≤ C₀ * (1 + w.im) * Real.exp (2 * π * w.im) + Real.exp (2 * π * w.im) *
        ((‖leechAxisCusp s β 0‖ * (R + 1) + ‖leechAxisCusp s β 1‖) * (1 + w.im)) :=
        add_le_add (le_mul_of_one_le_right (mul_nonneg hC₀ h1v) hexp)
          (mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le)
    _ = (C₀ + ‖leechAxisCusp s β 0‖ * (R + 1) + ‖leechAxisCusp s β 1‖) * (1 + w.im) *
        Real.exp (2 * π * w.im) := by ring

/-- Boundedness of the kernels at the cusp `0` of the right variable (CKMRV (4.39)). -/
theorem exists_bound_leechKernels_S (τ : ℍ) :
    ∃ C V : ℝ, 0 ≤ C ∧ 1 ≤ V ∧ ∀ w : ℍ, V ≤ w.im →
      ‖ckmrvLeechHatKernel τ (ModularGroup.S • w)‖ ≤ C ∧
        ‖ckmrvLeechKernel τ (ModularGroup.S • w)‖ ≤ C := by
  obtain ⟨c₁, V₁, hc₁, h₁⟩ :=
    exists_bound_of_isBigO_atImInfty (isBigO_ckmrvLeechPlusKernel_S_right τ)
  obtain ⟨c₂, V₂, hc₂, h₂⟩ :=
    exists_bound_of_isBigO_atImInfty (isBigO_ckmrvLeechMinusKernel_S_right τ)
  refine ⟨c₁ + c₂, max (max V₁ V₂) 1, by positivity, le_max_right _ _, fun w hw => ?_⟩
  have hw1 : 1 ≤ w.im := le_trans (le_max_right _ _) hw
  have hn : 1 ≤ ‖(w : ℂ)‖ ^ 10 := by
    have h := abs_of_pos w.im_pos
    have : w.im ≤ ‖(w : ℂ)‖ := by
      rw [show w.im = |(w : ℂ).im| from h.symm]
      exact Complex.abs_im_le_norm _
    exact one_le_pow₀ (by linarith)
  have bound : ∀ (K : ℍ → ℍ → ℂ) (c : ℝ) (k : ℝ), 0 < c → 0 < k →
      ‖K τ (ModularGroup.S • w) * (w : ℂ) ^ 10‖ ≤ c * ‖Real.exp (-k * π * w.im)‖ →
      ‖K τ (ModularGroup.S • w)‖ ≤ c := by
    intro K c k hc hk h
    rw [norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le] at h
    have hexp : Real.exp (-k * π * w.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos (mul_pos hk Real.pi_pos) w.im_pos])
    have hK := norm_nonneg (K τ (ModularGroup.S • w))
    nlinarith
  have hp := bound ckmrvLeechPlusKernel c₁ 2 hc₁ (by norm_num)
    (by
      have := h₁ w (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hw)
      simpa [mul_assoc] using this)
  have hm := bound ckmrvLeechMinusKernel c₂ 1 hc₂ (by norm_num)
    (by
      have := h₂ w (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hw)
      simpa using this)
  constructor
  · simp only [ckmrvLeechHatKernel, norm_div, Complex.norm_ofNat]
    have := norm_sub_le (ckmrvLeechPlusKernel τ (ModularGroup.S • w))
      (ckmrvLeechMinusKernel τ (ModularGroup.S • w))
    linarith
  · simp only [ckmrvLeechKernel, norm_div, Complex.norm_ofNat]
    have := norm_add_le (ckmrvLeechPlusKernel τ (ModularGroup.S • w))
      (ckmrvLeechMinusKernel τ (ModularGroup.S • w))
    linarith

/-! ## The two combined kernels -/

/-- `𝒦⁽²⁴⁾(iy, w) − e^{2πt}(A t + B)` (`t = −iw`) grows at most linearly at `i∞` in a strip. -/
theorem exists_bound_leechKernel_sub_growth (y : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ w : ℍ, V ≤ w.im → |(w : ℂ).re| ≤ R →
      ‖ckmrvLeechKernel (imagPt y) w -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * w)‖ ≤ C * (1 + w.im) := by
  obtain ⟨C, V, hC, h⟩ := exists_bound_leech_sub_growth 1 y hR
  refine ⟨C, V, hC, fun w hw hre => ?_⟩
  have b := h w hw hre
  rwa [one_mul] at b

/-- `𝒦̂⁽²⁴⁾(iy, w) = O((1 + Im w) e^{2π Im w})` at `i∞` in a strip. -/
theorem exists_bound_leechHatKernel_top (y : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ w : ℍ, V ≤ w.im → |(w : ℂ).re| ≤ R →
      ‖ckmrvLeechHatKernel (imagPt y) w‖ ≤ C * (1 + w.im) * Real.exp (2 * π * w.im) := by
  obtain ⟨C, V, hC, h⟩ := exists_bound_leech_top (-1) y hR
  refine ⟨C, V, hC, fun w hw hre => ?_⟩
  have b := h w hw hre
  rwa [show (ckmrvLeechPlusKernel (imagPt y) w + -1 * ckmrvLeechMinusKernel (imagPt y) w) / 2 =
    ckmrvLeechHatKernel (imagPt y) w by simp only [ckmrvLeechHatKernel]; ring] at b

/-! ## The closed triangles near the cusps -/

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is bounded near the cusp `0` of `(0, 1, ∞)`. -/
theorem exists_bound_leechHat_cusp0 (τ : ℍ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ →
      ‖rightC ckmrvLeechHatKernel τ z‖ ≤ M := by
  obtain ⟨C, V, _, hV1, hb⟩ := exists_bound_leechKernels_S τ
  have hV : 0 < V := by linarith
  refine ⟨1 / (2 * V), C, by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith,
    fun z hz hzn => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by simp [h, idealTriangleCl] at hz
  have hsmall : ‖z‖ ≤ 1 / 2 := hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hh := horn_zero_bounds hz.1 hz.2.1 (cl_re_le_normSq hz) hsmall
  have hIm : V ≤ (-1 / z).im := (one_div_two_mul_ge hV hz0 hzn).trans hh.2
  have hw : 0 < (-1 / z).im := lt_of_lt_of_le hV hIm
  have e : rightC ckmrvLeechHatKernel τ z =
      ckmrvLeechHatKernel τ (ModularGroup.S • (⟨-1 / z, hw⟩ : ℍ)) := by
    simp only [rightC]
    rw [← ofComplex_neg_inv hz.1, ofComplex_apply_of_im_pos hw]
  rw [e]
  exact (hb ⟨-1 / z, hw⟩ hIm).1

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is bounded near `0` on the closed triangle `(−1, 0, ∞)`. -/
theorem exists_bound_leechHat_shift_cusp1 (τ : ℍ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ →
      ‖rightC ckmrvLeechHatKernel τ (z - 1)‖ ≤ M := by
  obtain ⟨C, V, _, hV1, hb⟩ := exists_bound_leechKernels_S τ
  have hV : 0 < V := by linarith
  refine ⟨1 / (2 * V), C, by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith,
    fun z hz hzn => ?_⟩
  set u := z - 1 with hu
  have huim : 0 < u.im := by simpa [hu] using hz.1
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr fun h => by simp [h] at huim
  have hsmall : ‖u‖ ≤ 1 / 2 := hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hure : u.re ≤ 0 := by simp [hu]; linarith [hz.2.2.1]
  have hh := horn_one_bounds huim hure (cl_neg_re_sub_one_le hz) hsmall
  have hIm : V ≤ (-1 / u).im := (one_div_two_mul_ge hV hu0 hzn).trans hh.2
  have hw : 0 < (-1 / u).im := lt_of_lt_of_le hV hIm
  have e : rightC ckmrvLeechHatKernel τ u =
      ckmrvLeechHatKernel τ (ModularGroup.S • (⟨-1 / u, hw⟩ : ℍ)) := by
    simp only [rightC]
    rw [← ofComplex_neg_inv huim, ofComplex_apply_of_im_pos hw]
  rw [e]
  exact (hb ⟨-1 / u, hw⟩ hIm).1

/-- Near the cusp `1` of `(0, 1, ∞)`: `(z − 1)¹⁰ (𝒦(iy, w) − f(−iw))`, `w = z/(1 − z)`, is bounded.
By `𝒦̂ = 𝒦 |_{−10} STS` this is `𝒦̂(iy, z)` minus its cusp part `P₁(z)`. -/
theorem exists_bound_leech_cusp1 (y : ℝ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ →
      ‖(z - 1) ^ 10 * (rightC ckmrvLeechKernel (imagPt y) (z / (1 - z)) -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * (z / (1 - z))))‖ ≤ M := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_leechKernel_sub_growth y (R := 1) zero_le_one
  set W := max V 1
  have hW : 0 < W := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / (2 * W), C, by positivity,
    by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1], fun z hz hzn => ?_⟩
  set u := z - 1 with hu
  have huim : 0 < u.im := by simpa [hu] using hz.1
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr fun h => by simp [h] at huim
  have hsmall : ‖u‖ ≤ 1 / 2 :=
    hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1])
  have hure : u.re ≤ 0 := by simp [hu]; linarith [hz.2.2.1]
  have hh := horn_one_bounds huim hure (cl_neg_re_sub_one_le hz) hsmall
  have hIm : W ≤ (-1 / u).im := (one_div_two_mul_ge hW hu0 hzn).trans hh.2
  have hu1 : u ≠ 0 := fun h => by simp [h] at huim
  have hw : z / (1 - z) = -1 + -1 / u := div_one_sub_eq_neg_one_add hu1
  have hwim : (z / (1 - z)).im = (-1 / u).im := by rw [hw]; simp
  have hwre : |(z / (1 - z)).re| ≤ 1 := by
    rw [hw, Complex.add_re, abs_le]
    simp only [Complex.neg_re, Complex.one_re]
    constructor <;> linarith [hh.1.1, hh.1.2]
  have hwpos : 0 < (z / (1 - z)).im := by rw [hwim]; linarith [le_max_right V 1]
  have hb' := hb ⟨z / (1 - z), hwpos⟩ (by
    show V ≤ (z / (1 - z)).im
    rw [hwim]
    exact le_trans (le_max_left _ _) hIm) hwre
  have e : rightC ckmrvLeechKernel (imagPt y) (z / (1 - z)) =
      ckmrvLeechKernel (imagPt y) ⟨z / (1 - z), hwpos⟩ := by
    simp only [rightC]
    rw [ofComplex_apply_of_im_pos hwpos]
  rw [e, norm_mul, norm_pow]
  have hkey : (⟨z / (1 - z), hwpos⟩ : ℍ).im ≤ 1 / ‖u‖ := by
    show (z / (1 - z)).im ≤ 1 / ‖u‖
    rw [hwim]
    exact im_neg_one_div_le huim
  have hb'' : ‖ckmrvLeechKernel (imagPt y) ⟨z / (1 - z), hwpos⟩ -
      growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * (z / (1 - z)))‖ ≤
        C * (1 + 1 / ‖u‖) :=
    hb'.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  have hpow : ‖u‖ ^ 10 * (1 + 1 / ‖u‖) ≤ 1 := by
    have e1 : ‖u‖ ^ 10 * (1 + 1 / ‖u‖) = ‖u‖ ^ 10 + ‖u‖ ^ 9 := by
      field_simp
    have h9 : ‖u‖ ^ 9 ≤ (1 / 2 : ℝ) ^ 9 := pow_le_pow_left₀ hu0.le hsmall 9
    have h10 : ‖u‖ ^ 10 ≤ (1 / 2 : ℝ) ^ 10 := pow_le_pow_left₀ hu0.le hsmall 10
    rw [e1]
    norm_num at h9 h10
    linarith
  calc ‖u‖ ^ 10 * ‖ckmrvLeechKernel (imagPt y) ⟨z / (1 - z), hwpos⟩ -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * (z / (1 - z)))‖
      ≤ ‖u‖ ^ 10 * (C * (1 + 1 / ‖u‖)) := mul_le_mul_of_nonneg_left hb'' (by positivity)
    _ = C * (‖u‖ ^ 10 * (1 + 1 / ‖u‖)) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

/-- Near the cusp `−1` of `(−1, 0, ∞)` (that is, `z` near `0` and `u = z − 1`):
`(u + 1)¹⁰ (𝒦(iy, w) − f(−iw))`, `w = u/(u + 1)`, is bounded. -/
theorem exists_bound_leech_shift_cusp0 (y : ℝ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ →
      ‖(z - 1 + 1) ^ 10 * (rightC ckmrvLeechKernel (imagPt y) ((z - 1) / (z - 1 + 1)) -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1)
          (-I * ((z - 1) / (z - 1 + 1))))‖ ≤ M := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_leechKernel_sub_growth y (R := 1) zero_le_one
  set W := max V 1
  have hW : 0 < W := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / (2 * W), C, by positivity,
    by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1], fun z hz hzn => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by simp [h, idealTriangleCl] at hz
  have hsmall : ‖z‖ ≤ 1 / 2 :=
    hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1])
  have hh := horn_zero_bounds hz.1 hz.2.1 (cl_re_le_normSq hz) hsmall
  have hIm : W ≤ (-1 / z).im := (one_div_two_mul_ge hW hz0 hzn).trans hh.2
  have hz00 : z ≠ 0 := fun h => by simp [h] at hz0
  have hw : (z - 1) / (z - 1 + 1) = 1 + -1 / z := by
    rw [sub_add_cancel]
    field_simp
    ring
  have hwim : ((z - 1) / (z - 1 + 1)).im = (-1 / z).im := by rw [hw]; simp
  have hwre : |((z - 1) / (z - 1 + 1)).re| ≤ 1 := by
    rw [hw, Complex.add_re, abs_le]
    simp only [Complex.one_re]
    constructor <;> linarith [hh.1.1, hh.1.2]
  have hwpos : 0 < ((z - 1) / (z - 1 + 1)).im := by rw [hwim]; linarith [le_max_right V 1]
  have hb' := hb ⟨(z - 1) / (z - 1 + 1), hwpos⟩ (by
    show V ≤ ((z - 1) / (z - 1 + 1)).im
    rw [hwim]
    exact le_trans (le_max_left _ _) hIm) hwre
  have e : rightC ckmrvLeechKernel (imagPt y) ((z - 1) / (z - 1 + 1)) =
      ckmrvLeechKernel (imagPt y) ⟨(z - 1) / (z - 1 + 1), hwpos⟩ := by
    simp only [rightC]
    rw [ofComplex_apply_of_im_pos hwpos]
  rw [e, norm_mul, norm_pow, show ‖z - 1 + 1‖ = ‖z‖ by rw [sub_add_cancel]]
  have hkey : (⟨(z - 1) / (z - 1 + 1), hwpos⟩ : ℍ).im ≤ 1 / ‖z‖ := by
    show ((z - 1) / (z - 1 + 1)).im ≤ 1 / ‖z‖
    rw [hwim]
    exact im_neg_one_div_le hz.1
  have hb'' : ‖ckmrvLeechKernel (imagPt y) ⟨(z - 1) / (z - 1 + 1), hwpos⟩ -
      growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * ((z - 1) / (z - 1 + 1)))‖ ≤
        C * (1 + 1 / ‖z‖) :=
    hb'.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  have hpow : ‖z‖ ^ 10 * (1 + 1 / ‖z‖) ≤ 1 := by
    have e1 : ‖z‖ ^ 10 * (1 + 1 / ‖z‖) = ‖z‖ ^ 10 + ‖z‖ ^ 9 := by
      field_simp
    have h9 : ‖z‖ ^ 9 ≤ (1 / 2 : ℝ) ^ 9 := pow_le_pow_left₀ hz0.le hsmall 9
    have h10 : ‖z‖ ^ 10 ≤ (1 / 2 : ℝ) ^ 10 := pow_le_pow_left₀ hz0.le hsmall 10
    rw [e1]
    norm_num at h9 h10
    linarith
  calc ‖z‖ ^ 10 * ‖ckmrvLeechKernel (imagPt y) ⟨(z - 1) / (z - 1 + 1), hwpos⟩ -
        growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * ((z - 1) / (z - 1 + 1)))‖
      ≤ ‖z‖ ^ 10 * (C * (1 + 1 / ‖z‖)) := mul_le_mul_of_nonneg_left hb'' (by positivity)
    _ = C * (‖z‖ ^ 10 * (1 + 1 / ‖z‖)) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

end E8Leech
