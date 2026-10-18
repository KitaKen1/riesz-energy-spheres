import E8Leech.CKMRVLaplaceAxis
import E8Leech.KleinNoncritical
import E8Leech.ModularImaginaryIdentities
import E8Leech.CKMRVPlusInversion
import Mathlib.Analysis.Calculus.Darboux

/-!
# Laplace integrals on the imaginary axis without side conditions

The axis theorems of `CKMRVLaplaceAxis` assume `j'(iβ) ≠ 0` and that `j(it) = j(iβ)` only for
`t = β, β⁻¹`. Both hold for every `β > 0` with `β ≠ 1`:

* `j'(iβ) ≠ 0`: `E₄(iβ) ≥ 1`, and `E₆(iβ) ≠ 0` (positive for `β > 1`; the `S`-transformation
  `E₆(i/β) = (iβ)⁶ E₆(iβ)` handles `β < 1`).
* `t ↦ j(it)` is real, invariant under `t ↦ t⁻¹`, and its derivative `j'(it) i` is real and
  nonzero on `(1, ∞)`. By Darboux's theorem it has constant sign there, so `t ↦ j(it)` is
  strictly monotone, hence injective, on `[1, ∞)`.

For points off the imaginary-axis orbit the condition of `CKMRVLaplace` follows from
`j(τ) ∉ [1728, ∞)`, since `j(it)` is real and at least `1728`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real

theorem kleinImaginaryJ_eq_imagPt (y : ℝ) : kleinImaginaryJ y = kleinModularJ (imagPt y) := rfl

theorem eisensteinFour_imagPt_ne_zero {β : ℝ} (hβ : 0 < β) : ModularForm.E₄ (imagPt β) ≠ 0 := by
  intro h
  have h1 : 1 ≤ (ModularForm.E₄ (imagPt β)).re := eisensteinFour_imaginary_re_lower hβ
  rw [h, zero_re] at h1
  norm_num at h1

theorem eisensteinSix_imagPt_ne_zero_of_one_lt {β : ℝ} (hβ : 1 < β) :
    ModularForm.E₆ (imagPt β) ≠ 0 := by
  intro h
  have h1 : 0 < (ModularForm.E₆ (imagPt β)).re := eisensteinSix_imaginary_re_pos hβ
  rw [h, zero_re] at h1
  exact lt_irrefl _ h1

theorem eisensteinSix_imagPt_ne_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ModularForm.E₆ (imagPt β) ≠ 0 := by
  rcases lt_or_gt_of_ne hβ1 with h | h
  · rw [← S_smul_imagPt_inv hβ, eisensteinSix_S]
    exact mul_ne_zero (pow_ne_zero _ (UpperHalfPlane.ne_zero _))
      (eisensteinSix_imagPt_ne_zero_of_one_lt ((one_lt_inv₀ hβ).mpr h))
  · exact eisensteinSix_imagPt_ne_zero_of_one_lt h

/-- `j'(iβ) ≠ 0` for `β ≠ 1`. -/
theorem kleinModularJDerivative_imagPt_ne_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    kleinModularJDerivative (imagPt β) ≠ 0 :=
  (kleinModularJDerivative_ne_zero_iff _).mpr
    ⟨eisensteinFour_imagPt_ne_zero hβ, eisensteinSix_imagPt_ne_zero hβ hβ1⟩

theorem kleinImaginaryJ_im {y : ℝ} (hy : 0 < y) : (kleinImaginaryJ y).im = 0 := by
  rw [kleinImaginaryJ_eq_q hy, ofReal_im]

theorem kleinImaginaryJ_inv {y : ℝ} (hy : 0 < y) : kleinImaginaryJ y⁻¹ = kleinImaginaryJ y := by
  rw [kleinImaginaryJ_eq_imagPt, kleinImaginaryJ_eq_imagPt, ← S_smul_imagPt_inv hy,
    kleinModularJ_S]

theorem hasDerivAt_kleinImaginaryJ_re {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => (kleinImaginaryJ x).re)
      (kleinModularJDerivative (imagPt y) * I).re y := by
  simpa only [Function.comp_def, reCLM_apply] using!
    reCLM.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_kleinImaginaryJ hy)

/-- The derivative of the real function `t ↦ j(it)` is real. -/
theorem kleinImaginaryJ_deriv_im {y : ℝ} (hy : 0 < y) :
    (kleinModularJDerivative (imagPt y) * I).im = 0 := by
  have h : HasDerivAt (fun x => (kleinImaginaryJ x).im)
      (kleinModularJDerivative (imagPt y) * I).im y := by
    simpa only [Function.comp_def, imCLM_apply] using!
      imCLM.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_kleinImaginaryJ hy)
  have h0 : HasDerivAt (fun x => (kleinImaginaryJ x).im) 0 y := by
    refine (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact kleinImaginaryJ_im hx
  exact h.unique h0

theorem kleinImaginaryJ_deriv_re_ne_zero {y : ℝ} (hy : 1 < y) :
    (kleinModularJDerivative (imagPt y) * I).re ≠ 0 := by
  intro h
  have h0 : kleinModularJDerivative (imagPt y) * I = 0 :=
    Complex.ext (h.trans zero_re.symm)
      ((kleinImaginaryJ_deriv_im (by linarith : (0 : ℝ) < y)).trans zero_im.symm)
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact kleinModularJDerivative_imagPt_ne_zero (by linarith) hy.ne' h1
  · exact I_ne_zero h1

/-- `t ↦ j(it)` is injective on `[1, ∞)`. -/
theorem injOn_kleinImaginaryJ_re : InjOn (fun y => (kleinImaginaryJ y).re) (Ici 1) := by
  have hpos : ∀ x ∈ Ioi (1 : ℝ), (0 : ℝ) < x := fun x hx => lt_trans one_pos hx
  have hd : ∀ x ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun y => (kleinImaginaryJ y).re)
      ((kleinModularJDerivative (imagPt x) * I).re) (Ioi 1) x := fun x hx =>
    (hasDerivAt_kleinImaginaryJ_re (hpos x hx)).hasDerivWithinAt
  have hcont : ContinuousOn (fun y => (kleinImaginaryJ y).re) (Ici 1) := fun x hx =>
    (hasDerivAt_kleinImaginaryJ_re (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Ici (1 : ℝ)), deriv (fun y => (kleinImaginaryJ y).re) x =
      (kleinModularJDerivative (imagPt x) * I).re := by
    intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivAt_kleinImaginaryJ_re (hpos x hx)).deriv
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioi 1) hd
      (fun x hx => kleinImaginaryJ_deriv_re_ne_zero hx) with h | h
  · refine (strictAntiOn_of_deriv_neg (convex_Ici 1) hcont fun x hx => ?_).injOn
    rw [hderiv x hx]
    rw [interior_Ici] at hx
    exact h x hx
  · refine (strictMonoOn_of_deriv_pos (convex_Ici 1) hcont fun x hx => ?_).injOn
    rw [hderiv x hx]
    rw [interior_Ici] at hx
    exact h x hx

/-- On the imaginary axis, `j(iβ) = j(it)` only for `t = β` and `t = β⁻¹`. -/
theorem kleinModularJ_imagPt_eq {β t : ℝ} (hβ : 0 < β) (ht : 0 < t)
    (h : kleinModularJ (imagPt β) = kleinModularJ (imagPt t)) : t = β ∨ t = β⁻¹ := by
  have key : ∀ y : ℝ, 0 < y → ∃ y' ∈ Ici (1 : ℝ), (y' = y ∨ y' = y⁻¹) ∧
      kleinImaginaryJ y' = kleinImaginaryJ y := by
    intro y hy
    rcases le_total 1 y with h1 | h1
    · exact ⟨y, h1, Or.inl rfl, rfl⟩
    · exact ⟨y⁻¹, (one_le_inv₀ hy).mpr h1, Or.inr rfl, kleinImaginaryJ_inv hy⟩
  obtain ⟨β', hβ'1, hβ'e, hβ'J⟩ := key β hβ
  obtain ⟨t', ht'1, ht'e, ht'J⟩ := key t ht
  have hre : (kleinImaginaryJ β').re = (kleinImaginaryJ t').re := by
    rw [hβ'J, ht'J]
    exact congrArg Complex.re h
  have heq : β' = t' := injOn_kleinImaginaryJ_re hβ'1 ht'1 hre
  rcases hβ'e with hb | hb <;> rcases ht'e with ht2 | ht2 <;> rw [hb, ht2] at heq
  · exact Or.inl heq.symm
  · right
    rw [heq, inv_inv]
  · exact Or.inr heq.symm
  · exact Or.inl (inv_injective heq).symm

theorem kleinModularJ_imagPt_ne {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) (h1 : t ≠ β)
    (h2 : t ≠ β⁻¹) : kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) := fun h =>
  (kleinModularJ_imagPt_eq hβ ht h).elim h1 h2

/-- If `j(τ)` is not a real number `≥ 1728`, then `j(τ) ≠ j(it)` for every `t > 0`. -/
theorem kleinModularJ_ne_imagPt_of_not_real {τ : ℍ}
    (hτ : ¬((kleinModularJ τ).im = 0 ∧ 1728 ≤ (kleinModularJ τ).re)) (t : ℝ) (ht : 0 < t) :
    kleinModularJ τ ≠ kleinModularJ (imagPt t) := by
  intro h
  apply hτ
  rw [h, ← kleinImaginaryJ_eq_imagPt]
  exact ⟨kleinImaginaryJ_im ht, kleinImaginaryJ_re_ge_1728 ht⟩

/-! ### The Laplace integrals -/

theorem integrableOn_ckmrvEightPlusKernel_laplace_imagAxis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1)
    {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightPlusKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_ckmrvEightPlusKernel_laplace_axis hβ hβ1
    (kleinModularJDerivative_imagPt_ne_zero hβ hβ1)
    (fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2) hr

theorem integrableOn_ckmrvLeechPlusKernel_laplace_imagAxis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1)
    {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechPlusKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_ckmrvLeechPlusKernel_laplace_axis hβ hβ1
    (kleinModularJDerivative_imagPt_ne_zero hβ hβ1)
    (fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2) hr

theorem integrableOn_ckmrvEightMinusKernel_laplace_of_not_real {τ : ℍ}
    (hτ : ¬((kleinModularJ τ).im = 0 ∧ 1728 ≤ (kleinModularJ τ).re)) {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightMinusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_ckmrvEightMinusKernel_laplace τ (kleinModularJ_ne_imagPt_of_not_real hτ) hr

theorem integrableOn_ckmrvEightPlusKernel_laplace_of_not_real {τ : ℍ}
    (hτ : ¬((kleinModularJ τ).im = 0 ∧ 1728 ≤ (kleinModularJ τ).re)) {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightPlusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_ckmrvEightPlusKernel_laplace τ (kleinModularJ_ne_imagPt_of_not_real hτ) hr

theorem integrableOn_ckmrvLeechMinusKernel_laplace_of_not_real {τ : ℍ}
    (hτ : ¬((kleinModularJ τ).im = 0 ∧ 1728 ≤ (kleinModularJ τ).re)) {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechMinusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_ckmrvLeechMinusKernel_laplace τ (kleinModularJ_ne_imagPt_of_not_real hτ) hr

theorem integrableOn_ckmrvLeechPlusKernel_laplace_of_not_real {τ : ℍ}
    (hτ : ¬((kleinModularJ τ).im = 0 ∧ 1728 ≤ (kleinModularJ τ).re)) {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechPlusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_ckmrvLeechPlusKernel_laplace τ (kleinModularJ_ne_imagPt_of_not_real hτ) hr

end E8Leech
