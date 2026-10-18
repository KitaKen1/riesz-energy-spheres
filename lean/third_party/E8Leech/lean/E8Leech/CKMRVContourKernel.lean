import E8Leech.CKMRVKernelPoles

/-!
# The kernel `𝒦̂(τ, ·)` on the closed ideal triangles

Known answer first: for `τ = iy` (`y ≠ 1`) the only points of the closed triangles
`(0, 1, ∞)` and `(−1, 0, ∞)` (inside `ℍ`) where `j(z) = j(τ)` are the six boundary points
`τ, Sτ, τ ± 1, Sτ ± 1` and the two images of `τ, Sτ` on each semicircle: inside, `j` misses
`[1728, ∞)` (`TriangleSqrtJ`); on the vertical sides `j(it) = j(iy)` only for `t = y, 1/y`; and
the semicircles are mapped onto the imaginary axis by `TS`. Elsewhere `𝒦̂(τ, ·)` is holomorphic.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Holomorphy away from the `j`-coincidence locus -/

theorem eventually_kleinJC_ne_of_ne {z : ℂ} (hz : 0 < z.im) {c : ℂ} (hj : kleinJC z ≠ c) :
    ∀ᶠ w in 𝓝 z, kleinJC w ≠ c := by
  have hc : ContinuousAt kleinJC z := (hasDerivAt_kleinJC ⟨z, hz⟩).continuousAt
  exact hc.eventually_ne hj

theorem differentiableAt_rightC_minus (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC τ₀) :
    DifferentiableAt ℂ (rightC ckmrvEightMinusKernel τ₀) z := by
  have hnum : DifferentiableAt ℂ (eightMinusNumC τ₀) z := by
    unfold eightMinusNumC
    have h1 := (analyticAt_of_upperHalfPlane_mdifferentiable
      (mdifferentiable_eightMinusSingNum (ofComplex (τ₀ : ℂ))) ⟨z, hz⟩).differentiableAt
    have h2 := (analyticAt_of_upperHalfPlane_mdifferentiable
      mdifferentiable_modularDiscriminant ⟨z, hz⟩).differentiableAt
    exact (h1.div h2 (ModularForm.discriminant_ne_zero _)).const_mul _
  have hden : DifferentiableAt ℂ (fun w => kleinJC τ₀ - kleinJC w) z :=
    (differentiableAt_const _).sub (hasDerivAt_kleinJC ⟨z, hz⟩).differentiableAt
  have h := hnum.div hden (sub_ne_zero.mpr (Ne.symm hj))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [rightC, Pi.div_apply]
  rw [← ckmrvEightMinusKernel_eq_numC, UpperHalfPlane.ofComplex_apply]

theorem differentiableAt_rightC_plus (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC τ₀) :
    DifferentiableAt ℂ (rightC ckmrvEightPlusKernel τ₀) z := by
  have hnum : DifferentiableAt ℂ (eightPlusNumC τ₀) z := by
    have h := mdifferentiable_ckmrvEightPlusNormalizedNumerator.comp
      ((mdifferentiable_const (c := ofComplex (τ₀ : ℂ))).prodMk mdifferentiable_id)
    exact (analyticAt_of_upperHalfPlane_mdifferentiable h ⟨z, hz⟩).differentiableAt
  have hden : DifferentiableAt ℂ (fun w => kleinJC τ₀ - kleinJC w) z :=
    (differentiableAt_const _).sub (hasDerivAt_kleinJC ⟨z, hz⟩).differentiableAt
  have h := hnum.div hden (sub_ne_zero.mpr (Ne.symm hj))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_kleinJC_ne_of_ne hz hj] with w hw
  simp only [rightC, Pi.div_apply]
  have e := ckmrvEightPlusKernel_eq_numC (τ := (τ₀ : ℂ)) (z := w)
    (by rw [show kleinJC (τ₀ : ℂ) = kleinJC τ₀ from rfl]; exact Ne.symm hw)
  rw [UpperHalfPlane.ofComplex_apply] at e
  exact e

theorem differentiableAt_rightC_hatKernel (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC τ₀) :
    DifferentiableAt ℂ (rightC ckmrvEightHatKernel τ₀) z := by
  have h := ((differentiableAt_rightC_plus τ₀ hz hj).sub
    (differentiableAt_rightC_minus τ₀ hz hj)).div_const 2
  exact h

/-! ## Where `j(z) = j(iy)` on the closed triangles -/

theorem re_TS_smul_eq_zero_of_semicircle (z : ℍ) (hz : ‖(z : ℂ) - 1 / 2‖ = 1 / 2) :
    ((ModularGroup.T • ModularGroup.S • z : ℍ) : ℂ).re = 0 := by
  have hns : Complex.normSq z = (z : ℂ).re := by
    have h2 : Complex.normSq ((z : ℂ) - 1 / 2) = 1 / 4 := by
      rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    have e : Complex.normSq ((z : ℂ) - 1 / 2) = Complex.normSq (z : ℂ) - (z : ℂ).re + 1 / 4 := by
      rw [Complex.normSq_apply, Complex.normSq_apply]; simp; ring
    linarith
  have hpos : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.mpr (ne_zero z)
  have hre0 : (z : ℂ).re ≠ 0 := by rw [← hns]; exact hpos.ne'
  rw [coe_T_smul, coe_S_smul, Complex.add_re, Complex.div_re]
  simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
    zero_mul, zero_div, add_zero]
  rw [hns]
  field_simp [hpos.ne']
  ring

theorem eq_or_eq_inv_of_kleinJC_eq {y : ℝ} (hy : 0 < y) (w : ℍ) (hw : (w : ℂ).re = 0)
    (hj : kleinModularJ w = kleinModularJ (imagPt y)) :
    (w : ℂ) = (imagPt y : ℂ) ∨ (w : ℂ) = (imagPt y⁻¹ : ℂ) := by
  rw [eq_imagPt_of_re_eq_zero w hw] at hj ⊢
  rcases kleinModularJ_imagPt_eq hy w.im_pos hj.symm with h | h <;> rw [h] <;> simp

/-- The points of the closed triangle `(0, 1, ∞)` where `j(z) = j(iy)`. -/
theorem kleinJC_eq_imagPt_of_mem_cl {y : ℝ} (hy : 0 < y) {z : ℂ} (hz : z ∈ idealTriangleCl)
    (hj : kleinJC z = kleinJC (imagPt y)) :
    z = (imagPt y : ℂ) ∨ z = (imagPt y⁻¹ : ℂ) ∨ z = (imagPt y : ℂ) + 1 ∨
      z = (imagPt y⁻¹ : ℂ) + 1 ∨ z = -1 / ((imagPt y : ℂ) - 1) ∨
        z = -1 / ((imagPt y⁻¹ : ℂ) - 1) := by
  have hjy : kleinJC (imagPt y) = kleinModularJ (imagPt y) := by
    rw [kleinJC, UpperHalfPlane.ofComplex_apply]
  rw [hjy] at hj
  rcases hz with ⟨him, hre0, hre1, hc⟩
  by_cases hin : z ∈ idealTriangle
  · exact absurd hj (kleinModularJ_ne_imagPt_of_triangle (Or.inl hin) hy)
  have hside : z.re = 0 ∨ z.re = 1 ∨ ‖z - 1 / 2‖ = 1 / 2 := by
    by_contra h
    simp only [not_or] at h
    exact hin ⟨him, lt_of_le_of_ne hre0 (Ne.symm h.1), lt_of_le_of_ne hre1 h.2.1,
      lt_of_le_of_ne hc (Ne.symm h.2.2)⟩
  let w : ℍ := ⟨z, him⟩
  have hwz : ofComplex z = w := ofComplex_apply_of_im_pos him
  rw [kleinJC, hwz] at hj
  rcases hside with h | h | h
  · rcases eq_or_eq_inv_of_kleinJC_eq hy w h hj with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · let u : ℍ := ⟨z - 1, by simpa using him⟩
    have hu : ModularGroup.T • u = w := by
      apply UpperHalfPlane.ext; rw [coe_T_smul]; simp [u, w]
    have hure : (u : ℂ).re = 0 := by simp [u, h]
    rw [← hu, kleinModularJ_T] at hj
    rcases eq_or_eq_inv_of_kleinJC_eq hy u hure hj with h' | h'
    · right; right; left
      have : z - 1 = (imagPt y : ℂ) := h'
      linear_combination this
    · right; right; right; left
      have : z - 1 = (imagPt y⁻¹ : ℂ) := h'
      linear_combination this
  · have hre := re_TS_smul_eq_zero_of_semicircle w h
    rw [← kleinModularJ_S w, ← kleinModularJ_T (ModularGroup.S • w)] at hj
    have hz0 : z ≠ 0 := fun h0 => by simp [h0] at him
    have hcoe : ((ModularGroup.T • ModularGroup.S • w : ℍ) : ℂ) = -1 / z + 1 := by
      rw [coe_T_smul, coe_S_smul]
    rcases eq_or_eq_inv_of_kleinJC_eq hy _ hre hj with h' | h'
    · right; right; right; right; left
      rw [hcoe] at h'
      have h1 : (imagPt y : ℂ) - 1 = -1 / z := by rw [← h']; ring
      rw [h1]; field_simp
    · right; right; right; right; right
      rw [hcoe] at h'
      have h1 : (imagPt y⁻¹ : ℂ) - 1 = -1 / z := by rw [← h']; ring
      rw [h1]; field_simp

/-! ## Growth of the kernels in the right variable -/

theorem exists_bound_of_isBigO_atImInfty {f : ℍ → ℂ} {g : ℍ → ℝ}
    (h : f =O[atImInfty] g) : ∃ c V : ℝ, 0 < c ∧ ∀ z : ℍ, V ≤ z.im → ‖f z‖ ≤ c * ‖g z‖ := by
  obtain ⟨c, hc, hev⟩ := h.exists_pos
  rw [Asymptotics.IsBigOWith, Filter.eventually_iff, atImInfty_mem] at hev
  obtain ⟨V, hV⟩ := hev
  exact ⟨c, V, hc, fun z hz => hV z hz⟩

theorem norm_coe_le_of_re (z : ℍ) {R : ℝ} (hR : |(z : ℂ).re| ≤ R) : ‖(z : ℂ)‖ ≤ R + z.im := by
  have h := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
  have him : |(z : ℂ).im| = z.im := abs_of_pos z.im_pos
  rw [him] at h
  linarith

/-- Linear growth of `K₋⁽⁸⁾(τ, z)` at `i∞` in a vertical strip. -/
theorem exists_bound_minus_top (τ : ℍ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ z : ℍ, V ≤ z.im → |(z : ℂ).re| ≤ R →
      ‖ckmrvEightMinusKernel τ z‖ ≤ C * (1 + z.im) := by
  obtain ⟨c, V, hc, hb⟩ := exists_bound_of_isBigO_atImInfty (isBigO_ckmrvEightMinusKernel_sub_G τ)
  set A := ‖ckmrvMinusScale⁻¹‖ * (‖eightMinusTauCoeff 0 τ‖ * (4 * Real.log 2) +
    ‖eightMinusTauCoeff 1 τ‖ + ‖eightMinusTauCoeff 2 τ‖)
  set B := ‖ckmrvMinusScale⁻¹‖ * (‖eightMinusTauCoeff 0 τ‖ * π)
  refine ⟨(A + B * (R + 1)) + c * (R + 1), max V 1, by positivity, fun z hz hre => ?_⟩
  have hV : V ≤ z.im := le_trans (le_max_left _ _) hz
  have h1 : 1 ≤ z.im := le_trans (le_max_right _ _) hz
  have hzn := norm_coe_le_of_re z hre
  have hG : ‖ckmrvEightMinusG τ z‖ ≤ A + B * ‖(z : ℂ)‖ := by
    simp only [ckmrvEightMinusG, A, B]
    rw [norm_mul, norm_neg]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : ‖(π : ℂ) * I * z + 4 * Real.log 2‖ ≤ π * ‖(z : ℂ)‖ + 4 * Real.log 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      have : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ = 4 * Real.log 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]; norm_num
      linarith
    have e1 := norm_add_le (eightMinusTauCoeff 0 τ * (π * I * z + 4 * Real.log 2) +
      eightMinusTauCoeff 1 τ) (eightMinusTauCoeff 2 τ)
    have e2 := norm_add_le (eightMinusTauCoeff 0 τ * (π * I * z + 4 * Real.log 2))
      (eightMinusTauCoeff 1 τ)
    have e3 : ‖eightMinusTauCoeff 0 τ * (π * I * z + 4 * Real.log 2)‖ ≤
        ‖eightMinusTauCoeff 0 τ‖ * (π * ‖(z : ℂ)‖ + 4 * Real.log 2) := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    have hs := norm_nonneg ckmrvMinusScale⁻¹
    calc ‖ckmrvMinusScale⁻¹‖ * ‖eightMinusTauCoeff 0 τ * (π * I * z + 4 * Real.log 2) +
          eightMinusTauCoeff 1 τ + eightMinusTauCoeff 2 τ‖
        ≤ ‖ckmrvMinusScale⁻¹‖ * (‖eightMinusTauCoeff 0 τ‖ * (π * ‖(z : ℂ)‖ + 4 * Real.log 2) +
          ‖eightMinusTauCoeff 1 τ‖ + ‖eightMinusTauCoeff 2 τ‖) :=
          mul_le_mul_of_nonneg_left (by linarith) hs
      _ = _ := by ring
  have hdiff := hb z hV
  rw [Real.norm_of_nonneg (by positivity)] at hdiff
  have hexp : Real.exp (-π * z.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hK : ‖ckmrvEightMinusKernel τ z‖ ≤ ‖ckmrvEightMinusG τ z‖ +
      ‖ckmrvEightMinusKernel τ z - ckmrvEightMinusG τ z‖ := by
    have := norm_add_le (ckmrvEightMinusG τ z) (ckmrvEightMinusKernel τ z - ckmrvEightMinusG τ z)
    simpa using this
  have hn0 := norm_nonneg (z : ℂ)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  calc ‖ckmrvEightMinusKernel τ z‖
      ≤ (A + B * ‖(z : ℂ)‖) + c * (‖(z : ℂ)‖ * Real.exp (-π * z.im)) := hK.trans
        (add_le_add hG hdiff)
    _ ≤ (A + B * (R + z.im)) + c * (R + z.im) := by
        gcongr
        calc ‖(z : ℂ)‖ * Real.exp (-π * z.im) ≤ ‖(z : ℂ)‖ * 1 :=
              mul_le_mul_of_nonneg_left hexp hn0
          _ ≤ R + z.im := by linarith
    _ ≤ ((A + B * (R + 1)) + c * (R + 1)) * (1 + z.im) := by
        have hv : (0 : ℝ) ≤ z.im := by linarith
        nlinarith [mul_nonneg hA hv, mul_nonneg (mul_nonneg hB hR) hv,
          mul_nonneg (mul_nonneg hc.le hR) hv]

/-- A generic version: `K = G + O(g)` with `G` affine in `z` and `g` linear in the strip. -/
theorem exists_bound_top_of {K Gf : ℍ → ℂ} {g : ℍ → ℝ}
    (hO : (fun z => K z - Gf z) =O[atImInfty] g) {A B R D V₀ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hG : ∀ z : ℍ, ‖Gf z‖ ≤ A + B * ‖(z : ℂ)‖)
    (hg : ∀ z : ℍ, V₀ ≤ z.im → |(z : ℂ).re| ≤ R → ‖g z‖ ≤ D * (1 + z.im)) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ z : ℍ, V ≤ z.im → |(z : ℂ).re| ≤ R → ‖K z‖ ≤ C * (1 + z.im) := by
  obtain ⟨c, V, hc, hb⟩ := exists_bound_of_isBigO_atImInfty hO
  refine ⟨A + B * (R + 1) + c * D, max V V₀ ⊔ 0, by positivity, fun z hz hre => ?_⟩
  have hV : V ≤ z.im := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hV₀ : V₀ ≤ z.im := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hv : 0 ≤ z.im := z.im_pos.le
  have hzn := norm_coe_le_of_re z hre
  have hK : ‖K z‖ ≤ ‖Gf z‖ + ‖K z - Gf z‖ := by
    have := norm_add_le (Gf z) (K z - Gf z)
    simpa using this
  have h1 := hG z
  have h2 := hb z hV
  have h3 := hg z hV₀ hre
  calc ‖K z‖ ≤ (A + B * ‖(z : ℂ)‖) + c * (D * (1 + z.im)) :=
        hK.trans (add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hc.le)))
    _ ≤ (A + B * (R + z.im)) + c * (D * (1 + z.im)) := by gcongr
    _ ≤ (A + B * (R + 1) + c * D) * (1 + z.im) := by
        nlinarith [mul_nonneg hA hv, mul_nonneg (mul_nonneg hB hR) hv]

theorem one_add_mul_exp_neg_le (v : ℝ) (hv : 0 ≤ v) : (1 + v) * Real.exp (-(2 * π) * v) ≤ 1 := by
  have h := Real.add_one_le_exp ((2 * π) * v)
  have hpos := Real.exp_pos ((2 * π) * v)
  rw [show -(2 * π) * v = -((2 * π) * v) by ring, Real.exp_neg]
  rw [mul_inv_le_iff₀ hpos, one_mul]
  nlinarith [Real.pi_gt_three]

/-- Linear growth of `K₊⁽⁸⁾(τ, z)` at `i∞` in a vertical strip. -/
theorem exists_bound_plus_top (τ : ℍ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ z : ℍ, V ≤ z.im → |(z : ℂ).re| ≤ R →
      ‖ckmrvEightPlusKernel τ z‖ ≤ C * (1 + z.im) := by
  set a := ckmrvPlusScale⁻¹ * (12 * (Complex.I / (Real.pi : ℂ)) *
    (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))
  set b := ckmrvPlusScale⁻¹ * (36 / (Real.pi : ℂ) ^ 2 * (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ))
  refine exists_bound_top_of (isBigO_ckmrvEightPlusKernel_sub_G τ) (A := ‖b‖) (B := ‖a‖)
    (D := (R + 1) ^ 2) (V₀ := 0) (norm_nonneg _) (norm_nonneg _) hR (by positivity) ?_ ?_
  · intro z
    have e : ckmrvEightPlusG τ z = a * z + b := by simp only [ckmrvEightPlusG, a, b]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    linarith
  · intro z _ hre
    have hv : 0 ≤ z.im := z.im_pos.le
    have hzn := norm_coe_le_of_re z hre
    rw [Real.norm_of_nonneg (by positivity)]
    have hE := one_add_mul_exp_neg_le z.im hv
    have hsq : ‖(z : ℂ)‖ ^ 2 ≤ ((R + 1) * (1 + z.im)) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _); nlinarith
    have hpos := Real.exp_pos (-2 * π * z.im)
    have e : Real.exp (-2 * π * z.im) = Real.exp (-(2 * π) * z.im) := by ring_nf
    calc ‖(z : ℂ)‖ ^ 2 * Real.exp (-2 * π * z.im)
        ≤ ((R + 1) * (1 + z.im)) ^ 2 * Real.exp (-2 * π * z.im) :=
          mul_le_mul_of_nonneg_right hsq hpos.le
      _ = (R + 1) ^ 2 * (1 + z.im) * ((1 + z.im) * Real.exp (-(2 * π) * z.im)) := by
          rw [e]; ring
      _ ≤ (R + 1) ^ 2 * (1 + z.im) * 1 := by
          apply mul_le_mul_of_nonneg_left hE; positivity
      _ = (R + 1) ^ 2 * (1 + z.im) := by ring

/-- Linear growth of `𝒦̂⁽⁸⁾(τ, z)` and `𝒦⁽⁸⁾(τ, z)` at `i∞` in a vertical strip. -/
theorem exists_bound_hatKernel_top (τ : ℍ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ z : ℍ, V ≤ z.im → |(z : ℂ).re| ≤ R →
      ‖ckmrvEightHatKernel τ z‖ ≤ C * (1 + z.im) ∧ ‖ckmrvEightKernel τ z‖ ≤ C * (1 + z.im) := by
  obtain ⟨C₁, V₁, hC₁, h₁⟩ := exists_bound_plus_top τ hR
  obtain ⟨C₂, V₂, hC₂, h₂⟩ := exists_bound_minus_top τ hR
  refine ⟨C₁ + C₂, max V₁ V₂, by positivity, fun z hz hre => ?_⟩
  have hp := h₁ z (le_trans (le_max_left _ _) hz) hre
  have hm := h₂ z (le_trans (le_max_right _ _) hz) hre
  have hv : 0 ≤ 1 + z.im := by linarith [z.im_pos]
  constructor
  · simp only [ckmrvEightHatKernel, norm_div, Complex.norm_ofNat]
    have := norm_sub_le (ckmrvEightPlusKernel τ z) (ckmrvEightMinusKernel τ z)
    nlinarith
  · simp only [ckmrvEightKernel, norm_div, Complex.norm_ofNat]
    have := norm_add_le (ckmrvEightPlusKernel τ z) (ckmrvEightMinusKernel τ z)
    nlinarith

/-- Boundedness of `K(τ, S w)` for `Im w` large (the cusp `0` in the right variable). -/
theorem exists_bound_hatKernel_S (τ : ℍ) :
    ∃ C V : ℝ, 0 ≤ C ∧ 1 ≤ V ∧ ∀ w : ℍ, V ≤ w.im →
      ‖ckmrvEightHatKernel τ (ModularGroup.S • w)‖ ≤ C ∧
        ‖ckmrvEightKernel τ (ModularGroup.S • w)‖ ≤ C := by
  obtain ⟨c₁, V₁, hc₁, h₁⟩ := exists_bound_of_isBigO_atImInfty (isBigO_ckmrvEightPlusKernel_S_right τ)
  obtain ⟨c₂, V₂, hc₂, h₂⟩ :=
    exists_bound_of_isBigO_atImInfty (isBigO_ckmrvEightMinusKernel_S_right τ)
  refine ⟨c₁ + c₂, max (max V₁ V₂) 1, by positivity, le_max_right _ _, fun w hw => ?_⟩
  have hw1 : 1 ≤ w.im := le_trans (le_max_right _ _) hw
  have hn : 1 ≤ ‖(w : ℂ)‖ ^ 2 := by
    have := Complex.abs_im_le_norm (w : ℂ)
    have h := abs_of_pos w.im_pos
    have : 1 ≤ ‖(w : ℂ)‖ := by
      have : w.im ≤ ‖(w : ℂ)‖ := by
        rw [show w.im = |(w : ℂ).im| from h.symm]; exact Complex.abs_im_le_norm _
      linarith
    nlinarith
  have bound : ∀ (K : ℍ → ℍ → ℂ) (c : ℝ) (k : ℝ), 0 < c → 0 < k →
      ‖K τ (ModularGroup.S • w) * (w : ℂ) ^ 2‖ ≤ c * ‖Real.exp (-k * π * w.im)‖ →
      ‖K τ (ModularGroup.S • w)‖ ≤ c := by
    intro K c k hc hk h
    rw [norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le] at h
    have hexp : Real.exp (-k * π * w.im) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos (mul_pos hk Real.pi_pos) w.im_pos])
    have hK := norm_nonneg (K τ (ModularGroup.S • w))
    nlinarith
  have hp := bound ckmrvEightPlusKernel c₁ 2 hc₁ (by norm_num)
    (by
      have := h₁ w (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hw)
      simpa [mul_assoc] using this)
  have hm := bound ckmrvEightMinusKernel c₂ 1 hc₂ (by norm_num)
    (by
      have := h₂ w (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hw)
      simpa using this)
  constructor
  · simp only [ckmrvEightHatKernel, norm_div, Complex.norm_ofNat]
    have := norm_sub_le (ckmrvEightPlusKernel τ (ModularGroup.S • w))
      (ckmrvEightMinusKernel τ (ModularGroup.S • w))
    linarith
  · simp only [ckmrvEightKernel, norm_div, Complex.norm_ofNat]
    have := norm_add_le (ckmrvEightPlusKernel τ (ModularGroup.S • w))
      (ckmrvEightMinusKernel τ (ModularGroup.S • w))
    linarith

end E8Leech
