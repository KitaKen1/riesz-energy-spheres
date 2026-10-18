import E8Leech.IdealTriangleCauchy
import E8Leech.CKMRVLaplaceAxisClean
import E8Leech.CKMRVGrowth
import E8Leech.CKMRVGrowthLeech
import E8Leech.CKMRVKernelInversion
import E8Leech.ThetaFunctions
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.OpenMapping

/-!
# `j` takes no value in `[1728, ∞)` inside the ideal triangle `(0, 1, ∞)`

Known answer first: the CKMRV kernels have the denominator `j(τ) − j(z)`, and on the imaginary
axis `j(τ) ∈ [1728, ∞)`. Classically `j` maps the triangle `(0, 1, ∞)` three-to-one onto
`ℂ ∖ [1728, ∞)`; Mathlib has no valence formula, so we argue with a square root instead.

`s = E₆ / η¹²` is holomorphic on `ℍ` with `s² = j − 1728` (`Δ = η²⁴`), `s ∘ T = −s` and
`s ∘ S = −s` (Mathlib's `η` transformation laws). On the three sides of the triangle `j` is real
and `≥ 1728`, so `s` is real there. At the cusps `s e^{πiz} → 1`, which makes `Im s` at most
`O(e^{−π Im})` on the cuts. The maximum modulus principle for `exp(−i s)` gives `Im s ≤ 0` on the
triangle and the open mapping theorem gives `Im s < 0`. Hence `j − 1728 = s² ∉ [0, ∞)` there.
-/

noncomputable section

namespace E8Leech

open Complex Set Filter Topology Asymptotics Bornology
open UpperHalfPlane hiding I
open scoped Real Manifold

local notation "𝕢" => Function.Periodic.qParam

/-! ## The square root `s = E₆ / η¹²` of `j − 1728` -/

/-- `s = E₆ / η¹²`. -/
def sqrtJ (z : ℍ) : ℂ := ModularForm.E₆ z / ModularForm.eta z ^ 12

theorem eta_ne_zero_of_uhp (z : ℍ) : ModularForm.eta z ≠ 0 := ModularForm.eta_ne_zero z.2

theorem sqrtJ_sq (z : ℍ) : sqrtJ z ^ 2 = kleinModularJ z - 1728 := by
  rw [kleinModularJ_sub_1728, sqrtJ, div_pow, ← pow_mul]
  rfl

theorem qParam_add_one_24 (z : ℂ) : 𝕢 24 (z + 1) = cexp (2 * π * I / 24) * 𝕢 24 z := by
  simp only [Function.Periodic.qParam, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eta_q_add_one (n : ℕ) (z : ℂ) : ModularForm.eta_q n (z + 1) = ModularForm.eta_q n z := by
  simp only [ModularForm.eta_q, Function.Periodic.qParam]
  congr 1
  have : (2 * π * I * (z + 1) / ((1 : ℝ) : ℂ)) = 2 * π * I * z / ((1 : ℝ) : ℂ) + 2 * π * I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem eta_pow_twelve_add_one (z : ℂ) :
    ModularForm.eta (z + 1) ^ 12 = -ModularForm.eta z ^ 12 := by
  have h : ModularForm.eta (z + 1) = cexp (2 * π * I / 24) * ModularForm.eta z := by
    simp only [ModularForm.eta, qParam_add_one_24, eta_q_add_one]
    ring
  rw [h, mul_pow, ← Complex.exp_nat_mul]
  have e : ((12 : ℕ) : ℂ) * (2 * π * I / 24) = π * I := by push_cast; ring
  rw [e, Complex.exp_pi_mul_I]
  ring

theorem csqrt_pow_twelve {w : ℂ} (hw : w ≠ 0) : Complex.sqrt w ^ 12 = w ^ 6 := by
  rw [_root_.sqrt_eq_exp hw, ← Complex.exp_nat_mul]
  have e : ((12 : ℕ) : ℂ) * (Complex.log w / 2) = ((6 : ℕ) : ℂ) * Complex.log w := by
    push_cast; ring
  rw [e, Complex.exp_nat_mul, Complex.exp_log hw]

theorem eta_pow_twelve_S (z : ℍ) :
    ModularForm.eta (-(z : ℂ)⁻¹) ^ 12 = -(z : ℂ) ^ 6 * ModularForm.eta z ^ 12 := by
  have he : ModularForm.eta (-(z : ℂ)⁻¹) =
      (Complex.sqrt I)⁻¹ * (Complex.sqrt z * ModularForm.eta z) := by
    simpa [neg_div] using ModularForm.eta_comp_eq_csqrt_I_inv z.2
  have hI : Complex.sqrt I ^ 12 = -1 := by
    rw [csqrt_pow_twelve I_ne_zero]
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, I_sq]
    norm_num
  rw [he, mul_pow, mul_pow, inv_pow, hI, csqrt_pow_twelve (ne_zero z)]
  ring

theorem sqrtJ_T (z : ℍ) : sqrtJ (ModularGroup.T • z) = -sqrtJ z := by
  have hE : ModularForm.E₆ (ModularGroup.T • z) = ModularForm.E₆ z := by
    rw [← vadd_one_eq_T_smul]
    exact eisensteinSix_vadd_one z
  rw [sqrtJ, sqrtJ, hE, coe_T_smul, eta_pow_twelve_add_one, div_neg]

theorem sqrtJ_S (z : ℍ) : sqrtJ (ModularGroup.S • z) = -sqrtJ z := by
  have hη := eta_ne_zero_of_uhp z
  have hz := ne_zero z
  rw [sqrtJ, sqrtJ, eisensteinSix_S, coe_S_smul, show -1 / (z : ℂ) = -(z : ℂ)⁻¹ by ring,
    eta_pow_twelve_S]
  field_simp

theorem mdifferentiable_eta_uhp : MDiff (fun z : ℍ => ModularForm.eta (z : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro w hw
  have h := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw).differentiableWithinAt
    (s := {z : ℂ | 0 < z.im})
  refine h.congr (fun x hx => ?_) ?_
  · simp [Function.comp, ofComplex_apply_of_im_pos hx]
  · simp [Function.comp, ofComplex_apply_of_im_pos hw]

theorem mdifferentiable_sqrtJ : MDiff sqrtJ :=
  (ModularFormClass.holo ModularForm.E₆).div (mdifferentiable_eta_uhp.pow 12)
    fun z => pow_ne_zero 12 (eta_ne_zero_of_uhp z)

/-! ## The cusp `i∞` -/

/-- The `η`-product without its `q^{1/24}` factor. -/
def etaProduct (z : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n z)

theorem qParam_24_pow_twelve (z : ℂ) : 𝕢 24 z ^ 12 = cexp (π * I * z) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem sqrtJ_mul_exp (z : ℍ) :
    sqrtJ z * cexp (π * I * z) = ModularForm.E₆ z / etaProduct z ^ 12 := by
  have hη := eta_ne_zero_of_uhp z
  have hη' : ModularForm.eta z = 𝕢 24 z * etaProduct z := rfl
  have hq : 𝕢 24 z ≠ 0 := by simp [Function.Periodic.qParam]
  have hP : etaProduct z ≠ 0 := by
    intro h; apply hη; rw [hη', h, mul_zero]
  rw [sqrtJ, hη', mul_pow, qParam_24_pow_twelve]
  have hexp : cexp (π * I * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem tendsto_etaProduct :
    Tendsto (fun z : ℍ => etaProduct z) atImInfty (𝓝 1) := by
  have htprod : Tendsto (fun q : ℂ ↦ ∏' (n : ℕ), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
    simp_rw [sub_eq_add_neg]
    refine this
      (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
      (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  have := htprod.comp (qParam_tendsto_atImInfty zero_lt_one)
  refine this.congr fun z => ?_
  simp [etaProduct, ModularForm.eta_q, Function.comp]

theorem tendsto_sqrtJ_mul_exp :
    Tendsto (fun z : ℍ => sqrtJ z * cexp (π * I * z)) atImInfty (𝓝 1) := by
  have h := tendsto_eisensteinSix_atImInfty.div (tendsto_etaProduct.pow 12) (by norm_num)
  simp only [one_pow, div_one] at h
  exact h.congr fun z => (sqrtJ_mul_exp z).symm

theorem exists_bound_sqrtJ_mul_exp :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ z : ℍ, V ≤ z.im →
      ‖sqrtJ z * cexp (π * I * z) - 1‖ ≤ C * Real.exp (-2 * π * z.im) := by
  have hT : ∀ z : ℍ, (fun z : ℍ => sqrtJ z * cexp (π * I * z) - 1) (ModularGroup.T • z) =
      (fun z : ℍ => sqrtJ z * cexp (π * I * z) - 1) z := by
    intro z
    simp only
    rw [sqrtJ_T, coe_T_smul]
    have : cexp (π * I * ((z : ℂ) + 1)) = -cexp (π * I * z) := by
      rw [show π * I * ((z : ℂ) + 1) = π * I * z + π * I by ring, Complex.exp_add,
        Complex.exp_pi_mul_I]
      ring
    rw [this]
    ring
  have hdiff : MDiff (fun z : ℍ => sqrtJ z * cexp (π * I * z) - 1) := by
    have hexp : MDiff (fun z : ℍ => cexp (π * I * z)) := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      intro w hw
      refine (Differentiable.differentiableAt (by fun_prop) : DifferentiableAt ℂ
        (fun z : ℂ => cexp (π * I * z)) w).differentiableWithinAt.congr (fun x hx => ?_) ?_
      · simp [Function.comp, ofComplex_apply_of_im_pos hx]
      · simp [Function.comp, ofComplex_apply_of_im_pos hw]
    exact (mdifferentiable_sqrtJ.mul hexp).sub mdifferentiable_const
  have hlim : Tendsto (fun z : ℍ => sqrtJ z * cexp (π * I * z) - 1) atImInfty (𝓝 0) := by
    simpa using tendsto_sqrtJ_mul_exp.sub_const 1
  have hO := isBigO_exp_of_T_invariant hdiff hT hlim
  obtain ⟨C, hC, hev⟩ := hO.exists_pos
  rw [IsBigOWith, Filter.eventually_iff, atImInfty_mem] at hev
  obtain ⟨V, hV⟩ := hev
  refine ⟨C, V, hC.le, fun z hz => ?_⟩
  have := hV z hz
  simpa [Real.norm_of_nonneg (Real.exp_pos _).le] using this

theorem im_neg_exp_neg_pi_I (z : ℂ) :
    (cexp (-(π * I * z))).im = -(Real.exp (π * z.im) * Real.sin (π * z.re)) := by
  have : -(π * I * z) = (π * z.im : ℝ) + ((-(π * z.re) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [this, Complex.exp_add, ← Complex.ofReal_exp, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ring

theorem norm_exp_neg_pi_I (z : ℂ) : ‖cexp (-(π * I * z))‖ = Real.exp (π * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- Near `i∞`, `Im s ≤ C e^{−π Im z}` when `0 ≤ Re z ≤ 1`, and `−Im s ≤ C e^{−π Im z}`
when `−1 ≤ Re z ≤ 0`. -/
theorem exists_bound_im_sqrtJ :
    ∃ C V : ℝ, 0 ≤ C ∧ ∀ z : ℍ, V ≤ z.im →
      (0 ≤ (z : ℂ).re → (z : ℂ).re ≤ 1 → (sqrtJ z).im ≤ C * Real.exp (-π * z.im)) ∧
      (-1 ≤ (z : ℂ).re → (z : ℂ).re ≤ 0 → -(sqrtJ z).im ≤ C * Real.exp (-π * z.im)) := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_sqrtJ_mul_exp
  refine ⟨C, V, hC, fun z hz => ?_⟩
  have hsplit : sqrtJ z = cexp (-(π * I * z)) +
      (sqrtJ z * cexp (π * I * z) - 1) * cexp (-(π * I * z)) := by
    have h1 : cexp (π * I * z) * cexp (-(π * I * z)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    linear_combination (-sqrtJ z) * h1
  have herr : |((sqrtJ z * cexp (π * I * z) - 1) * cexp (-(π * I * z))).im| ≤
      C * Real.exp (-π * z.im) := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, norm_exp_neg_pi_I]
    calc ‖sqrtJ z * cexp (π * I * z) - 1‖ * Real.exp (π * (z : ℂ).im)
        ≤ C * Real.exp (-2 * π * z.im) * Real.exp (π * z.im) :=
          mul_le_mul_of_nonneg_right (hb z hz) (Real.exp_pos _).le
      _ = C * Real.exp (-π * z.im) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hmain : (sqrtJ z).im = -(Real.exp (π * z.im) * Real.sin (π * (z : ℂ).re)) +
      ((sqrtJ z * cexp (π * I * z) - 1) * cexp (-(π * I * z))).im := by
    conv_lhs => rw [hsplit]
    rw [Complex.add_im, im_neg_exp_neg_pi_I]
    rfl
  rw [abs_le] at herr
  have hexp := Real.exp_pos (π * z.im)
  constructor
  · intro h0 h1
    have hs : 0 ≤ Real.sin (π * (z : ℂ).re) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    rw [hmain]; nlinarith
  · intro h0 h1
    have hs : Real.sin (π * (z : ℂ).re) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    rw [hmain]; nlinarith

/-! ## `s` is real on the three sides -/

theorem im_eq_zero_of_sq_nonneg {w : ℂ} (h1 : (w ^ 2).im = 0) (h2 : 0 ≤ (w ^ 2).re) :
    w.im = 0 := by
  rw [sq, Complex.mul_im] at h1
  rw [sq, Complex.mul_re] at h2
  by_contra h
  have hre : w.re = 0 := by
    have h3 : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact h'
    · exact absurd h' h
  rw [hre] at h2
  have : 0 < w.im * w.im := mul_self_pos.mpr h
  linarith

theorem sqrtJ_im_eq_zero (z : ℍ)
    (h : (kleinModularJ z).im = 0 ∧ 1728 ≤ (kleinModularJ z).re) : (sqrtJ z).im = 0 :=
  im_eq_zero_of_sq_nonneg (by rw [sqrtJ_sq]; simp [h.1]) (by rw [sqrtJ_sq]; simp; linarith [h.2])

theorem eq_imagPt_of_re_eq_zero (z : ℍ) (hz : (z : ℂ).re = 0) : z = imagPt z.im := by
  have hz' : z.re = 0 := hz
  apply UpperHalfPlane.ext
  rw [coe_imagPt z.im_pos]
  apply Complex.ext <;> simp [hz']

theorem j_real_of_re_eq_zero (z : ℍ) (hz : (z : ℂ).re = 0) :
    (kleinModularJ z).im = 0 ∧ 1728 ≤ (kleinModularJ z).re := by
  rw [eq_imagPt_of_re_eq_zero z hz, ← kleinImaginaryJ_eq_imagPt]
  exact ⟨kleinImaginaryJ_im z.im_pos, kleinImaginaryJ_re_ge_1728 z.im_pos⟩

theorem j_real_of_re_eq_one (z : ℍ) (hz : (z : ℂ).re = 1) :
    (kleinModularJ z).im = 0 ∧ 1728 ≤ (kleinModularJ z).re := by
  let w : ℍ := ⟨(z : ℂ) - 1, by simpa using z.2⟩
  have hw : ModularGroup.T • w = z := by
    apply UpperHalfPlane.ext; rw [coe_T_smul]; simp [w]
  have hz' : z.re = 1 := hz
  have hwre : (w : ℂ).re = 0 := by simp [w, hz']
  rw [← hw, kleinModularJ_T]
  exact j_real_of_re_eq_zero w hwre

theorem j_real_of_semicircle (z : ℍ) (hz : ‖(z : ℂ) - 1 / 2‖ = 1 / 2) :
    (kleinModularJ z).im = 0 ∧ 1728 ≤ (kleinModularJ z).re := by
  have hns : Complex.normSq z = (z : ℂ).re := by
    have h2 : Complex.normSq ((z : ℂ) - 1 / 2) = 1 / 4 := by
      rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    have e : Complex.normSq ((z : ℂ) - 1 / 2) = Complex.normSq (z : ℂ) - (z : ℂ).re + 1 / 4 := by
      rw [Complex.normSq_apply, Complex.normSq_apply]; simp; ring
    linarith
  have hpos : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.mpr (ne_zero z)
  have hre0 : (z : ℂ).re ≠ 0 := by rw [← hns]; exact hpos.ne'
  have hre : ((ModularGroup.T • ModularGroup.S • z : ℍ) : ℂ).re = 0 := by
    rw [coe_T_smul, coe_S_smul, Complex.add_re, Complex.div_re]
    simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
      zero_mul, zero_div, add_zero]
    rw [hns]
    field_simp [hpos.ne']
    ring
  rw [← kleinModularJ_S z, ← kleinModularJ_T (ModularGroup.S • z)]
  exact j_real_of_re_eq_zero _ hre

/-! ## The function `s` on `ℂ` and its size at the three cusps -/

/-- `s` read on `ℂ` (junk off `ℍ`). -/
def sqrtJC (z : ℂ) : ℂ := sqrtJ (ofComplex z)

theorem sqrtJC_apply {z : ℂ} (hz : 0 < z.im) : sqrtJC z = sqrtJ ⟨z, hz⟩ := by
  rw [sqrtJC, ofComplex_apply_of_im_pos hz]

theorem differentiableOn_sqrtJC : DifferentiableOn ℂ sqrtJC {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_sqrtJ

theorem differentiableAt_sqrtJC {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ sqrtJC z :=
  differentiableOn_sqrtJC.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

/-- In the horn of the triangle at the cusp `0`, the point `−1/z` is high up. -/
theorem horn_zero_bounds {z : ℂ} (him : 0 < z.im) (hre : 0 ≤ z.re)
    (hc : z.re ≤ Complex.normSq z) (hsmall : ‖z‖ ≤ 1 / 2) :
    (-1 / z).re ∈ Icc (-1 : ℝ) 0 ∧ 1 / (2 * ‖z‖) ≤ (-1 / z).im := by
  have hz : z ≠ 0 := fun h => by simp [h] at him
  have hpos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hnorm : ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
  have hn0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hre' : (-1 / z).re = -z.re / Complex.normSq z := by
    rw [Complex.div_re]; simp
  have him' : (-1 / z).im = z.im / Complex.normSq z := by
    rw [Complex.div_im]; norm_num; ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hre', le_div_iff₀ hpos]; linarith
  · rw [hre']; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  · rw [him', div_le_div_iff₀ (by positivity) hpos]
    have hns : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
    have hre2 : z.re * z.re ≤ Complex.normSq z * Complex.normSq z := by
      have := mul_le_mul hc hc hre hpos.le; linarith
    have hq : Complex.normSq z ≤ 1 / 4 := by rw [← hnorm]; nlinarith
    have hzim : ‖z‖ * ‖z‖ ≤ 4 * (z.im * z.im) := by nlinarith
    nlinarith [sq_nonneg (‖z‖ - 2 * z.im)]

/-- In the horn of the triangle `(−1, 0, ∞)` at `0` (that is, `z − 1` near the cusp `1`),
the point `−1/u` is high up over `[0, 1]`. -/
theorem horn_one_bounds {u : ℂ} (him : 0 < u.im) (hre : u.re ≤ 0)
    (hc : -u.re ≤ Complex.normSq u) (hsmall : ‖u‖ ≤ 1 / 2) :
    (-1 / u).re ∈ Icc (0 : ℝ) 1 ∧ 1 / (2 * ‖u‖) ≤ (-1 / u).im := by
  have hu : u ≠ 0 := fun h => by simp [h] at him
  have hpos : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have hnorm : ‖u‖ ^ 2 = Complex.normSq u := (Complex.normSq_eq_norm_sq u).symm
  have hn0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hre' : (-1 / u).re = -u.re / Complex.normSq u := by
    rw [Complex.div_re]; simp
  have him' : (-1 / u).im = u.im / Complex.normSq u := by
    rw [Complex.div_im]; norm_num; ring
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hre']; exact div_nonneg (by linarith) hpos.le
  · rw [hre', div_le_one hpos]; exact hc
  · rw [him', div_le_div_iff₀ (by positivity) hpos]
    have hns : Complex.normSq u = u.re * u.re + u.im * u.im := Complex.normSq_apply u
    have hre2 : u.re * u.re ≤ Complex.normSq u * Complex.normSq u := by
      have := mul_le_mul hc hc (by linarith) hpos.le; nlinarith
    have hq : Complex.normSq u ≤ 1 / 4 := by rw [← hnorm]; nlinarith
    have hzim : ‖u‖ * ‖u‖ ≤ 4 * (u.im * u.im) := by nlinarith
    nlinarith [sq_nonneg (‖u‖ - 2 * u.im)]

theorem sqrtJC_top {C V : ℝ}
    (hb : ∀ z : ℍ, V ≤ z.im →
      (0 ≤ (z : ℂ).re → (z : ℂ).re ≤ 1 → (sqrtJ z).im ≤ C * Real.exp (-π * z.im)) ∧
      (-1 ≤ (z : ℂ).re → (z : ℂ).re ≤ 0 → -(sqrtJ z).im ≤ C * Real.exp (-π * z.im)))
    {z : ℂ} (him : 0 < z.im) (hV : V ≤ z.im) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) :
    (sqrtJC z).im ≤ C * Real.exp (-π * z.im) := by
  rw [sqrtJC_apply him]
  exact (hb ⟨z, him⟩ hV).1 h0 h1

theorem sqrtJC_cusp_zero {C V : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : ℍ, V ≤ z.im →
      (0 ≤ (z : ℂ).re → (z : ℂ).re ≤ 1 → (sqrtJ z).im ≤ C * Real.exp (-π * z.im)) ∧
      (-1 ≤ (z : ℂ).re → (z : ℂ).re ≤ 0 → -(sqrtJ z).im ≤ C * Real.exp (-π * z.im)))
    {z : ℂ} (him : 0 < z.im) (hre : 0 ≤ z.re) (hc : z.re ≤ Complex.normSq z)
    (hsmall : ‖z‖ ≤ 1 / 2) (hV : V ≤ 1 / (2 * ‖z‖)) :
    (sqrtJC z).im ≤ C * Real.exp (-π * (1 / (2 * ‖z‖))) := by
  obtain ⟨⟨hre1, hre2⟩, himw⟩ := horn_zero_bounds him hre hc hsmall
  have hwpos : 0 < (-1 / z).im := lt_of_lt_of_le (by
    have : z ≠ 0 := fun h => by simp [h] at him
    positivity) himw
  let w : ℍ := ⟨-1 / z, hwpos⟩
  have hz : ofComplex z = ModularGroup.S • w := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos him, coe_S_smul]
    have : z ≠ 0 := fun h => by simp [h] at him
    simp only [w]
    field_simp
  rw [sqrtJC, hz, sqrtJ_S, Complex.neg_im]
  have h := (hb w (hV.trans himw)).2 hre1 hre2
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have : (1 / (2 * ‖z‖)) ≤ w.im := himw
  nlinarith [Real.pi_pos]

theorem sqrtJC_cusp_one {C V : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : ℍ, V ≤ z.im →
      (0 ≤ (z : ℂ).re → (z : ℂ).re ≤ 1 → (sqrtJ z).im ≤ C * Real.exp (-π * z.im)) ∧
      (-1 ≤ (z : ℂ).re → (z : ℂ).re ≤ 0 → -(sqrtJ z).im ≤ C * Real.exp (-π * z.im)))
    {z : ℂ} (him : 0 < z.im) (hre : z.re ≤ 1) (hc : 1 / 2 ≤ ‖z - 1 / 2‖)
    (hsmall : ‖z - 1‖ ≤ 1 / 2) (hV : V ≤ 1 / (2 * ‖z - 1‖)) :
    (sqrtJC z).im ≤ C * Real.exp (-π * (1 / (2 * ‖z - 1‖))) := by
  set u := z - 1 with hu
  have huim : 0 < u.im := by simpa [hu] using him
  have hure : u.re ≤ 0 := by simp [hu]; linarith
  have huc : -u.re ≤ Complex.normSq u := by
    have h2 : (1 / 2 : ℝ) ^ 2 ≤ Complex.normSq (z - 1 / 2) := by
      rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (by norm_num) hc 2
    have e : Complex.normSq (z - 1 / 2) = Complex.normSq u + u.re + 1 / 4 := by
      rw [hu, Complex.normSq_apply, Complex.normSq_apply]; simp; ring
    linarith
  obtain ⟨⟨hre1, hre2⟩, himw⟩ := horn_one_bounds huim hure huc hsmall
  have hwpos : 0 < (-1 / u).im := lt_of_lt_of_le (by
    have : u ≠ 0 := fun h => by simp [h] at huim
    positivity) himw
  let w : ℍ := ⟨-1 / u, hwpos⟩
  have hz : ofComplex z = ModularGroup.T • ModularGroup.S • w := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos him, coe_T_smul, coe_S_smul]
    have : u ≠ 0 := fun h => by simp [h] at huim
    simp only [w]
    field_simp
    rw [hu]; ring
  rw [sqrtJC, hz, sqrtJ_T, sqrtJ_S, neg_neg]
  have h := (hb w (hV.trans himw)).1 hre1 hre2
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have : (1 / (2 * ‖u‖)) ≤ w.im := himw
  nlinarith [Real.pi_pos]

/-! ## Maximum principle: `Im s < 0` on the triangle -/

/-- The triangle with its three cusps cut off. -/
def triangleCut (V : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 / 2 < ‖z - 1 / 2‖ ∧ z.im < V ∧
    1 / (2 * V) < ‖z‖ ∧ 1 / (2 * V) < ‖z - 1‖}

theorem isOpen_triangleCut (V : ℝ) : IsOpen (triangleCut V) := by
  have c1 := Complex.continuous_im
  have c2 := Complex.continuous_re
  have c3 : Continuous fun z : ℂ => ‖z - 1 / 2‖ := (continuous_id.sub continuous_const).norm
  have c4 : Continuous fun z : ℂ => ‖z‖ := continuous_norm
  have c5 : Continuous fun z : ℂ => ‖z - 1‖ := (continuous_id.sub continuous_const).norm
  exact (isOpen_lt continuous_const c1).inter ((isOpen_lt continuous_const c2).inter
    ((isOpen_lt c2 continuous_const).inter ((isOpen_lt continuous_const c3).inter
      ((isOpen_lt c1 continuous_const).inter ((isOpen_lt continuous_const c4).inter
        (isOpen_lt continuous_const c5))))))

/-- The closed version, which does not touch the real axis. -/
def triangleCutCl (V : ℝ) : Set ℂ :=
  {z | 0 ≤ z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 / 2 ≤ ‖z - 1 / 2‖ ∧ z.im ≤ V ∧
    1 / (2 * V) ≤ ‖z‖ ∧ 1 / (2 * V) ≤ ‖z - 1‖}

theorem closure_triangleCut_subset (V : ℝ) : closure (triangleCut V) ⊆ triangleCutCl V := by
  apply closure_minimal
  · intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.1.le, hz.2.2.2.2.1.le, hz.2.2.2.2.2.1.le,
      hz.2.2.2.2.2.2.le⟩
  · have c1 := Complex.continuous_im
    have c2 := Complex.continuous_re
    have c3 : Continuous fun z : ℂ => ‖z - 1 / 2‖ := (continuous_id.sub continuous_const).norm
    have c4 : Continuous fun z : ℂ => ‖z‖ := continuous_norm
    have c5 : Continuous fun z : ℂ => ‖z - 1‖ := (continuous_id.sub continuous_const).norm
    exact (isClosed_le continuous_const c1).inter ((isClosed_le continuous_const c2).inter
      ((isClosed_le c2 continuous_const).inter ((isClosed_le continuous_const c3).inter
        ((isClosed_le c1 continuous_const).inter ((isClosed_le continuous_const c4).inter
          (isClosed_le continuous_const c5))))))

theorem im_pos_of_mem_triangleCutCl {V : ℝ} (hV : 0 < V) {z : ℂ} (hz : z ∈ triangleCutCl V) :
    0 < z.im := by
  rcases hz with ⟨him, hre0, hre1, hc, -, h0, h1⟩
  rcases lt_or_eq_of_le him with h | h
  · exact h
  exfalso
  have hpos : 0 < 1 / (2 * V) := by positivity
  have e1 : ‖z - 1 / 2‖ ^ 2 = (z.re - 1 / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [← h]; ring
  have e2 : ‖z‖ ^ 2 = z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [← h]; ring
  have e3 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [← h]; ring
  have hc2 : (1 / 2 : ℝ) ^ 2 ≤ ‖z - 1 / 2‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hc 2
  have hprod : z.re * (z.re - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h' | h'
  · have : ‖z‖ ^ 2 = 0 := by rw [e2, h']; ring
    have : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    linarith
  · have : ‖z - 1‖ ^ 2 = 0 := by rw [e3, h']; ring
    have : ‖z - 1‖ = 0 := by nlinarith [norm_nonneg (z - 1)]
    linarith

theorem sqrtJC_im_eq_zero_of_side {z : ℂ} (him : 0 < z.im)
    (h : z.re = 0 ∨ z.re = 1 ∨ ‖z - 1 / 2‖ = 1 / 2) : (sqrtJC z).im = 0 := by
  rw [sqrtJC_apply him]
  apply sqrtJ_im_eq_zero
  rcases h with h | h | h
  · exact j_real_of_re_eq_zero ⟨z, him⟩ h
  · exact j_real_of_re_eq_one ⟨z, him⟩ h
  · exact j_real_of_semicircle ⟨z, him⟩ h

theorem isOpen_idealTriangle : IsOpen idealTriangle := isOpen_idealTriangleAbove 0

/-- `Im s ≤ 0` on the ideal triangle `(0, 1, ∞)`. -/
theorem sqrtJC_im_nonpos {z₀ : ℂ} (hz₀ : z₀ ∈ idealTriangle) : (sqrtJC z₀).im ≤ 0 := by
  by_contra hδ
  rw [not_le] at hδ
  set δ := (sqrtJC z₀).im with hδdef
  obtain ⟨C, V₀, hC, hb⟩ := exists_bound_im_sqrtJ
  have hz0 : 0 < ‖z₀‖ := norm_pos_iff.mpr fun h => by simp [h, idealTriangle] at hz₀
  have hz1 : 0 < ‖z₀ - 1‖ := norm_pos_iff.mpr fun h => by
    have : z₀ = 1 := sub_eq_zero.mp h
    simp [this, idealTriangle] at hz₀
  have hev : ∀ᶠ V : ℝ in atTop, V₀ ≤ V ∧ 1 ≤ V ∧ z₀.im < V ∧ 1 / (2 * V) < ‖z₀‖ ∧
      1 / (2 * V) < ‖z₀ - 1‖ ∧ C * Real.exp (-π * V) < δ := by
    have hinv : Tendsto (fun V : ℝ => 1 / (2 * V)) atTop (𝓝 0) := by
      have h := (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).inv_tendsto_atTop
      refine h.congr fun V => ?_
      simp [one_div]
    have hexp : Tendsto (fun V : ℝ => C * Real.exp (-π * V)) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -π < 0)))
      simpa using h.const_mul C
    filter_upwards [eventually_ge_atTop V₀, eventually_ge_atTop 1, eventually_gt_atTop z₀.im,
      hinv.eventually (gt_mem_nhds hz0), hinv.eventually (gt_mem_nhds hz1),
      hexp.eventually (gt_mem_nhds hδ)] with V h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨V, hV₀, hV1, hVim, hV0, hV1', hVδ⟩ := hev.exists
  have hVpos : 0 < V := by linarith
  set F : ℂ → ℂ := fun z => cexp (-I * sqrtJC z) with hF
  have hFn : ∀ z, ‖F z‖ = Real.exp (sqrtJC z).im := fun z => by
    simp [hF, Complex.norm_exp]
  have hbdd : IsBounded (triangleCut V) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := V + 1)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz.2.1, abs_of_pos hz.1] at this
    linarith [hz.2.2.1, hz.2.2.2.2.1]
  have hdiff : DiffContOnCl ℂ F (triangleCut V) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have him := im_pos_of_mem_triangleCutCl hVpos (closure_triangleCut_subset V hz)
    exact ((differentiableAt_sqrtJC him).const_mul (-I)).cexp.differentiableWithinAt
  have hfront : ∀ z ∈ frontier (triangleCut V), ‖F z‖ ≤ Real.exp (C * Real.exp (-π * V)) := by
    intro z hz
    rw [hFn, Real.exp_le_exp]
    have hzcl : z ∈ triangleCutCl V := closure_triangleCut_subset V (frontier_subset_closure hz)
    have hnot : z ∉ triangleCut V := ((isOpen_triangleCut V).frontier_eq ▸ hz).2
    have him := im_pos_of_mem_triangleCutCl hVpos hzcl
    rcases hzcl with ⟨-, hre0, hre1, hc, hVle, hn0, hn1⟩
    have hCe : 0 ≤ C * Real.exp (-π * V) := by positivity
    by_cases hside : z.re = 0 ∨ z.re = 1 ∨ ‖z - 1 / 2‖ = 1 / 2
    · rw [sqrtJC_im_eq_zero_of_side him hside]; exact hCe
    simp only [not_or] at hside
    obtain ⟨hs0, hs1, hs2⟩ := hside
    by_cases htop : z.im = V
    · rw [← htop]
      exact sqrtJC_top hb him (htop ▸ hV₀) hre0 hre1
    by_cases hcz : ‖z‖ = 1 / (2 * V)
    · have hsm : ‖z‖ ≤ 1 / 2 := by
        rw [hcz, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hcz' : 1 / (2 * ‖z‖) = V := by rw [hcz]; field_simp
      have hcr : z.re ≤ Complex.normSq z := by
        have h2 : (1 / 2 : ℝ) ^ 2 ≤ Complex.normSq (z - 1 / 2) := by
          rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (by norm_num) hc 2
        have e : Complex.normSq (z - 1 / 2) = Complex.normSq z - z.re + 1 / 4 := by
          rw [Complex.normSq_apply, Complex.normSq_apply]; simp; ring
        linarith
      have h := sqrtJC_cusp_zero hC hb him hre0 hcr hsm (by rw [hcz']; exact hV₀)
      rwa [hcz'] at h
    by_cases hc1 : ‖z - 1‖ = 1 / (2 * V)
    · have hsm : ‖z - 1‖ ≤ 1 / 2 := by
        rw [hc1, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hc1' : 1 / (2 * ‖z - 1‖) = V := by rw [hc1]; field_simp
      have h := sqrtJC_cusp_one hC hb him hre1 hc hsm (by rw [hc1']; exact hV₀)
      rwa [hc1'] at h
    exfalso
    exact hnot ⟨him, lt_of_le_of_ne hre0 (Ne.symm hs0), lt_of_le_of_ne hre1 hs1,
      lt_of_le_of_ne hc (Ne.symm hs2), lt_of_le_of_ne hVle htop, lt_of_le_of_ne hn0 (Ne.symm hcz),
      lt_of_le_of_ne hn1 (Ne.symm hc1)⟩
  have hz₀U : z₀ ∈ triangleCut V :=
    ⟨hz₀.1, hz₀.2.1, hz₀.2.2.1, hz₀.2.2.2, hVim, hV0, hV1'⟩
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdiff hfront
    (subset_closure hz₀U)
  rw [hFn, Real.exp_le_exp] at h
  linarith

/-- `Im s < 0` on the ideal triangle `(0, 1, ∞)`. -/
theorem sqrtJC_im_neg {z₀ : ℂ} (hz₀ : z₀ ∈ idealTriangle) : (sqrtJC z₀).im < 0 := by
  rcases lt_or_eq_of_le (sqrtJC_im_nonpos hz₀) with h | h
  · exact h
  exfalso
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have hana : AnalyticOnNhd ℂ sqrtJC {z : ℂ | 0 < z.im} :=
    differentiableOn_sqrtJC.analyticOnNhd hU
  rcases (hana z₀ hz₀.1).eventually_constant_or_nhds_le_map_nhds with hc | hopen
  · have heq := hana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_halfSpace_im_gt 0).isPreconnected hz₀.1 hc
    have h2 : sqrtJC (I * (2 : ℝ)) = sqrtJC z₀ := heq (by simp)
    have h3 : sqrtJC (I * (3 : ℝ)) = sqrtJC z₀ := heq (by simp)
    have hsq : kleinModularJ (imagPt 2) = kleinModularJ (imagPt 3) := by
      have e2 := sqrtJ_sq (imagPt 2)
      have e3 := sqrtJ_sq (imagPt 3)
      have : sqrtJ (imagPt 2) = sqrtJ (imagPt 3) := by
        rw [show sqrtJ (imagPt 2) = sqrtJC (I * (2 : ℝ)) from rfl,
          show sqrtJ (imagPt 3) = sqrtJC (I * (3 : ℝ)) from rfl, h2, h3]
      linear_combination e3 - e2 + (sqrtJ (imagPt 2) + sqrtJ (imagPt 3)) * this
    have := kleinModularJ_imagPt_eq (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3) hsq
    norm_num at this
  · have hA : {w : ℂ | w.im ≤ 0} ∈ 𝓝 (sqrtJC z₀) := by
      apply hopen
      rw [Filter.mem_map]
      filter_upwards [isOpen_idealTriangle.mem_nhds hz₀] with z hz
      exact sqrtJC_im_nonpos hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hA
    have hp : sqrtJC z₀ + I * ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (sqrtJC z₀) r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have := hball hp
    change (sqrtJC z₀ + I * ((r / 2 : ℝ) : ℂ)).im ≤ 0 at this
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at this
    rw [h] at this
    linarith

/-! ## Consequences for the CKMRV denominators -/

/-- Inside the ideal triangle `(0, 1, ∞)`, `j` is not a real number `≥ 1728`. -/
theorem kleinModularJ_not_real_of_mem_idealTriangle {z : ℂ} (hz : z ∈ idealTriangle) :
    ¬((kleinModularJ (ofComplex z)).im = 0 ∧ 1728 ≤ (kleinModularJ (ofComplex z)).re) :=
  fun h => (sqrtJC_im_neg hz).ne (sqrtJ_im_eq_zero _ h)

/-- The same inside the ideal triangle `(−1, 0, ∞)`. -/
theorem kleinModularJ_not_real_of_add_one_mem {z : ℂ} (hz : z + 1 ∈ idealTriangle) :
    ¬((kleinModularJ (ofComplex z)).im = 0 ∧ 1728 ≤ (kleinModularJ (ofComplex z)).re) := by
  have him : 0 < z.im := by simpa using hz.1
  have h : ofComplex (z + 1) = ModularGroup.T • ofComplex z := by
    apply UpperHalfPlane.ext
    rw [coe_T_smul, ofComplex_apply_of_im_pos him, ofComplex_apply_of_im_pos hz.1]
  have := kleinModularJ_not_real_of_mem_idealTriangle hz
  rwa [h, kleinModularJ_T] at this

/-- For `τ` on the imaginary axis, `j(z) ≠ j(τ)` inside both triangles `(0, 1, ∞)` and
`(−1, 0, ∞)`: the CKMRV kernels have no poles there. -/
theorem kleinModularJ_ne_imagPt_of_triangle {z : ℂ}
    (hz : z ∈ idealTriangle ∨ z + 1 ∈ idealTriangle) {t : ℝ} (ht : 0 < t) :
    kleinModularJ (ofComplex z) ≠ kleinModularJ (imagPt t) := by
  rcases hz with hz | hz
  · exact kleinModularJ_ne_imagPt_of_not_real (kleinModularJ_not_real_of_mem_idealTriangle hz) t ht
  · exact kleinModularJ_ne_imagPt_of_not_real (kleinModularJ_not_real_of_add_one_mem hz) t ht

end E8Leech
