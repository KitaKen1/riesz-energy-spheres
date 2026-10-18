import E8Leech.CKMRVGrowth

/-!
# Second-order cusp expansions in `s = e^{πiτ}`

`HasExp3 f a b c` says `f = a + b s + c s² + O(|s|³)` as `Im τ → ∞`, with `s = e^{πiτ}`.
The predicate is closed under sums, products, inverses (nonzero constant term) and logarithms
(`exp g = f`, `g → 0`), and the coefficients of the results are explicit polynomials in the
input coefficients. Starting from the theta series, this computes the expansions of `U, V, W`,
`E₄`, `E₆`, `Δ`, `L - πiτ - 4 log 2` and `L_S` to second order; the coefficient identities are
checked by `norm_num`. The numbers agree with the exact truncated `q`-series computation in
`research/check-ckmrv-growth-421-20261010.py`.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The cusp parameter `s = e^{πiτ}` -/

/-- The cusp parameter `s = e^{πiτ}` of period two. -/
def cuspS (τ : ℍ) : ℂ := cexp (π * I * τ)

theorem norm_cuspS (τ : ℍ) : ‖cuspS τ‖ = Real.exp (-π * τ.im) := by
  rw [cuspS, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_cuspS_lt_one (τ : ℍ) : ‖cuspS τ‖ < 1 := by
  rw [norm_cuspS, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, τ.im_pos])

theorem norm_cuspS_le_one (τ : ℍ) : ‖cuspS τ‖ ≤ 1 := (norm_cuspS_lt_one τ).le

theorem tendsto_norm_cuspS : Tendsto (fun τ : ℍ => ‖cuspS τ‖) atImInfty (𝓝 0) := by
  have h1 : Tendsto (fun τ : ℍ => π * τ.im) atImInfty atTop :=
    tendsto_upperHalfPlaneIm_atImInfty.const_mul_atTop Real.pi_pos
  have h2 : Tendsto (fun τ : ℍ => -π * τ.im) atImInfty atBot := by
    refine (tendsto_neg_atTop_atBot.comp h1).congr fun τ => ?_
    simp only [Function.comp_apply]
    ring
  refine (Real.tendsto_exp_atBot.comp h2).congr fun τ => ?_
  simp only [Function.comp_apply, norm_cuspS]

theorem tendsto_cuspS : Tendsto cuspS atImInfty (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr tendsto_norm_cuspS

theorem eventually_norm_cuspS_le_half : ∀ᶠ τ : ℍ in atImInfty, ‖cuspS τ‖ ≤ 1 / 2 :=
  tendsto_norm_cuspS.eventually (ge_mem_nhds (by norm_num))

theorem cuspS_ne_zero (τ : ℍ) : cuspS τ ≠ 0 := Complex.exp_ne_zero _

/-- `e^{-2π Im τ} = |s|²`. -/
theorem exp_neg_two_pi_eq_norm_cuspS_sq (τ : ℍ) :
    Real.exp (-2 * π * τ.im) = ‖cuspS τ‖ ^ 2 := by
  rw [norm_cuspS, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exp_two_pi_eq_norm_cuspS_sq_inv (τ : ℍ) :
    Real.exp (2 * π * τ.im) = (‖cuspS τ‖ ^ 2)⁻¹ := by
  rw [← exp_neg_two_pi_eq_norm_cuspS_sq, ← Real.exp_neg]
  congr 1
  ring

/-! ## The predicate -/

/-- `f = a + b s + c s² + O(|s|³)` at `i∞`, with `s = e^{πiτ}`. -/
def HasExp3 (f : ℍ → ℂ) (a b c : ℂ) : Prop :=
  (fun τ : ℍ => f τ - (a + b * cuspS τ + c * cuspS τ ^ 2)) =O[atImInfty]
    fun τ : ℍ => ‖cuspS τ‖ ^ 3

/-- Quadratic polynomials in `s` are bounded. -/
theorem isBigO_quad_one (a b c : ℂ) :
    (fun τ : ℍ => a + b * cuspS τ + c * cuspS τ ^ 2) =O[atImInfty] fun _ : ℍ => (1 : ℝ) := by
  refine IsBigO.of_bound (‖a‖ + ‖b‖ + ‖c‖) (Eventually.of_forall fun τ => ?_)
  have hs := norm_cuspS_le_one τ
  have hs2 : ‖cuspS τ‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hs
  calc ‖a + b * cuspS τ + c * cuspS τ ^ 2‖
      ≤ ‖a‖ + ‖b‖ * ‖cuspS τ‖ + ‖c‖ * ‖cuspS τ‖ ^ 2 := by
        refine (norm_add₃_le).trans ?_
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ ‖a‖ + ‖b‖ * 1 + ‖c‖ * 1 := by gcongr
    _ = (‖a‖ + ‖b‖ + ‖c‖) * ‖(1 : ℝ)‖ := by simp

theorem isBigO_cube_one :
    (fun τ : ℍ => ‖cuspS τ‖ ^ 3) =O[atImInfty] fun _ : ℍ => (1 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one, one_mul]
  exact pow_le_one₀ (norm_nonneg _) (norm_cuspS_le_one τ)

/-- `s^k = O(|s|³)` for `k ≥ 3`. -/
theorem isBigO_cuspS_pow {k : ℕ} (hk : 3 ≤ k) :
    (fun τ : ℍ => cuspS τ ^ k) =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 3 := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) (norm_cuspS_le_one τ) hk

namespace HasExp3

variable {f g : ℍ → ℂ} {a b c a' b' c' : ℂ}

theorem congr_fun (hf : HasExp3 f a b c) (h : ∀ τ, f τ = g τ) : HasExp3 g a b c :=
  IsBigO.congr_left hf fun τ => by rw [h]

theorem congr_coeff (hf : HasExp3 f a b c) (ha : a = a') (hb : b = b') (hc : c = c') :
    HasExp3 f a' b' c' := by
  subst ha hb hc
  exact hf

theorem isBigO_one (hf : HasExp3 f a b c) : f =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
  ((IsBigO.trans hf isBigO_cube_one).add (isBigO_quad_one a b c)).congr_left fun τ => by ring

theorem const (a : ℂ) : HasExp3 (fun _ => a) a 0 0 :=
  (isBigO_zero _ _).congr_left fun τ => by ring

theorem cuspS' : HasExp3 cuspS 0 1 0 :=
  (isBigO_zero _ _).congr_left fun τ => by ring

theorem add (hf : HasExp3 f a b c) (hg : HasExp3 g a' b' c') :
    HasExp3 (fun τ => f τ + g τ) (a + a') (b + b') (c + c') :=
  (IsBigO.add hf hg).congr_left fun τ => by ring

theorem neg (hf : HasExp3 f a b c) : HasExp3 (fun τ => -f τ) (-a) (-b) (-c) :=
  (IsBigO.neg_left hf).congr_left fun τ => by ring

theorem sub (hf : HasExp3 f a b c) (hg : HasExp3 g a' b' c') :
    HasExp3 (fun τ => f τ - g τ) (a - a') (b - b') (c - c') :=
  (IsBigO.sub hf hg).congr_left fun τ => by ring

theorem const_mul (k : ℂ) (hf : HasExp3 f a b c) :
    HasExp3 (fun τ => k * f τ) (k * a) (k * b) (k * c) :=
  (IsBigO.const_mul_left hf k).congr_left fun τ => by ring

theorem add_isBigO (hf : HasExp3 f a b c) {r : ℍ → ℂ}
    (hr : r =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 3) :
    HasExp3 (fun τ => f τ + r τ) a b c :=
  (IsBigO.add hf hr).congr_left fun τ => by ring

theorem mul (hf : HasExp3 f a b c) (hg : HasExp3 g a' b' c') :
    HasExp3 (fun τ => f τ * g τ) (a * a') (a * b' + b * a') (a * c' + b * b' + c * a') := by
  have h1 := (IsBigO.mul hf (isBigO_one hg)).congr_right fun τ => mul_one _
  have h2 := (IsBigO.mul (isBigO_quad_one a b c) hg).congr_right fun τ => one_mul _
  have h3 : (fun τ : ℍ => (b * c' + c * b') * cuspS τ ^ 3 + c * c' * cuspS τ ^ 4)
      =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 3 :=
    ((isBigO_cuspS_pow le_rfl).const_mul_left _).add
      ((isBigO_cuspS_pow (by norm_num)).const_mul_left _)
  exact ((h1.add h2).add h3).congr_left fun τ => by ring

theorem pow (hf : HasExp3 f a b c) :
    HasExp3 (fun τ => f τ ^ 2) (a ^ 2) (2 * a * b) (2 * a * c + b ^ 2) :=
  (hf.mul hf).congr_fun (fun τ => by ring) |>.congr_coeff (by ring) (by ring) (by ring)

theorem tendsto (hf : HasExp3 f a b c) : Tendsto f atImInfty (𝓝 a) := by
  have hr : Tendsto (fun τ : ℍ => f τ - (a + b * cuspS τ + c * cuspS τ ^ 2)) atImInfty (𝓝 0) :=
    IsBigO.trans_tendsto hf (by simpa using tendsto_norm_cuspS.pow 3)
  have hp : Tendsto (fun τ : ℍ => a + b * cuspS τ + c * cuspS τ ^ 2) atImInfty (𝓝 a) := by
    simpa using ((tendsto_const_nhds (x := a)).add (tendsto_cuspS.const_mul b)).add
      ((tendsto_cuspS.pow 2).const_mul c)
  simpa using hr.add hp

/-- If all three coefficients vanish, `f = O(|s|³)`. -/
theorem isBigO_cube (hf : HasExp3 f 0 0 0) : f =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 3 :=
  IsBigO.congr_left hf fun τ => by ring

/-- If the first two coefficients vanish, `f = O(|s|²)`. -/
theorem isBigO_sq (hf : HasExp3 f 0 0 c) : f =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 2 := by
  have h3 : (fun τ : ℍ => ‖cuspS τ‖ ^ 3) =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 2 := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) (norm_cuspS_le_one τ) (by norm_num)
  have h2 : (fun τ : ℍ => c * cuspS τ ^ 2) =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 2 :=
    IsBigO.of_bound ‖c‖ (Eventually.of_forall fun τ => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
  exact ((IsBigO.trans hf h3).add h2).congr_left fun τ => by ring

theorem inv (hf : HasExp3 f a b c) (ha : a ≠ 0) :
    HasExp3 (fun τ => (f τ)⁻¹) a⁻¹ (-b / a ^ 2) ((b ^ 2 - a * c) / a ^ 3) := by
  set R : ℍ → ℂ := fun τ => a⁻¹ + -b / a ^ 2 * cuspS τ + (b ^ 2 - a * c) / a ^ 3 * cuspS τ ^ 2
  have hR : HasExp3 R a⁻¹ (-b / a ^ 2) ((b ^ 2 - a * c) / a ^ 3) :=
    (isBigO_zero _ _).congr_left fun τ => by simp only [R]; ring
  -- `f R = 1 + O(|s|³)`
  have hfR : HasExp3 (fun τ => f τ * R τ) 1 0 0 := by
    refine (hf.mul hR).congr_coeff ?_ ?_ ?_
    · field_simp
    · field_simp; ring
    · field_simp; ring
  have hne : ∀ᶠ τ : ℍ in atImInfty, f τ ≠ 0 := hf.tendsto.eventually_ne ha
  have hinv : (fun τ : ℍ => (f τ)⁻¹) =O[atImInfty] fun _ : ℍ => (1 : ℝ) :=
    (hf.tendsto.inv₀ ha).isBigO_one ℝ
  -- `f⁻¹ - R = -f⁻¹ (f R - 1)`
  have h := ((hinv.mul hfR).congr_right fun τ => one_mul _).neg_left
  refine h.congr' ?_ (Eventually.of_forall fun τ => rfl)
  filter_upwards [hne] with τ hτ
  simp only [R]
  field_simp
  ring

/-- Logarithms: if `exp g = f`, `g → 0` and `f = 1 + b s + c s² + O(|s|³)`, then
`g = b s + (c - b²/2) s² + O(|s|³)`. -/
theorem log_of_exp (hf : HasExp3 f 1 b c) (hexp : ∀ τ, cexp (g τ) = f τ)
    (hg : Tendsto g atImInfty (𝓝 0)) : HasExp3 g 0 b (c - b ^ 2 / 2) := by
  set x : ℍ → ℂ := fun τ => f τ - 1
  have hx : HasExp3 x 0 b c := (hf.sub (const 1)).congr_coeff (by ring) (by ring) (by ring)
  -- `x - x²/2` has the claimed expansion
  have hq : HasExp3 (fun τ => x τ - (1 / 2 : ℂ) * x τ ^ 2) 0 b (c - b ^ 2 / 2) :=
    (hx.sub ((hx.pow).const_mul (1 / 2 : ℂ))).congr_coeff (by ring) (by ring) (by ring)
  -- eventually `g = log f` and `|x| ≤ 1/2`
  have hxs : x =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ := by
    have h1 : (fun τ : ℍ => b * cuspS τ + c * cuspS τ ^ 2) =O[atImInfty]
        fun τ : ℍ => ‖cuspS τ‖ :=
      IsBigO.of_bound (‖b‖ + ‖c‖) (Eventually.of_forall fun τ => by
        have hs := norm_cuspS_le_one τ
        calc ‖b * cuspS τ + c * cuspS τ ^ 2‖ ≤ ‖b‖ * ‖cuspS τ‖ + ‖c‖ * ‖cuspS τ‖ ^ 2 := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_mul, norm_mul, norm_pow]
          _ ≤ ‖b‖ * ‖cuspS τ‖ + ‖c‖ * ‖cuspS τ‖ := by
              gcongr
              nlinarith [norm_nonneg (cuspS τ)]
          _ = (‖b‖ + ‖c‖) * ‖‖cuspS τ‖‖ := by rw [norm_norm]; ring)
    have h3 : (fun τ : ℍ => ‖cuspS τ‖ ^ 3) =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ :=
      IsBigO.of_bound 1 (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          abs_of_nonneg (norm_nonneg _), one_mul]
        exact pow_le_of_le_one (norm_nonneg _) (norm_cuspS_le_one τ) (by norm_num))
    exact ((IsBigO.trans hx h3).add h1).congr_left fun τ => by ring
  have hx0 : Tendsto x atImInfty (𝓝 0) := hxs.trans_tendsto tendsto_norm_cuspS
  have hsmall : ∀ᶠ τ : ℍ in atImInfty, ‖x τ‖ ≤ 1 / 2 :=
    (tendsto_norm_zero.comp hx0).eventually (ge_mem_nhds (by norm_num))
  have hlog : ∀ᶠ τ : ℍ in atImInfty, g τ = Complex.log (1 + x τ) := by
    have him : ∀ᶠ τ : ℍ in atImInfty, ‖g τ‖ < 1 :=
      (tendsto_norm_zero.comp hg).eventually (gt_mem_nhds (by norm_num))
    filter_upwards [him] with τ hτ
    have hre : |(g τ).im| < 1 := (abs_im_le_norm _).trans_lt hτ
    have h1 : -π < (g τ).im := by
      have := Real.pi_gt_three
      linarith [(abs_lt.mp hre).1]
    have h2 : (g τ).im ≤ π := by
      have := Real.pi_gt_three
      linarith [(abs_lt.mp hre).2]
    rw [show 1 + x τ = f τ by simp [x], ← hexp τ, Complex.log_exp h1 h2]
  -- `|log (1 + x) - (x - x²/2)| ≤ |x|³`
  have hrem : (fun τ : ℍ => g τ - (x τ - (1 / 2 : ℂ) * x τ ^ 2)) =O[atImInfty]
      fun τ : ℍ => ‖cuspS τ‖ ^ 3 := by
    have hx3 : (fun τ : ℍ => ‖x τ‖ ^ 3) =O[atImInfty] fun τ : ℍ => ‖cuspS τ‖ ^ 3 := by
      have := hxs.norm_left.pow 3
      simpa using this
    refine IsBigO.trans ?_ hx3
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hlog, hsmall] with τ hτ hsm
    rw [hτ]
    have hlt : ‖x τ‖ < 1 := by linarith
    have key := Complex.norm_log_sub_logTaylor_le 2 hlt
    have hT : Complex.logTaylor (2 + 1) (x τ) = x τ - 1 / 2 * x τ ^ 2 := by
      simp [Complex.logTaylor, Finset.sum_range_succ]
      ring
    rw [hT] at key
    have hden : (1 - ‖x τ‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖Complex.log (1 + x τ) - (x τ - 1 / 2 * x τ ^ 2)‖
        ≤ ‖x τ‖ ^ (2 + 1) * (1 - ‖x τ‖)⁻¹ / (2 + 1) := key
      _ ≤ ‖x τ‖ ^ 3 * 2 / 3 := by
          gcongr
          · norm_num
      _ ≤ 1 * ‖‖x τ‖ ^ 3‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [pow_nonneg (norm_nonneg (x τ)) 3]
  exact (hq.add_isBigO hrem).congr_fun fun τ => by ring

end HasExp3

end E8Leech
