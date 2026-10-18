import E8Leech.CKMRVKernelInversion

/-!
# Convergence of the CKMRV Laplace integrals (P4d, first step)

CKMRV (5.1) defines `F(τ, r)` through `∫₀^∞ K(τ, it) e^{-π r² t} dt`. For fixed `τ` whose
`j`-value is not taken on the positive imaginary axis (so `t ↦ K(τ, it)` has no poles), this
integral converges absolutely for `r ≠ 0` in dimension eight and for `r² > 2` in dimension
twenty-four.

* At `t → ∞`, CKMRV (4.38) gives `K(τ, it) = O(t)` for `d = 8` and `O(t e^{2π t})` for `d = 24`.
* At `t → 0`, `K(τ, it) = (K ∣ S)(τ, i/t) · (−t^{k})`, and the `z`-variable part of Lemma 4.11
  (`CKMRVKernelInversion`) bounds `K ∣ S` at `i∞`.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The positive imaginary axis -/

/-- The point `it` of the upper half-plane (a junk point for `t ≤ 0`). -/
def imagPt (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (I * t)

theorem coe_imagPt {t : ℝ} (ht : 0 < t) : ((imagPt t : ℍ) : ℂ) = I * t := by
  rw [imagPt, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]

theorem im_imagPt {t : ℝ} (ht : 0 < t) : (imagPt t).im = t := by
  show ((imagPt t : ℍ) : ℂ).im = t
  rw [coe_imagPt ht]
  simp

theorem norm_coe_imagPt {t : ℝ} (ht : 0 < t) : ‖((imagPt t : ℍ) : ℂ)‖ = t := by
  rw [coe_imagPt ht, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg ht.le]

theorem S_smul_imagPt_inv {t : ℝ} (ht : 0 < t) : ModularGroup.S • imagPt t⁻¹ = imagPt t := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hne : I * ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by
    push_cast
    exact mul_ne_zero I_ne_zero (inv_ne_zero ht')
  apply UpperHalfPlane.ext
  rw [coe_S_smul, coe_imagPt (inv_pos.mpr ht), coe_imagPt ht, div_eq_iff hne]
  push_cast
  linear_combination (-((t : ℂ) * (t : ℂ)⁻¹)) * Complex.I_sq + mul_inv_cancel₀ ht'

theorem coe_imagPt_inv_sq {t : ℝ} (ht : 0 < t) :
    ((imagPt t⁻¹ : ℍ) : ℂ) ^ 2 * (-(t : ℂ) ^ 2) = 1 := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [coe_imagPt (inv_pos.mpr ht)]
  push_cast
  linear_combination (-((t : ℂ)⁻¹ ^ 2 * (t : ℂ) ^ 2)) * Complex.I_sq +
    (mul_inv_cancel₀ ht' : (t : ℂ) * (t : ℂ)⁻¹ = 1) * ((t : ℂ) * (t : ℂ)⁻¹ + 1)

theorem coe_imagPt_inv_pow_ten {t : ℝ} (ht : 0 < t) :
    ((imagPt t⁻¹ : ℍ) : ℂ) ^ 10 * (-(t : ℂ) ^ 10) = 1 := by
  have h := coe_imagPt_inv_sq ht
  have h5 : (((imagPt t⁻¹ : ℍ) : ℂ) ^ 2 * (-(t : ℂ) ^ 2)) ^ 5 = 1 := by rw [h, one_pow]
  linear_combination h5

theorem tendsto_imagPt_atTop : Tendsto imagPt atTop atImInfty := by
  rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [im_imagPt ht]

theorem tendsto_imagPt_inv : Tendsto (fun t : ℝ => imagPt t⁻¹) (𝓝[>] 0) atImInfty := by
  rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
  refine tendsto_inv_nhdsGT_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [im_imagPt (inv_pos.mpr (show (0 : ℝ) < t from ht))]

theorem continuousOn_comp_imagPt {F : ℍ → ℂ} (hF : Continuous F) :
    ContinuousOn (fun t => F (imagPt t)) (Ioi 0) :=
  hF.comp_continuousOn continuousOn_ofComplex_I_mul

/-! ## A Laplace integrability criterion -/

/-- If `f` is continuous on `(0, ∞)`, bounded near `0` and `O(t e^{a t})` at `∞`, then
`f(t) e^{-b t}` is integrable on `(0, ∞)` for every `b > a`. -/
theorem integrableOn_Ioi_mul_exp_of_isBigO {f : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Ioi 0)) (h0 : f =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hinf : f =O[atTop] fun t => t * Real.exp (a * t)) :
    IntegrableOn (fun t => f t * (Real.exp (-b * t) : ℂ)) (Ioi 0) := by
  set g : ℝ → ℂ := fun t => f t * (Real.exp (-b * t) : ℂ) with hg_def
  have hgc : ContinuousOn g (Ioi 0) :=
    hcont.mul (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · -- `g` is bounded on `(0, 1]`.
    obtain ⟨C, hC⟩ := h0.bound
    obtain ⟨u, hu, huS⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hC
    set δ : ℝ := min u 1 / 2 with hδdef
    have hδ : 0 < δ := by
      have : (0 : ℝ) < min u 1 := lt_min hu one_pos
      positivity
    have hδu : δ < u := by
      have : min u 1 ≤ u := min_le_left _ _
      have : (0 : ℝ) < min u 1 := lt_min hu one_pos
      rw [hδdef]
      linarith
    have hδ1 : δ ≤ 1 := by
      have : min u 1 ≤ 1 := min_le_right _ _
      rw [hδdef]
      linarith
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn
      (hgc.mono fun t ht => lt_of_lt_of_le hδ ht.1)
    refine ⟨(hgc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc,
      HasFiniteIntegral.restrict_of_bounded (max M (C * Real.exp |b|)) (by simp) ?_⟩
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    by_cases htδ : δ ≤ t
    · exact (hM t ⟨htδ, ht.2⟩).trans (le_max_left _ _)
    · replace htδ : t < δ := not_le.mp htδ
      have hft : ‖f t‖ ≤ C * ‖(1 : ℝ)‖ := huS ⟨ht.1, htδ.trans hδu⟩
      rw [norm_one, mul_one] at hft
      have hexp : Real.exp (-b * t) ≤ Real.exp |b| := by
        apply Real.exp_le_exp.mpr
        have h1 : -b * t ≤ |b| * t := by nlinarith [neg_abs_le b, ht.1]
        nlinarith [abs_nonneg b, ht.2]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans hft
      calc ‖g t‖ = ‖f t‖ * Real.exp (-b * t) := by
            simp only [hg_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
        _ ≤ C * Real.exp |b| := mul_le_mul hft hexp (Real.exp_pos _).le hC0
        _ ≤ max M (C * Real.exp |b|) := le_max_right _ _
  · -- `‖g‖ = O(e^{-ε t})` at `∞` with `ε = (b - a)/2`.
    set ε : ℝ := (b - a) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    have hnorm : (fun t => ‖g t‖) =O[atTop] fun t => Real.exp (-ε * t) := by
      have he : (fun t : ℝ => (Real.exp (-b * t) : ℂ)) =O[atTop] fun t => Real.exp (-b * t) :=
        IsBigO.of_bound 1 (Eventually.of_forall fun t => by rw [Complex.norm_real, one_mul])
      have h1 : g =O[atTop] fun t => t * Real.exp (a * t) * Real.exp (-b * t) := hinf.mul he
      have h2 : (fun t : ℝ => t * Real.exp (a * t) * Real.exp (-b * t)) =O[atTop]
          fun t => Real.exp (-ε * t) := by
        refine IsBigO.of_bound (1 / ε) ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        have hexp : t * Real.exp (a * t) * Real.exp (-b * t) =
            t * Real.exp (-ε * t) * Real.exp (-ε * t) := by
          rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2
          simp only [ε]
          ring
        have hlin : t ≤ Real.exp (ε * t) / ε := by
          rw [le_div_iff₀ hε]
          nlinarith [Real.add_one_le_exp (ε * t)]
        have hprod : t * Real.exp (-ε * t) ≤ 1 / ε := by
          calc t * Real.exp (-ε * t) ≤ Real.exp (ε * t) / ε * Real.exp (-ε * t) :=
                mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
            _ = 1 / ε := by
                rw [div_mul_eq_mul_div, ← Real.exp_add]
                simp
        rw [hexp, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le) (Real.exp_pos _).le),
          abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      exact (h1.trans h2).norm_left
    have hint := integrable_of_isBigO_exp_neg hε
      ((hgc.mono fun t (ht : 1 ≤ t) => lt_of_lt_of_le one_pos ht).norm) hnorm
    exact (integrable_norm_iff
      ((hgc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)).mp hint

/-! ## Dimension eight, minus kernel -/

theorem continuous_eightMinusDenZ (τ : ℍ) : Continuous fun z => eightMinusDenZ τ z :=
  ((mdifferentiable_modularDiscriminant.mul mdifferentiable_const).sub
    ((ModularFormClass.holo ModularForm.E₄).pow 3)).continuous

theorem eightMinusDenZ_ne_zero {τ z : ℍ} (h : kleinModularJ τ ≠ kleinModularJ z) :
    eightMinusDenZ τ z ≠ 0 := by
  have hΔ := ModularForm.discriminant_ne_zero z
  have hJ := kleinModularJ_mul_discriminant z
  have hD : eightMinusDenZ τ z =
      ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z) := by
    rw [eightMinusDenZ]
    linear_combination hJ
  rw [hD]
  exact mul_ne_zero hΔ (sub_ne_zero.mpr h)

theorem continuousOn_ckmrvEightMinusKernel_imagPt (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvEightMinusKernel τ (imagPt t)) (Ioi 0) := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hL := continuous_ckmrvL
  have hU := mdifferentiable_thetaU.continuous
  have hV := mdifferentiable_thetaV.continuous
  have hW := mdifferentiable_thetaW.continuous
  have hN : Continuous fun z : ℍ =>
      eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z) +
        eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaW z) +
          eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2)) := by
    fun_prop
  have hD := (continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have h := (continuousOn_const (c := ckmrvMinusScale⁻¹)).mul hD |>.mul
    (continuousOn_comp_imagPt hN)
  refine h.congr fun t _ => ?_
  rw [ckmrvEightMinusKernel_eq_z]
  rfl

/-- Near `t = 0`: `K₋(τ, it) = (K₋ ∣ S)(τ, i/t) · (-t²)` is bounded. -/
theorem isBigO_ckmrvEightMinusKernel_imagPt_zero (τ : ℍ) :
    (fun t => ckmrvEightMinusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ : (fun t : ℝ => ckmrvEightMinusKernel τ (ModularGroup.S • imagPt t⁻¹) *
      ((imagPt t⁻¹ : ℍ) : ℂ) ^ 2) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((isBigO_ckmrvEightMinusKernel_S_right τ).comp_tendsto tendsto_imagPt_inv).trans
    (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      simp only [Function.comp_apply, Real.norm_eq_abs, one_mul, Real.abs_exp, abs_one]
      have hy : 0 < (imagPt t⁻¹).im := (imagPt t⁻¹).im_pos
      apply Real.exp_le_one_iff.mpr
      nlinarith [Real.pi_pos]))
  have ht2 : (fun t : ℝ => -(t : ℂ) ^ 2) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 2) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht2).congr_right fun _ => one_mul _).congr' ?_ (Eventually.of_forall fun _ =>
    rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [S_smul_imagPt_inv ht0, mul_assoc, coe_imagPt_inv_sq ht0, mul_one]

theorem isBigO_ckmrvEightMinusG (τ : ℍ) :
    (fun z => ckmrvEightMinusG τ z) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ := by
  have h := (((isBigO_linear_norm_coe.const_mul_left (eightMinusTauCoeff 0 τ)).add
      ((isBigO_const_one ℝ (eightMinusTauCoeff 1 τ) atImInfty).trans
        isBigO_one_real_norm_coe)).add
      ((isBigO_const_one ℝ (eightMinusTauCoeff 2 τ) atImInfty).trans
        isBigO_one_real_norm_coe)).const_mul_left (-ckmrvMinusScale⁻¹)
  refine h.congr_left fun z => ?_
  rw [ckmrvEightMinusG]

/-- Near `t = ∞`: `K₋(τ, it) = O(t)`. -/
theorem isBigO_ckmrvEightMinusKernel_imagPt_atTop (τ : ℍ) :
    (fun t => ckmrvEightMinusKernel τ (imagPt t)) =O[atTop]
      fun t => t * Real.exp (0 * t) := by
  have hKG : (fun z => ckmrvEightMinusKernel τ z - ckmrvEightMinusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ :=
    (isBigO_ckmrvEightMinusKernel_sub_G τ).trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (norm_nonneg _), one_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos]))))
  have hK : (fun z => ckmrvEightMinusKernel τ z) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ :=
    (hKG.add (isBigO_ckmrvEightMinusG τ)).congr_left fun z => sub_add_cancel _ _
  refine (hK.comp_tendsto tendsto_imagPt_atTop).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, norm_coe_imagPt ht, zero_mul, Real.exp_zero, mul_one,
    Real.norm_eq_abs, abs_of_pos ht, one_mul, le_refl]

/-- **Convergence of the Laplace integral (5.1), `d = 8`, minus kernel.** -/
theorem integrableOn_ckmrvEightMinusKernel_laplace (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightMinusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO (a := 0) (by positivity)
    (continuousOn_ckmrvEightMinusKernel_imagPt τ hτ)
    (isBigO_ckmrvEightMinusKernel_imagPt_zero τ) (isBigO_ckmrvEightMinusKernel_imagPt_atTop τ)

/-! ## Comparison functions along the imaginary axis -/

theorem isBigO_comp_imagPt {F : ℍ → ℂ} {w : ℝ → ℝ} {c : ℝ}
    (hF : F =O[atImInfty] fun z : ℍ => w ‖(z : ℂ)‖ * Real.exp (c * z.im)) :
    (fun t => F (imagPt t)) =O[atTop] fun t => w t * Real.exp (c * t) := by
  refine (hF.comp_tendsto tendsto_imagPt_atTop).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, norm_coe_imagPt ht, im_imagPt ht, one_mul, le_refl]

/-- `t^k e^{c t} = O(t e^{c' t})` for `k ≤ 2` and `c + 1 ≤ c'`. -/
theorem isBigO_pow_mul_exp_t {k : ℕ} (hk : k ≤ 2) {c c' : ℝ} (hc : c + 1 ≤ c') :
    (fun t : ℝ => t ^ k * Real.exp (c * t)) =O[atTop] fun t => t * Real.exp (c' * t) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hexp : t * Real.exp (c * t) ≤ Real.exp (c' * t) := by
    calc t * Real.exp (c * t) ≤ Real.exp t * Real.exp (c * t) := by
          gcongr
          linarith [Real.add_one_le_exp t]
      _ = Real.exp ((c + 1) * t) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (c' * t) := Real.exp_le_exp.mpr (by nlinarith)
  have hpow : t ^ k ≤ t ^ 2 := pow_le_pow_right₀ ht hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul]
  calc t ^ k * Real.exp (c * t) ≤ t ^ 2 * Real.exp (c * t) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = t * (t * Real.exp (c * t)) := by ring
    _ ≤ t * Real.exp (c' * t) := mul_le_mul_of_nonneg_left hexp ht0.le

theorem exp_le_exp_mul_of_le {c c' : ℝ} (h : c ≤ c') (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (c * y) ≤ Real.exp (c' * y) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h hy)

theorem isBigO_mul_exp_t_mono {c c' : ℝ} (hc : c ≤ c') :
    (fun t : ℝ => t * Real.exp (c * t)) =O[atTop] fun t => t * Real.exp (c' * t) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le),
    abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le), one_mul]
  exact mul_le_mul_of_nonneg_left (exp_le_exp_mul_of_le hc t ht) ht

/-! ## Dimension eight, plus kernel -/

theorem continuous_ckmrvTildePhiBasis (j : Fin 3) : Continuous fun z => ckmrvTildePhiBasis z j := by
  have h2 := E2_mdifferentiable.continuous
  have hz := UpperHalfPlane.continuous_coe
  fin_cases j <;> simp only [ckmrvTildePhiBasis, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] <;> fun_prop

theorem continuousOn_ckmrvEightPlusKernel_imagPt (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvEightPlusKernel τ (imagPt t)) (Ioi 0) := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hz := UpperHalfPlane.continuous_coe
  have hp1 := continuous_ckmrvTildePhiBasis 1
  have hp2 := continuous_ckmrvTildePhiBasis 2
  have hA : Continuous fun z : ℍ =>
      (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)) *
        (z : ℂ) ^ 2 := by fun_prop
  have hB : Continuous fun z : ℍ =>
      ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 * ModularForm.discriminant z * (z : ℂ) ^ 2 := by
    fun_prop
  have hC : Continuous fun z : ℍ =>
      -2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
          (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1) +
        ckmrvPhiBasis τ 0 * ModularForm.E₆ τ *
          (ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2) := by fun_prop
  have hD := (continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have h := (continuousOn_const (c := ckmrvPlusScale⁻¹)).mul
    (((continuousOn_comp_imagPt hA).add ((continuousOn_comp_imagPt hB).mul hD)).add
      (hD.mul (continuousOn_comp_imagPt hC)))
  refine h.congr fun t ht => ?_
  rw [ckmrvEightPlusKernel_eq_z τ (imagPt t) (sub_ne_zero.mpr (hτ t ht))]
  rfl

theorem isBigO_ckmrvEightPlusKernel_imagPt_zero (τ : ℍ) :
    (fun t => ckmrvEightPlusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ : (fun t : ℝ => ckmrvEightPlusKernel τ (ModularGroup.S • imagPt t⁻¹) *
      ((imagPt t⁻¹ : ℍ) : ℂ) ^ 2) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((isBigO_ckmrvEightPlusKernel_S_right τ).comp_tendsto tendsto_imagPt_inv).trans
    (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      simp only [Function.comp_apply, Real.norm_eq_abs, one_mul, Real.abs_exp, abs_one]
      have hy : 0 < (imagPt t⁻¹).im := (imagPt t⁻¹).im_pos
      apply Real.exp_le_one_iff.mpr
      nlinarith [Real.pi_pos]))
  have ht2 : (fun t : ℝ => -(t : ℂ) ^ 2) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 2) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht2).congr_right fun _ => one_mul _).congr' ?_ (Eventually.of_forall fun _ =>
    rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [S_smul_imagPt_inv ht0, mul_assoc, coe_imagPt_inv_sq ht0, mul_one]

theorem isBigO_ckmrvEightPlusG (τ : ℍ) :
    (fun z => ckmrvEightPlusG τ z) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ := by
  have h := ((isBigO_coe_norm.const_mul_left (12 * (Complex.I / (Real.pi : ℂ)) *
      (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))).add
    ((isBigO_const_one ℝ (36 / (Real.pi : ℂ) ^ 2 * (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ))
      atImInfty).trans isBigO_one_real_norm_coe)).const_mul_left ckmrvPlusScale⁻¹
  refine h.congr_left fun z => ?_
  rw [ckmrvEightPlusG]

theorem isBigO_ckmrvEightPlusKernel_imagPt_atTop (τ : ℍ) :
    (fun t => ckmrvEightPlusKernel τ (imagPt t)) =O[atTop] fun t => t * Real.exp (0 * t) := by
  have h1 := (isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -2 * π)
    (isBigO_ckmrvEightPlusKernel_sub_G τ)).trans
    (isBigO_pow_mul_exp_t (k := 2) le_rfl (c' := 0) (by nlinarith [Real.pi_gt_three]))
  have h2 := (isBigO_comp_imagPt (w := id) (c := 0) ((isBigO_ckmrvEightPlusG τ).congr_right
    fun z => by simp)).trans (isBigO_refl _ _)
  exact (h1.add h2).congr_left fun t => sub_add_cancel _ _

/-- **Convergence of the Laplace integral (5.1), `d = 8`, plus kernel.** -/
theorem integrableOn_ckmrvEightPlusKernel_laplace (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightPlusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO (a := 0) (by positivity)
    (continuousOn_ckmrvEightPlusKernel_imagPt τ hτ)
    (isBigO_ckmrvEightPlusKernel_imagPt_zero τ) (isBigO_ckmrvEightPlusKernel_imagPt_atTop τ)

/-! ## The Leech kernels -/

theorem continuousOn_ckmrvLeechMinusKernel_imagPt (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvLeechMinusKernel τ (imagPt t)) (Ioi 0) := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hz := UpperHalfPlane.continuous_coe
  have hL := continuous_ckmrvL
  have hU := mdifferentiable_thetaU.continuous
  have hV := mdifferentiable_thetaV.continuous
  have hW := mdifferentiable_thetaW.continuous
  have hDc := continuous_eightMinusDenZ τ
  have hN : Continuous fun z : ℍ => ckmrvEll z * leechMinusNEll τ z + leechMinusNZero τ z := by
    simp only [ckmrvEll, leechMinusNEll, leechMinusNZero]
    fun_prop
  have hD := (continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have hΔi := (continuousOn_comp_imagPt hΔ).inv₀ fun t _ => ModularForm.discriminant_ne_zero _
  have h := (((continuousOn_const (c := ckmrvMinusScale⁻¹)).mul hD).mul hΔi).mul
    (continuousOn_comp_imagPt hN)
  refine h.congr fun t _ => ?_
  rw [ckmrvLeechMinusKernel_eq_z]
  rfl

theorem isBigO_ckmrvLeechMinusKernel_imagPt_zero (τ : ℍ) :
    (fun t => ckmrvLeechMinusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ : (fun t : ℝ => ckmrvLeechMinusKernel τ (ModularGroup.S • imagPt t⁻¹) *
      ((imagPt t⁻¹ : ℍ) : ℂ) ^ 10) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((isBigO_ckmrvLeechMinusKernel_S_right τ).comp_tendsto tendsto_imagPt_inv).trans
    (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      simp only [Function.comp_apply, Real.norm_eq_abs, one_mul, Real.abs_exp, abs_one]
      have hy : 0 < (imagPt t⁻¹).im := (imagPt t⁻¹).im_pos
      apply Real.exp_le_one_iff.mpr
      nlinarith [Real.pi_pos]))
  have ht10 : (fun t : ℝ => -(t : ℂ) ^ 10) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 10) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht10).congr_right fun _ => one_mul _).congr' ?_ (Eventually.of_forall fun _ =>
    rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [S_smul_imagPt_inv ht0, mul_assoc, coe_imagPt_inv_pow_ten ht0, mul_one]

theorem isBigO_norm_le_norm_mul_exp_two_pi :
    (fun z : ℍ => ‖(z : ℂ)‖) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (2 * π * z.im) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    have he : 1 ≤ Real.exp (2 * π * z.im) := Real.one_le_exp (by nlinarith [Real.pi_pos, z.im_pos])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (by positivity), one_mul]
    nlinarith [norm_nonneg (z : ℂ)])

theorem isBigO_ckmrvLeechMinusG (τ : ℍ) :
    (fun z => ckmrvLeechMinusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (2 * π * z.im) := by
  have hA : (fun z : ℍ => ckmrvEll z * (2 * 1728 * ModularForm.discriminant τ) +
      (leechMinusBeta τ + leechMinusAlpha τ)) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ :=
    ((isBigO_ckmrvEll.mul (isBigO_const_one ℝ _ atImInfty)).congr_right (fun _ => mul_one _)).add
      ((isBigO_const_one ℝ _ atImInfty).trans isBigO_one_real_norm_coe)
  have hC : (fun z : ℍ => ckmrvEll z * (-(2 * 1728) * ModularForm.discriminant τ *
      (720 - kleinModularJ τ)) +
      ((-leechMinusBeta τ - leechMinusAlpha τ) * (696 - kleinModularJ τ) - leechMinusNZeroC τ))
      =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ :=
    ((isBigO_ckmrvEll.mul (isBigO_const_one ℝ _ atImInfty)).congr_right (fun _ => mul_one _)).add
      ((isBigO_const_one ℝ _ atImInfty).trans isBigO_one_real_norm_coe)
  have h := (((isBigO_cuspS_sq_inv.mul hA).congr_right fun _ => mul_comm _ _).add
    (hC.trans isBigO_norm_le_norm_mul_exp_two_pi)).const_mul_left ckmrvMinusScale⁻¹
  refine h.congr_left fun z => ?_
  rw [ckmrvLeechMinusG]
  ring

theorem isBigO_ckmrvLeechMinusKernel_imagPt_atTop (τ : ℍ) :
    (fun t => ckmrvLeechMinusKernel τ (imagPt t)) =O[atTop]
      fun t => t * Real.exp (2 * π * t) := by
  have h1 := (isBigO_comp_imagPt (w := id) (c := -π) (isBigO_ckmrvLeechMinusKernel_sub_G τ)).trans
    (isBigO_mul_exp_t_mono (c' := 2 * π) (by nlinarith [Real.pi_pos]))
  have h2 := isBigO_comp_imagPt (w := id) (c := 2 * π) (isBigO_ckmrvLeechMinusG τ)
  refine (h1.add (h2.congr_right fun t => rfl)).congr_left fun t => sub_add_cancel _ _

/-- **Convergence of the Laplace integral (5.1), Leech minus kernel, for `r² > 2`.** -/
theorem integrableOn_ckmrvLeechMinusKernel_laplace (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechMinusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO (a := 2 * π) (by nlinarith [Real.pi_pos])
    (continuousOn_ckmrvLeechMinusKernel_imagPt τ hτ)
    (isBigO_ckmrvLeechMinusKernel_imagPt_zero τ) (isBigO_ckmrvLeechMinusKernel_imagPt_atTop τ)

theorem continuousOn_ckmrvLeechPlusKernel_imagPt (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvLeechPlusKernel τ (imagPt t)) (Ioi 0) := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hz := UpperHalfPlane.continuous_coe
  have hp1 := continuous_ckmrvTildePhiBasis 1
  have hp2 := continuous_ckmrvTildePhiBasis 2
  have hA : Continuous fun z : ℍ => leechPlusAz τ z := by simp only [leechPlusAz]; fun_prop
  have hB : Continuous fun z : ℍ => leechPlusBz τ z := by simp only [leechPlusBz]; fun_prop
  have hD := (continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have hΔi := (continuousOn_comp_imagPt hΔ).inv₀ fun t _ => ModularForm.discriminant_ne_zero _
  have h := (continuousOn_const (c := (1728 * ckmrvPlusScale)⁻¹)).mul
    ((hΔi.mul (continuousOn_comp_imagPt hA)).add ((hD.mul hΔi).mul (continuousOn_comp_imagPt hB)))
  refine h.congr fun t _ => ?_
  rw [ckmrvLeechPlusKernel_eq_z]
  rfl

theorem isBigO_ckmrvLeechPlusKernel_imagPt_zero (τ : ℍ) :
    (fun t => ckmrvLeechPlusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ : (fun t : ℝ => ckmrvLeechPlusKernel τ (ModularGroup.S • imagPt t⁻¹) *
      ((imagPt t⁻¹ : ℍ) : ℂ) ^ 10) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((isBigO_ckmrvLeechPlusKernel_S_right τ).comp_tendsto tendsto_imagPt_inv).trans
    (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      simp only [Function.comp_apply, Real.norm_eq_abs, one_mul, Real.abs_exp, abs_one]
      have hy : 0 < (imagPt t⁻¹).im := (imagPt t⁻¹).im_pos
      apply Real.exp_le_one_iff.mpr
      nlinarith [Real.pi_pos]))
  have ht10 : (fun t : ℝ => -(t : ℂ) ^ 10) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 10) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht10).congr_right fun _ => one_mul _).congr' ?_ (Eventually.of_forall fun _ =>
    rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [S_smul_imagPt_inv ht0, mul_assoc, coe_imagPt_inv_pow_ten ht0, mul_one]

theorem isBigO_ckmrvLeechPlusG (τ : ℍ) :
    (fun z => ckmrvLeechPlusG τ z) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (2 * π * z.im) := by
  have hA : (fun z : ℍ => (z : ℂ) * leechPlusM1a τ + leechPlusM0a τ) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ :=
    ((isBigO_coe_norm.mul (isBigO_const_one ℝ _ atImInfty)).congr_right (fun _ => mul_one _)).add
      ((isBigO_const_one ℝ _ atImInfty).trans isBigO_one_real_norm_coe)
  have hC : (fun z : ℍ => (z : ℂ) * leechPlusM1c τ + leechPlusM0c τ) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ :=
    ((isBigO_coe_norm.mul (isBigO_const_one ℝ _ atImInfty)).congr_right (fun _ => mul_one _)).add
      ((isBigO_const_one ℝ _ atImInfty).trans isBigO_one_real_norm_coe)
  have h := (((isBigO_cuspS_sq_inv.mul hA).congr_right fun _ => mul_comm _ _).add
    (hC.trans isBigO_norm_le_norm_mul_exp_two_pi)).const_mul_left (1728 * ckmrvPlusScale)⁻¹
  refine h.congr_left fun z => ?_
  rw [ckmrvLeechPlusG]
  ring

theorem isBigO_ckmrvLeechPlusKernel_imagPt_atTop (τ : ℍ) :
    (fun t => ckmrvLeechPlusKernel τ (imagPt t)) =O[atTop]
      fun t => t * Real.exp (2 * π * t) := by
  have h1 := (isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -π)
    (isBigO_ckmrvLeechPlusKernel_sub_G τ)).trans
    (isBigO_pow_mul_exp_t (k := 2) le_rfl (c' := 2 * π) (by nlinarith [Real.pi_gt_three]))
  have h2 := isBigO_comp_imagPt (w := id) (c := 2 * π) (isBigO_ckmrvLeechPlusG τ)
  refine (h1.add (h2.congr_right fun t => rfl)).congr_left fun t => sub_add_cancel _ _

/-- **Convergence of the Laplace integral (5.1), Leech plus kernel, for `r² > 2`.** -/
theorem integrableOn_ckmrvLeechPlusKernel_laplace (τ : ℍ)
    (hτ : ∀ t : ℝ, 0 < t → kleinModularJ τ ≠ kleinModularJ (imagPt t)) {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechPlusKernel τ (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) :=
  integrableOn_Ioi_mul_exp_of_isBigO (a := 2 * π) (by nlinarith [Real.pi_pos])
    (continuousOn_ckmrvLeechPlusKernel_imagPt τ hτ)
    (isBigO_ckmrvLeechPlusKernel_imagPt_zero τ) (isBigO_ckmrvLeechPlusKernel_imagPt_atTop τ)

end E8Leech
