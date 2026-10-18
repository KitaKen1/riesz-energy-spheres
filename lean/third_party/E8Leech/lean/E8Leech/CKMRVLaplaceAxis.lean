import E8Leech.CKMRVLaplace
import E8Leech.CKMRVPlusRemovable
import E8Leech.CKMRVMeromorphic
import E8Leech.CKMRVActualDerivatives

/-!
# The Laplace integrals for `τ` on the imaginary axis (P4d, second step: plus kernels)

For `τ = iβ` the integrand `t ↦ K₊(iβ, it)` of CKMRV (5.1) meets the zeros of `j(τ) - j(it)` at
`t = β` and `t = 1/β`. There the singularities are removable (CKMRV: the residues are
`φ(I) = φ(S) = 0`). For the plus kernels this is elementary: after clearing `j(τ) - j(z)` the
singular numerator vanishes at `z = τ`, and the one of `K₊ ∣ S` vanishes at `w = τ`; both
identities only use `i² = -1`. With removable singularities at two points the integral converges
exactly as in `CKMRVLaplace`.

The hypotheses `j'(iβ) ≠ 0` (i.e. `E₄ E₆ (iβ) ≠ 0`, so `β ≠ 1`) and "no other `t` with
`j(it) = j(iβ)`" are kept explicit here.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Removable singularities in the second variable -/

theorem exists_tendsto_div_kleinModularJ_sub {τ : ℍ} {F : ℍ → ℂ} (hF : MDiff F) (hF0 : F τ = 0)
    (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => F (UpperHalfPlane.ofComplex w) /
      (kleinModularJ τ - kleinModularJ (UpperHalfPlane.ofComplex w))) (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  have hf := (analyticAt_of_upperHalfPlane_mdifferentiable hF τ).differentiableAt.hasDerivAt.neg
  have h := tendsto_removable_quotient hf (by simp [UpperHalfPlane.ofComplex_apply, hF0])
    (hasDerivAt_kleinModularJ τ) hj
  refine ⟨_, h.congr' (Eventually.of_forall fun w => ?_)⟩
  have hs : kleinModularJ τ - kleinModularJ (UpperHalfPlane.ofComplex w) =
      -(kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ τ) := by ring
  simp only [UpperHalfPlane.ofComplex_apply, Pi.neg_apply]
  rw [hs, div_neg, neg_div]

/-- `D(z) = Δ(z) (j(τ) - j(z))`. -/
theorem eightMinusDenZ_eq_mul (τ z : ℍ) :
    eightMinusDenZ τ z = ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z) := by
  rw [eightMinusDenZ]
  linear_combination kleinModularJ_mul_discriminant z

/-! ## A Laplace integrability criterion with two removable points -/

theorem integrableOn_Ioi_mul_exp_of_isBigO_two {f : ℝ → ℂ} {a b p q : ℝ} (hab : a < b)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hcont : ∀ x : ℝ, 0 < x → x ≠ p → x ≠ q → ContinuousAt f x)
    (hLp : ∃ L, Tendsto f (𝓝[≠] p) (𝓝 L)) (hLq : ∃ L, Tendsto f (𝓝[≠] q) (𝓝 L))
    (h0 : f =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hinf : f =O[atTop] fun t => t * Real.exp (a * t)) :
    IntegrableOn (fun t => f t * (Real.exp (-b * t) : ℂ)) (Ioi 0) := by
  classical
  obtain ⟨Lp, hfp⟩ := hLp
  obtain ⟨Lq, hfq⟩ := hLq
  set g : ℝ → ℂ := Function.update (Function.update f p Lp) q Lq with hg
  have hgf : ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x := fun x hxp hxq => by
    rw [hg, Function.update_of_ne hxq, Function.update_of_ne hxp]
  have hcontg : ContinuousOn g (Ioi 0) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hxq : x = q
    · subst hxq
      rw [hg, continuousAt_update_same]
      refine hfq.congr' ?_
      filter_upwards [(eventually_ne_nhds hpq.symm).filter_mono nhdsWithin_le_nhds] with y hy
      rw [Function.update_of_ne hy]
    · rw [hg, continuousAt_update_of_ne hxq]
      by_cases hxp : x = p
      · subst hxp
        exact continuousAt_update_same.mpr hfp
      · rw [continuousAt_update_of_ne hxp]
        exact hcont x hx hxp hxq
  have hev0 : g =ᶠ[𝓝[>] (0 : ℝ)] f := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hp hq)] with x hx
    exact hgf x (ne_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _)))
      (ne_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _)))
  have hevt : g =ᶠ[atTop] f := by
    filter_upwards [eventually_gt_atTop (max p q)] with x hx
    exact hgf x (ne_of_gt (lt_of_le_of_lt (le_max_left _ _) hx))
      (ne_of_gt (lt_of_le_of_lt (le_max_right _ _) hx))
  have hint := integrableOn_Ioi_mul_exp_of_isBigO hab hcontg (h0.congr' hev0.symm EventuallyEq.rfl)
    (hinf.congr' hevt.symm EventuallyEq.rfl)
  refine hint.congr_fun_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  have hfin : volume ({p, q} : Set ℝ) = 0 := (Set.toFinite {p, q}).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfin] with x hx _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  rw [hgf x hx.1 hx.2]

/-! ## Approaching a point of the imaginary axis -/

theorem tendsto_I_mul_punctured {β : ℝ} :
    Tendsto (fun t : ℝ => (I * t : ℂ)) (𝓝[≠] β) (𝓝[≠] (I * β : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨((Continuous.tendsto (by fun_prop) β).mono_left
    nhdsWithin_le_nhds), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht h
  apply ht
  have := congrArg (fun w : ℂ => (w / I).re) h
  simpa using this

theorem tendsto_I_mul_inv_punctured {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun t : ℝ => (I * (t⁻¹ : ℝ) : ℂ)) (𝓝[≠] β⁻¹) (𝓝[≠] (I * β : ℂ)) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[≠] β⁻¹) (𝓝[≠] β) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := ((continuousAt_inv₀ (inv_ne_zero hβ.ne')).tendsto).mono_left
        (nhdsWithin_le_nhds (s := {β⁻¹}ᶜ))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with t ht h
      apply ht
      have : t = β⁻¹ := by rw [← h, inv_inv]
      exact this
  exact tendsto_I_mul_punctured.comp hinv

theorem coe_imagPt_eq (t : ℝ) (ht : 0 < t) : ((imagPt t : ℍ) : ℂ) = I * t := coe_imagPt ht

/-! ## The dimension-eight plus kernel on the imaginary axis -/

/-- The singular numerator of `K₊⁽⁸⁾(τ, ·)`: `K₊ = c₊⁻¹ ((a₀ - 2a₁) z² + Ñ(z) / (Δ(z) (j(τ)-j(z))))`. -/
def eightPlusSingNum (τ z : ℍ) : ℂ :=
  ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 * ModularForm.discriminant z * (z : ℂ) ^ 2 +
    (-2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
        (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1) +
      ckmrvPhiBasis τ 0 * ModularForm.E₆ τ * (ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2))

/-- The singular numerator of `K₊⁽⁸⁾ ∣ S`. -/
def eightPlusSingNumS (τ w : ℍ) : ℂ :=
  ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 * ModularForm.discriminant w -
    2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
      (ModularForm.E₄ w * ModularForm.E₆ w * EisensteinSeries.E2 w) +
    ckmrvPhiBasis τ 0 * ModularForm.E₆ τ * (ModularForm.E₄ w ^ 2 * EisensteinSeries.E2 w ^ 2)

theorem ckmrvModularFactor_two_eq (τ : ℍ) :
    ckmrvModularFactor τ 2 =
      ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * (ModularForm.discriminant τ)⁻¹ := by
  rw [← div_eq_mul_inv, ← eisensteinFourteen_eq_four_sq_mul_six]
  rfl

theorem eightPlusSingNum_self (τ : ℍ) : eightPlusSingNum τ τ = 0 := by
  have hu : ModularForm.discriminant τ * (ModularForm.discriminant τ)⁻¹ = 1 :=
    mul_inv_cancel₀ (ModularForm.discriminant_ne_zero τ)
  have hp0 : ckmrvPhiBasis τ 0 = τ := rfl
  have ht1 : ckmrvTildePhiBasis τ 1 = (τ : ℂ) ^ 2 * EisensteinSeries.E2 τ -
      6 * Complex.I / (Real.pi : ℂ) * τ := rfl
  have ht2 : ckmrvTildePhiBasis τ 2 = (τ : ℂ) ^ 2 * EisensteinSeries.E2 τ ^ 2 -
      12 * Complex.I / (Real.pi : ℂ) * τ * EisensteinSeries.E2 τ - 36 / (Real.pi : ℂ) ^ 2 := rfl
  rw [eightPlusSingNum, ckmrvModularFactor_two_eq, hp0, ht1, ht2, leechPlus_phi_one,
    leechPlus_phi_two]
  linear_combination
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * (τ : ℂ) ^ 2 * ((τ : ℂ) * EisensteinSeries.E2 τ ^ 2 -
      6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 τ)) * hu +
    (-36 * (τ : ℂ) * ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ / (Real.pi : ℂ) ^ 2) * Complex.I_sq

theorem eightPlusSingNumS_self (τ : ℍ) : eightPlusSingNumS τ τ = 0 := by
  have hu : ModularForm.discriminant τ * (ModularForm.discriminant τ)⁻¹ = 1 :=
    mul_inv_cancel₀ (ModularForm.discriminant_ne_zero τ)
  have hp0 : ckmrvPhiBasis τ 0 = τ := rfl
  rw [eightPlusSingNumS, ckmrvModularFactor_two_eq, hp0, leechPlus_phi_one, leechPlus_phi_two]
  linear_combination
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * ((τ : ℂ) * EisensteinSeries.E2 τ ^ 2 -
      6 * Complex.I / (Real.pi : ℂ) * EisensteinSeries.E2 τ)) * hu

theorem mdifferentiable_eightPlusSingNum (τ : ℍ) : MDiff (fun z => eightPlusSingNum τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  exact ((mdifferentiable_const.mul hΔ).mul (UpperHalfPlane.mdifferentiable_coe.pow 2)).add
    ((mdifferentiable_const.mul ((h4.mul h6).mul (mdifferentiable_ckmrvTildePhiBasis 1))).add
      (mdifferentiable_const.mul ((h4.pow 2).mul (mdifferentiable_ckmrvTildePhiBasis 2))))

theorem mdifferentiable_eightPlusSingNumS (τ : ℍ) : MDiff (fun w => eightPlusSingNumS τ w) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  exact ((mdifferentiable_const.mul hΔ).sub
    (mdifferentiable_const.mul ((h4.mul h6).mul E2_mdifferentiable))).add
    (mdifferentiable_const.mul ((h4.pow 2).mul (E2_mdifferentiable.pow 2)))

theorem ckmrvEightPlusKernel_eq_sing (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0) :
    ckmrvEightPlusKernel τ z = ckmrvPlusScale⁻¹ *
      ((ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)) *
          (z : ℂ) ^ 2 +
        eightPlusSingNum τ z / ModularForm.discriminant z /
          (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvEightPlusKernel_eq_z τ z hg, eightMinusDenZ_eq_mul, eightPlusSingNum, div_div]
  ring

theorem ckmrvEightPlusKernel_S_eq_sing (τ w : ℍ) (hg : kleinModularJ τ - kleinModularJ w ≠ 0) :
    ckmrvEightPlusKernel τ (ModularGroup.S • w) * (w : ℂ) ^ 2 = ckmrvPlusScale⁻¹ *
      ((ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)) +
        eightPlusSingNumS τ w / ModularForm.discriminant w /
          (kleinModularJ τ - kleinModularJ w)) := by
  rw [ckmrvEightPlusKernel_S_right τ w hg, eightMinusDenZ_eq_mul, eightPlusSingNumS, div_div]
  ring

/-- `t ↦ K₊⁽⁸⁾(τ, ofComplex w)` has a finite limit at `w = τ`. -/
theorem exists_tendsto_ckmrvEightPlusKernel_right (τ : ℍ) (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvEightPlusKernel τ (UpperHalfPlane.ofComplex w))
      (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => eightPlusSingNum τ z /
    ModularForm.discriminant z) ((mdifferentiable_eightPlusSingNum τ).div
      mdifferentiable_modularDiscriminant ModularForm.discriminant_ne_zero)
    (by simp [eightPlusSingNum_self]) hj
  have hz : Tendsto (fun w : ℂ => ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) ^ 2) (𝓝[≠] (τ : ℂ))
      (𝓝 ((τ : ℂ) ^ 2)) := by
    have h : Tendsto (fun w : ℂ => w ^ 2) (𝓝[≠] (τ : ℂ)) (𝓝 ((τ : ℂ) ^ 2)) :=
      ((continuous_pow 2).tendsto _).mono_left nhdsWithin_le_nhds
    refine h.congr' ?_
    filter_upwards [nhdsWithin_le_nhds
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with w hw
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  refine ⟨_, (((tendsto_const_nhds (x := ckmrvPhiBasis τ 0 * ModularForm.E₆ τ -
    2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))).mul hz).add hL₀ |>.const_mul
      ckmrvPlusScale⁻¹).congr' ?_⟩
  filter_upwards [eventually_kleinModularJ_gap_ne_zero τ hj] with w hw
  rw [ckmrvEightPlusKernel_eq_sing τ _ (by intro h; apply hw; linear_combination -h)]

/-- `w ↦ K₊⁽⁸⁾(τ, S • ofComplex w) · w²` has a finite limit at `w = τ`. -/
theorem exists_tendsto_ckmrvEightPlusKernel_S_right (τ : ℍ) (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvEightPlusKernel τ
      (ModularGroup.S • UpperHalfPlane.ofComplex w) * ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) ^ 2)
      (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => eightPlusSingNumS τ z /
    ModularForm.discriminant z) ((mdifferentiable_eightPlusSingNumS τ).div
      mdifferentiable_modularDiscriminant ModularForm.discriminant_ne_zero)
    (by simp [eightPlusSingNumS_self]) hj
  refine ⟨_, (((tendsto_const_nhds (x := ckmrvPhiBasis τ 0 * ModularForm.E₆ τ -
    2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ))).add hL₀).const_mul ckmrvPlusScale⁻¹).congr' ?_⟩
  filter_upwards [eventually_kleinModularJ_gap_ne_zero τ hj] with w hw
  rw [ckmrvEightPlusKernel_S_eq_sing τ _ (by intro h; apply hw; linear_combination -h)]

theorem continuousOn_ckmrvEightPlusKernel_imagPt' (τ : ℍ) {s : Set ℝ} (hs : s ⊆ Ioi 0)
    (hτ : ∀ t ∈ s, kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvEightPlusKernel τ (imagPt t)) s := by
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
  have hD := ((continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).mono hs).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have h := (continuousOn_const (c := ckmrvPlusScale⁻¹)).mul
    ((((continuousOn_comp_imagPt hA).mono hs).add
      (((continuousOn_comp_imagPt hB).mono hs).mul hD)).add
      (hD.mul ((continuousOn_comp_imagPt hC).mono hs)))
  refine h.congr fun t ht => ?_
  rw [ckmrvEightPlusKernel_eq_z τ (imagPt t) (sub_ne_zero.mpr (hτ t ht))]
  rfl

theorem ne_inv_of_ne_one {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) : β ≠ β⁻¹ := by
  intro h
  apply hβ1
  have h2 : β * β = 1 := by
    calc β * β = β * β⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hβ.ne'
  nlinarith [sq_nonneg (β - 1)]

/-- **CKMRV (5.1) on the imaginary axis, `d = 8`, plus kernel.** For `τ = iβ` with
`j'(iβ) ≠ 0`, the only zeros of `j(iβ) - j(it)` being `t = β, 1/β`, the Laplace integral
converges absolutely for `r ≠ 0`: the singularities at `t = β, 1/β` are removable. -/
theorem integrableOn_ckmrvEightPlusKernel_laplace_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1)
    (hj : kleinModularJDerivative (imagPt β) ≠ 0)
    (hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t))
    {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightPlusKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) := by
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine integrableOn_Ioi_mul_exp_of_isBigO_two (a := 0) (p := β) (q := β⁻¹) (by positivity) hβ
    (inv_pos.mpr hβ) (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
    (isBigO_ckmrvEightPlusKernel_imagPt_zero τ) (isBigO_ckmrvEightPlusKernel_imagPt_atTop τ)
  · intro x hx hxp hxq
    set s : Set ℝ := Ioi 0 ∩ ({β}ᶜ ∩ {β⁻¹}ᶜ)
    have hsopen : IsOpen s := isOpen_Ioi.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)
    have hxs : x ∈ s := ⟨hx, hxp, hxq⟩
    exact (continuousOn_ckmrvEightPlusKernel_imagPt' τ (fun t ht => ht.1)
      (fun t ht => hpole t ht.1 ht.2.1 ht.2.2)).continuousAt (hsopen.mem_nhds hxs)
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightPlusKernel_right τ hj
    rw [hτc] at hL
    exact ⟨L, hL.comp tendsto_I_mul_punctured⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightPlusKernel_S_right τ hj
    rw [hτc] at hL
    have hsq : Tendsto (fun t : ℝ => -((t : ℂ) ^ 2)) (𝓝[≠] β⁻¹) (𝓝 (-((β⁻¹ : ℝ) : ℂ) ^ 2)) :=
      ((Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds)
    refine ⟨_, ((hL.comp (tendsto_I_mul_inv_punctured hβ)).mul hsq).congr' ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds (inv_pos.mpr hβ)) :
      Ioi (0 : ℝ) ∈ 𝓝[≠] β⁻¹)] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    have hS := S_smul_imagPt_inv ht0
    have hsq1 := coe_imagPt_inv_sq ht0
    simp only [imagPt] at hS hsq1 ⊢
    rw [hS, mul_assoc]
    rw [show ((UpperHalfPlane.ofComplex (I * ((t⁻¹ : ℝ) : ℂ)) : ℍ) : ℂ) ^ 2 * -((t : ℂ) ^ 2) = 1
      from by simpa [neg_mul] using hsq1, mul_one]

/-! ## The Leech plus kernel on the imaginary axis -/

theorem leechPlusBz_self (τ : ℍ) : leechPlusBz τ τ = 0 := by
  have ht1 : ckmrvTildePhiBasis τ 1 = (τ : ℂ) ^ 2 * EisensteinSeries.E2 τ -
      6 * Complex.I / (Real.pi : ℂ) * τ := rfl
  have ht2 : ckmrvTildePhiBasis τ 2 = (τ : ℂ) ^ 2 * EisensteinSeries.E2 τ ^ 2 -
      12 * Complex.I / (Real.pi : ℂ) * τ * EisensteinSeries.E2 τ - 36 / (Real.pi : ℂ) ^ 2 := rfl
  rw [leechPlusBz, leechPlusA0, leechPlusA1, leechPlusA2, ht1, ht2, leechPlus_phi_one,
    leechPlus_phi_two]
  linear_combination (1728 * ModularForm.discriminant τ * ModularForm.E₄ τ ^ 2 *
    ModularForm.E₆ τ * (-36 * (τ : ℂ) / (Real.pi : ℂ) ^ 2)) * Complex.I_sq

theorem leechPlusB2z_self (τ : ℍ) : leechPlusB2z τ τ = 0 := by
  rw [leechPlusB2z, leechPlusA0, leechPlusA1, leechPlusA2, leechPlus_phi_one, leechPlus_phi_two]
  ring

theorem mdifferentiable_leechPlusBz (τ : ℍ) : MDiff (fun z => leechPlusBz τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  exact (((mdifferentiable_const.mul h4).mul (UpperHalfPlane.mdifferentiable_coe.pow 2)).mul hΔ
    |>.sub ((mdifferentiable_const.mul ((h4.pow 2).mul h6)).mul
      (mdifferentiable_ckmrvTildePhiBasis 1))).add
    ((mdifferentiable_const.mul (mdifferentiable_ckmrvTildePhiBasis 2)).mul hΔ)

theorem mdifferentiable_leechPlusB2z (τ : ℍ) : MDiff (fun z => leechPlusB2z τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  exact ((mdifferentiable_const.mul (h4.mul hΔ)).sub
    (mdifferentiable_const.mul (((h4.pow 2).mul h6).mul E2_mdifferentiable))).add
    (mdifferentiable_const.mul ((E2_mdifferentiable.pow 2).mul hΔ))

theorem continuous_leechPlusAz_div (τ : ℍ) :
    Continuous fun z : ℍ => (ModularForm.discriminant z)⁻¹ * leechPlusAz τ z := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have hz := UpperHalfPlane.continuous_coe
  have hp2 := continuous_ckmrvTildePhiBasis 2
  have hΔi : Continuous fun z : ℍ => (ModularForm.discriminant z)⁻¹ :=
    mdifferentiable_modularDiscriminant.continuous.inv₀ ModularForm.discriminant_ne_zero
  have hA : Continuous fun z : ℍ => leechPlusAz τ z := by simp only [leechPlusAz]; fun_prop
  exact hΔi.mul hA

theorem continuous_leechPlusA2z_div (τ : ℍ) :
    Continuous fun z : ℍ => (ModularForm.discriminant z)⁻¹ * leechPlusA2z τ z := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h2 := E2_mdifferentiable.continuous
  have hΔi : Continuous fun z : ℍ => (ModularForm.discriminant z)⁻¹ :=
    mdifferentiable_modularDiscriminant.continuous.inv₀ ModularForm.discriminant_ne_zero
  have hA : Continuous fun z : ℍ => leechPlusA2z τ z := by simp only [leechPlusA2z]; fun_prop
  exact hΔi.mul hA

theorem ckmrvLeechPlusKernel_eq_sing (τ z : ℍ) :
    ckmrvLeechPlusKernel τ z = (1728 * ckmrvPlusScale)⁻¹ *
      ((ModularForm.discriminant z)⁻¹ * leechPlusAz τ z +
        leechPlusBz τ z / ModularForm.discriminant z ^ 2 /
          (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvLeechPlusKernel_eq_z, eightMinusDenZ_eq_mul, mul_inv (ModularForm.discriminant z)]
  ring

theorem ckmrvLeechPlusKernel_S_eq_sing (τ w : ℍ) :
    ckmrvLeechPlusKernel τ (ModularGroup.S • w) * (w : ℂ) ^ 10 = (1728 * ckmrvPlusScale)⁻¹ *
      ((ModularForm.discriminant w)⁻¹ * leechPlusA2z τ w +
        leechPlusB2z τ w / ModularForm.discriminant w ^ 2 /
          (kleinModularJ τ - kleinModularJ w)) := by
  rw [ckmrvLeechPlusKernel_S_right, eightMinusDenZ_eq_mul, mul_inv (ModularForm.discriminant w)]
  ring

theorem tendsto_comp_ofComplex_punctured {F : ℍ → ℂ} (hF : Continuous F) (τ : ℍ) :
    Tendsto (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (𝓝[≠] (τ : ℂ)) (𝓝 (F τ)) := by
  have h : ContinuousAt (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (τ : ℂ) := by
    have hof : ContinuousAt UpperHalfPlane.ofComplex (τ : ℂ) :=
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) τ.im_pos).continuousAt
    exact ContinuousAt.comp (g := F) (f := UpperHalfPlane.ofComplex) hF.continuousAt hof
  have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := {(τ : ℂ)}ᶜ))
  simpa [UpperHalfPlane.ofComplex_apply] using this

theorem exists_tendsto_ckmrvLeechPlusKernel_right (τ : ℍ) (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvLeechPlusKernel τ (UpperHalfPlane.ofComplex w))
      (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => leechPlusBz τ z /
    ModularForm.discriminant z ^ 2) ((mdifferentiable_leechPlusBz τ).div
      (mdifferentiable_modularDiscriminant.pow 2)
      (fun z => pow_ne_zero 2 (ModularForm.discriminant_ne_zero z)))
    (by simp [leechPlusBz_self]) hj
  refine ⟨_, ((tendsto_comp_ofComplex_punctured (continuous_leechPlusAz_div τ) τ).add hL₀
    |>.const_mul (1728 * ckmrvPlusScale)⁻¹).congr' (Eventually.of_forall fun w => ?_)⟩
  beta_reduce
  rw [ckmrvLeechPlusKernel_eq_sing]

theorem exists_tendsto_ckmrvLeechPlusKernel_S_right (τ : ℍ)
    (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvLeechPlusKernel τ
      (ModularGroup.S • UpperHalfPlane.ofComplex w) *
        ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) ^ 10) (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => leechPlusB2z τ z /
    ModularForm.discriminant z ^ 2) ((mdifferentiable_leechPlusB2z τ).div
      (mdifferentiable_modularDiscriminant.pow 2)
      (fun z => pow_ne_zero 2 (ModularForm.discriminant_ne_zero z)))
    (by simp [leechPlusB2z_self]) hj
  refine ⟨_, ((tendsto_comp_ofComplex_punctured (continuous_leechPlusA2z_div τ) τ).add hL₀
    |>.const_mul (1728 * ckmrvPlusScale)⁻¹).congr' (Eventually.of_forall fun w => ?_)⟩
  beta_reduce
  rw [ckmrvLeechPlusKernel_S_eq_sing]

theorem continuousOn_ckmrvLeechPlusKernel_imagPt' (τ : ℍ) {s : Set ℝ} (hs : s ⊆ Ioi 0)
    (hτ : ∀ t ∈ s, kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvLeechPlusKernel τ (imagPt t)) s := by
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hB : Continuous fun z : ℍ => leechPlusBz τ z := (mdifferentiable_leechPlusBz τ).continuous
  have hD := ((continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).mono hs).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have hΔi := ((continuousOn_comp_imagPt hΔ).mono hs).inv₀
    fun t _ => ModularForm.discriminant_ne_zero _
  have h := (continuousOn_const (c := (1728 * ckmrvPlusScale)⁻¹)).mul
    (((continuousOn_comp_imagPt (continuous_leechPlusAz_div τ)).mono hs).add
      ((hD.mul hΔi).mul ((continuousOn_comp_imagPt hB).mono hs)))
  refine h.congr fun t _ => ?_
  rw [ckmrvLeechPlusKernel_eq_z]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.inv_apply]

/-- **CKMRV (5.1) on the imaginary axis, Leech plus kernel, for `r² > 2`.** -/
theorem integrableOn_ckmrvLeechPlusKernel_laplace_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1)
    (hj : kleinModularJDerivative (imagPt β) ≠ 0)
    (hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t))
    {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechPlusKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) := by
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine integrableOn_Ioi_mul_exp_of_isBigO_two (a := 2 * π) (p := β) (q := β⁻¹)
    (by nlinarith [Real.pi_pos]) hβ (inv_pos.mpr hβ) (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
    (isBigO_ckmrvLeechPlusKernel_imagPt_zero τ) (isBigO_ckmrvLeechPlusKernel_imagPt_atTop τ)
  · intro x hx hxp hxq
    set s : Set ℝ := Ioi 0 ∩ ({β}ᶜ ∩ {β⁻¹}ᶜ)
    have hsopen : IsOpen s := isOpen_Ioi.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)
    have hxs : x ∈ s := ⟨hx, hxp, hxq⟩
    exact (continuousOn_ckmrvLeechPlusKernel_imagPt' τ (fun t ht => ht.1)
      (fun t ht => hpole t ht.1 ht.2.1 ht.2.2)).continuousAt (hsopen.mem_nhds hxs)
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechPlusKernel_right τ hj
    rw [hτc] at hL
    exact ⟨L, hL.comp tendsto_I_mul_punctured⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechPlusKernel_S_right τ hj
    rw [hτc] at hL
    have hpow : Tendsto (fun t : ℝ => -((t : ℂ) ^ 10)) (𝓝[≠] β⁻¹) (𝓝 (-((β⁻¹ : ℝ) : ℂ) ^ 10)) :=
      ((Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds)
    refine ⟨_, ((hL.comp (tendsto_I_mul_inv_punctured hβ)).mul hpow).congr' ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds (inv_pos.mpr hβ)) :
      Ioi (0 : ℝ) ∈ 𝓝[≠] β⁻¹)] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    have hS := S_smul_imagPt_inv ht0
    have hp10 := coe_imagPt_inv_pow_ten ht0
    simp only [imagPt] at hS hp10 ⊢
    rw [hS, mul_assoc]
    rw [show ((UpperHalfPlane.ofComplex (I * ((t⁻¹ : ℝ) : ℂ)) : ℍ) : ℂ) ^ 10 * -((t : ℂ) ^ 10) = 1
      from by simpa [neg_mul] using hp10, mul_one]

end E8Leech
