import E8Leech.CKMRVSchwartzProfile

/-!
# The full-radius representation on the imaginary axis (P4d-5f)

Downstream (CKMRV Lemma 6.2) needs the generating functions at `τ = iβ`. There `t ↦ K(iβ, it)`
has the removable singularities `t = β, 1/β` (P4d-2), so it is replaced by its continuous
extension `g` (equal to `K(iβ, i·)` off the two points, hence almost everywhere). The generic
results of `CKMRVLaplaceFull`, `CKMRVLaplaceSmooth`, `CKMRVLaplaceDecay` and
`CKMRVSchwartzProfile` apply to `g` verbatim: near `0` and at `∞` it agrees with the kernel.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ContDiff

/-! ## Continuous extension across two points -/

theorem exists_continuousOn_eq_off_two {f : ℝ → ℂ} {p q : ℝ} (hpq : p ≠ q)
    (hcont : ∀ x : ℝ, 0 < x → x ≠ p → x ≠ q → ContinuousAt f x)
    (hLp : ∃ L, Tendsto f (𝓝[≠] p) (𝓝 L)) (hLq : ∃ L, Tendsto f (𝓝[≠] q) (𝓝 L)) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Ioi 0) ∧ ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x := by
  classical
  obtain ⟨Lp, hfp⟩ := hLp
  obtain ⟨Lq, hfq⟩ := hLq
  set g : ℝ → ℂ := Function.update (Function.update f p Lp) q Lq with hg
  have hgf : ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x := fun x hxp hxq => by
    rw [hg, Function.update_of_ne hxq, Function.update_of_ne hxp]
  refine ⟨g, fun x hx => ContinuousAt.continuousWithinAt ?_, hgf⟩
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

theorem eventuallyEq_zero_of_eq_off_two {f g : ℝ → ℂ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h : ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x) : g =ᶠ[𝓝[>] (0 : ℝ)] f := by
  filter_upwards [Ioo_mem_nhdsGT (lt_min hp hq)] with x hx
  exact h x (ne_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _)))
    (ne_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _)))

theorem eventuallyEq_atTop_of_eq_off_two {f g : ℝ → ℂ} {p q : ℝ}
    (h : ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x) : g =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop (max p q)] with x hx
  exact h x (ne_of_gt (lt_of_le_of_lt (le_max_left _ _) hx))
    (ne_of_gt (lt_of_le_of_lt (le_max_right _ _) hx))

theorem setIntegral_eq_of_eq_off_two {f g w : ℝ → ℂ} {p q : ℝ}
    (h : ∀ x : ℝ, x ≠ p → x ≠ q → g x = f x) :
    ∫ t in Ioi 0, g t * w t = ∫ t in Ioi 0, f t * w t := by
  refine integral_congr_ae ?_
  have hfin : volume ({p, q} : Set ℝ) = 0 := (Set.toFinite {p, q}).measure_zero _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({p, q} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  filter_upwards [ae_restrict_of_ae hae] with x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  rw [h x hx.1 hx.2]

/-! ## `d = 8`, minus kernel -/

/-- The continuous extension of `t ↦ K₋⁽⁸⁾(iβ, it)` across `t = β, 1/β`. -/
theorem exists_ckmrvEightMinus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Ioi 0) ∧ ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ →
      g x = ckmrvEightMinusKernel (imagPt β) (imagPt x) := by
  have hj := kleinModularJDerivative_imagPt_ne_zero hβ hβ1
  have hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) :=
    fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine exists_continuousOn_eq_off_two (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
  · intro x hx hxp hxq
    set s : Set ℝ := Ioi 0 ∩ ({β}ᶜ ∩ {β⁻¹}ᶜ)
    have hsopen : IsOpen s := isOpen_Ioi.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)
    have hxs : x ∈ s := ⟨hx, hxp, hxq⟩
    exact (continuousOn_ckmrvEightMinusKernel_imagPt' τ (fun t ht => ht.1)
      (fun t ht => hpole t ht.1 ht.2.1 ht.2.2)).continuousAt (hsopen.mem_nhds hxs)
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightMinusKernel_right τ hj
    rw [hτc] at hL
    exact ⟨L, hL.comp tendsto_I_mul_punctured⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightMinusKernel_S_right τ hj
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

theorem isBigO_eightMinusAxis_zero {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t) :=
  (isBigO_ckmrvEightMinusKernel_imagPt_zero_exp (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_eightMinusAxis_zero_one {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
  (isBigO_ckmrvEightMinusKernel_imagPt_zero (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_eightMinusAxis_atTop {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x)) :
    g =O[atTop] fun t => t * Real.exp (0 * t) :=
  (isBigO_ckmrvEightMinusKernel_imagPt_atTop (imagPt β)).congr'
    (eventuallyEq_atTop_of_eq_off_two hgK).symm EventuallyEq.rfl

theorem isBigO_eightMinusAxis_sub_G {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x)) :
    (fun t => g t - cuspProfile 0 0 (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 (imagPt β))
      (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 (imagPt β) * (4 * Real.log 2) +
        eightMinusTauCoeff 1 (imagPt β) + eightMinusTauCoeff 2 (imagPt β))) 0 t)
      =O[atTop] fun t => t * Real.exp (-π * t) := by
  refine (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvEightMinusG_imagPt _ ht)
    (isBigO_comp_imagPt (w := fun x => x) (c := -π)
      (isBigO_ckmrvEightMinusKernel_sub_G (imagPt β)))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventuallyEq_atTop_of_eq_off_two hgK] with t ht
  rw [ht]

/-- **(5.3) on the axis, `d = 8`, minus kernel.** -/
theorem integral_ckmrvEightMinusKernel_axis_eq {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x))
    {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi 0, ckmrvEightMinusKernel (imagPt β) (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (g t - cuspProfile 0 0
        (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 (imagPt β))
        (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 (imagPt β) * (4 * Real.log 2) +
          eightMinusTauCoeff 1 (imagPt β) + eightMinusTauCoeff 2 (imagPt β))) 0 t) *
            (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace 0 0 (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 (imagPt β))
        (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 (imagPt β) * (4 * Real.log 2) +
          eightMinusTauCoeff 1 (imagPt β) + eightMinusTauCoeff 2 (imagPt β))) 0 b := by
  rw [← setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
  exact integral_eq_sub_cuspProfile hg (isBigO_eightMinusAxis_zero_one hβ hgK)
    (isBigO_eightMinusAxis_sub_G hgK) (by linarith [Real.pi_pos]) le_rfl hb

/-- **On the axis the subtracted transform is `C^∞` in `b > −π`.** -/
theorem contDiffOn_eightMinusAxis_sub_G_laplace {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x)) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile 0 0
      (π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 (imagPt β))
      (-ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 (imagPt β) * (4 * Real.log 2) +
        eightMinusTauCoeff 1 (imagPt β) + eightMinusTauCoeff 2 (imagPt β))) 0 t) *
          (Real.exp (-b * t) : ℂ)) (Ioi (-π)) :=
  contDiffOn_laplace (hg.sub (continuous_cuspProfile _ _ _ _ 0).continuousOn)
    ((isBigO_eightMinusAxis_zero_one hβ hgK).sub
      (((continuous_cuspProfile _ _ _ _ 0).tendsto 0).mono_left nhdsWithin_le_nhds
        |>.isBigO_one ℝ))
    (isBigO_eightMinusAxis_sub_G hgK)

/-- **On the axis every derivative of the kernel transform decays rapidly.** -/
theorem exists_bound_eightMinusAxis_decay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x)) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖laplaceFamily g n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay hg (isBigO_eightMinusAxis_zero hβ hgK)
    (isBigO_eightMinusAxis_atTop hgK) n k

theorem exists_bound_eightMinusAxis_cdecay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightMinusKernel (imagPt β) (imagPt x))
    {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ ≤ 1) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖claplaceFamily g c n s‖ ≤ C :=
  exists_bound_claplaceFamily_decay hg (isBigO_eightMinusAxis_zero hβ hgK)
    (isBigO_eightMinusAxis_atTop hgK) hc hc1 n k


/-! ## `d = 8`, plus kernel -/

/-- The continuous extension of `t ↦ K₊⁽⁸⁾(iβ, it)` across `t = β, 1/β`. -/
theorem exists_ckmrvEightPlus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Ioi 0) ∧ ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ →
      g x = ckmrvEightPlusKernel (imagPt β) (imagPt x) := by
  have hj := kleinModularJDerivative_imagPt_ne_zero hβ hβ1
  have hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) :=
    fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine exists_continuousOn_eq_off_two (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
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

theorem isBigO_eightPlusAxis_zero {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t) :=
  (isBigO_ckmrvEightPlusKernel_imagPt_zero_exp (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_eightPlusAxis_zero_one {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
  (isBigO_ckmrvEightPlusKernel_imagPt_zero (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_eightPlusAxis_atTop {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x)) :
    g =O[atTop] fun t => t * Real.exp (0 * t) :=
  (isBigO_ckmrvEightPlusKernel_imagPt_atTop (imagPt β)).congr'
    (eventuallyEq_atTop_of_eq_off_two hgK).symm EventuallyEq.rfl

theorem isBigO_eightPlusAxis_sub_G {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x)) :
    (fun t => g t - cuspProfile 0 0
        (-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ * (ckmrvPhiBasis (imagPt β) 0 * ModularForm.E₆ (imagPt β) -
          ckmrvPhiBasis (imagPt β) 1 * ModularForm.E₄ (imagPt β)))
        (ckmrvPlusScale⁻¹ * (36 / (π : ℂ) ^ 2 * (ckmrvPhiBasis (imagPt β) 0 *
          ModularForm.E₆ (imagPt β)))) 0 t)
      =O[atTop] fun t => t * Real.exp (-π * t) := by
  refine (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvEightPlusG_imagPt _ ht)
    (isBigO_mul_exp_neg_pi_sq (isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -2 * π)
      (isBigO_ckmrvEightPlusKernel_sub_G (imagPt β))))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventuallyEq_atTop_of_eq_off_two hgK] with t ht
  rw [ht]

/-- **(5.3) on the axis, `d = 8`, plus kernel.** -/
theorem integral_ckmrvEightPlusKernel_axis_eq {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x))
    {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi 0, ckmrvEightPlusKernel (imagPt β) (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (g t - cuspProfile 0 0
        (-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ * (ckmrvPhiBasis (imagPt β) 0 * ModularForm.E₆ (imagPt β) -
          ckmrvPhiBasis (imagPt β) 1 * ModularForm.E₄ (imagPt β)))
        (ckmrvPlusScale⁻¹ * (36 / (π : ℂ) ^ 2 * (ckmrvPhiBasis (imagPt β) 0 *
          ModularForm.E₆ (imagPt β)))) 0 t) *
            (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace 0 0
        (-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ * (ckmrvPhiBasis (imagPt β) 0 * ModularForm.E₆ (imagPt β) -
          ckmrvPhiBasis (imagPt β) 1 * ModularForm.E₄ (imagPt β)))
        (ckmrvPlusScale⁻¹ * (36 / (π : ℂ) ^ 2 * (ckmrvPhiBasis (imagPt β) 0 *
          ModularForm.E₆ (imagPt β)))) 0 b := by
  rw [← setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
  exact integral_eq_sub_cuspProfile hg (isBigO_eightPlusAxis_zero_one hβ hgK)
    (isBigO_eightPlusAxis_sub_G hgK) (by linarith [Real.pi_pos]) le_rfl hb

/-- **On the axis the subtracted transform is `C^∞` in `b > −π`.** -/
theorem contDiffOn_eightPlusAxis_sub_G_laplace {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x)) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile 0 0
        (-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ * (ckmrvPhiBasis (imagPt β) 0 * ModularForm.E₆ (imagPt β) -
          ckmrvPhiBasis (imagPt β) 1 * ModularForm.E₄ (imagPt β)))
        (ckmrvPlusScale⁻¹ * (36 / (π : ℂ) ^ 2 * (ckmrvPhiBasis (imagPt β) 0 *
          ModularForm.E₆ (imagPt β)))) 0 t) *
          (Real.exp (-b * t) : ℂ)) (Ioi (-π)) :=
  contDiffOn_laplace (hg.sub (continuous_cuspProfile _ _ _ _ 0).continuousOn)
    ((isBigO_eightPlusAxis_zero_one hβ hgK).sub
      (((continuous_cuspProfile _ _ _ _ 0).tendsto 0).mono_left nhdsWithin_le_nhds
        |>.isBigO_one ℝ))
    (isBigO_eightPlusAxis_sub_G hgK)

/-- **On the axis every derivative of the kernel transform decays rapidly.** -/
theorem exists_bound_eightPlusAxis_decay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x)) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖laplaceFamily g n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay hg (isBigO_eightPlusAxis_zero hβ hgK)
    (isBigO_eightPlusAxis_atTop hgK) n k

theorem exists_bound_eightPlusAxis_cdecay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvEightPlusKernel (imagPt β) (imagPt x))
    {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ ≤ 1) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖claplaceFamily g c n s‖ ≤ C :=
  exists_bound_claplaceFamily_decay hg (isBigO_eightPlusAxis_zero hβ hgK)
    (isBigO_eightPlusAxis_atTop hgK) hc hc1 n k


/-! ## The Leech lattice, minus kernel -/

/-- The continuous extension of `t ↦ K₋⁽²⁴⁾(iβ, it)` across `t = β, 1/β`. -/
theorem exists_ckmrvLeechMinus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Ioi 0) ∧ ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ →
      g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x) := by
  have hj := kleinModularJDerivative_imagPt_ne_zero hβ hβ1
  have hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) :=
    fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine exists_continuousOn_eq_off_two (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
  · intro x hx hxp hxq
    set s : Set ℝ := Ioi 0 ∩ ({β}ᶜ ∩ {β⁻¹}ᶜ)
    have hsopen : IsOpen s := isOpen_Ioi.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)
    have hxs : x ∈ s := ⟨hx, hxp, hxq⟩
    exact (continuousOn_ckmrvLeechMinusKernel_imagPt' τ (fun t ht => ht.1)
      (fun t ht => hpole t ht.1 ht.2.1 ht.2.2)).continuousAt (hsopen.mem_nhds hxs)
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechMinusKernel_right τ hj
    rw [hτc] at hL
    exact ⟨L, hL.comp tendsto_I_mul_punctured⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechMinusKernel_S_right τ hj
    rw [hτc] at hL
    have hsq : Tendsto (fun t : ℝ => -((t : ℂ) ^ 10)) (𝓝[≠] β⁻¹) (𝓝 (-((β⁻¹ : ℝ) : ℂ) ^ 10)) :=
      ((Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds)
    refine ⟨_, ((hL.comp (tendsto_I_mul_inv_punctured hβ)).mul hsq).congr' ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds (inv_pos.mpr hβ)) :
      Ioi (0 : ℝ) ∈ 𝓝[≠] β⁻¹)] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    have hS := S_smul_imagPt_inv ht0
    have hsq1 := coe_imagPt_inv_pow_ten ht0
    simp only [imagPt] at hS hsq1 ⊢
    rw [hS, mul_assoc]
    rw [show ((UpperHalfPlane.ofComplex (I * ((t⁻¹ : ℝ) : ℂ)) : ℍ) : ℂ) ^ 10 * -((t : ℂ) ^ 10) = 1
      from by simpa [neg_mul] using hsq1, mul_one]

theorem isBigO_leechMinusAxis_zero {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t) :=
  (isBigO_ckmrvLeechMinusKernel_imagPt_zero_exp (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_leechMinusAxis_zero_one {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
  (isBigO_ckmrvLeechMinusKernel_imagPt_zero (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_leechMinusAxis_atTop {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x)) :
    g =O[atTop] fun t => t * Real.exp (2 * π * t) :=
  (isBigO_ckmrvLeechMinusKernel_imagPt_atTop (imagPt β)).congr'
    (eventuallyEq_atTop_of_eq_off_two hgK).symm EventuallyEq.rfl

theorem isBigO_leechMinusAxis_sub_G {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x)) :
    (fun t => g t - cuspProfile (ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant (imagPt β))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant (imagPt β)) +
          (leechMinusBeta (imagPt β) + leechMinusAlpha (imagPt β))))
        (ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β)))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β))) +
          ((-leechMinusBeta (imagPt β) - leechMinusAlpha (imagPt β)) *
            (696 - kleinModularJ (imagPt β)) - leechMinusNZeroC (imagPt β)))) (2 * π) t)
      =O[atTop] fun t => t * Real.exp (-π * t) := by
  refine (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvLeechMinusG_imagPt _ ht)
    (isBigO_comp_imagPt (w := fun x => x) (c := -π)
      (isBigO_ckmrvLeechMinusKernel_sub_G (imagPt β)))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventuallyEq_atTop_of_eq_off_two hgK] with t ht
  rw [ht]

/-- **(5.4) on the axis, Leech minus kernel.** -/
theorem integral_ckmrvLeechMinusKernel_axis_eq {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x))
    {b : ℝ} (hb : 2 * π < b) :
    ∫ t in Ioi 0, ckmrvLeechMinusKernel (imagPt β) (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (g t - cuspProfile (ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant (imagPt β))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant (imagPt β)) +
          (leechMinusBeta (imagPt β) + leechMinusAlpha (imagPt β))))
        (ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β)))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β))) +
          ((-leechMinusBeta (imagPt β) - leechMinusAlpha (imagPt β)) *
            (696 - kleinModularJ (imagPt β)) - leechMinusNZeroC (imagPt β)))) (2 * π) t) *
            (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace (ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant (imagPt β))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant (imagPt β)) +
          (leechMinusBeta (imagPt β) + leechMinusAlpha (imagPt β))))
        (ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β)))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β))) +
          ((-leechMinusBeta (imagPt β) - leechMinusAlpha (imagPt β)) *
            (696 - kleinModularJ (imagPt β)) - leechMinusNZeroC (imagPt β)))) (2 * π) b := by
  rw [← setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
  exact integral_eq_sub_cuspProfile hg (isBigO_leechMinusAxis_zero_one hβ hgK)
    (isBigO_leechMinusAxis_sub_G hgK) (by linarith [Real.pi_pos]) (by positivity) hb

/-- **On the axis the subtracted transform is `C^∞` in `b > −π`.** -/
theorem contDiffOn_leechMinusAxis_sub_G_laplace {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x)) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile (ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant (imagPt β))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant (imagPt β)) +
          (leechMinusBeta (imagPt β) + leechMinusAlpha (imagPt β))))
        (ckmrvMinusScale⁻¹ * (-π * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β)))))
        (ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
          (720 - kleinModularJ (imagPt β))) +
          ((-leechMinusBeta (imagPt β) - leechMinusAlpha (imagPt β)) *
            (696 - kleinModularJ (imagPt β)) - leechMinusNZeroC (imagPt β)))) (2 * π) t) *
          (Real.exp (-b * t) : ℂ)) (Ioi (-π)) :=
  contDiffOn_laplace (hg.sub (continuous_cuspProfile _ _ _ _ (2 * π)).continuousOn)
    ((isBigO_leechMinusAxis_zero_one hβ hgK).sub
      (((continuous_cuspProfile _ _ _ _ (2 * π)).tendsto 0).mono_left nhdsWithin_le_nhds
        |>.isBigO_one ℝ))
    (isBigO_leechMinusAxis_sub_G hgK)

/-- **On the axis every derivative of the kernel transform decays rapidly.** -/
theorem exists_bound_leechMinusAxis_decay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x)) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖laplaceFamily g n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay hg (isBigO_leechMinusAxis_zero hβ hgK)
    (isBigO_leechMinusAxis_atTop hgK) n k

theorem exists_bound_leechMinusAxis_cdecay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechMinusKernel (imagPt β) (imagPt x))
    {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ ≤ 1) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖claplaceFamily g c n s‖ ≤ C :=
  exists_bound_claplaceFamily_decay hg (isBigO_leechMinusAxis_zero hβ hgK)
    (isBigO_leechMinusAxis_atTop hgK) hc hc1 n k


/-! ## The Leech lattice, plus kernel -/

/-- The continuous extension of `t ↦ K₊⁽²⁴⁾(iβ, it)` across `t = β, 1/β`. -/
theorem exists_ckmrvLeechPlus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Ioi 0) ∧ ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ →
      g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x) := by
  have hj := kleinModularJDerivative_imagPt_ne_zero hβ hβ1
  have hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) :=
    fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine exists_continuousOn_eq_off_two (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
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
    have hsq : Tendsto (fun t : ℝ => -((t : ℂ) ^ 10)) (𝓝[≠] β⁻¹) (𝓝 (-((β⁻¹ : ℝ) : ℂ) ^ 10)) :=
      ((Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds)
    refine ⟨_, ((hL.comp (tendsto_I_mul_inv_punctured hβ)).mul hsq).congr' ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds (inv_pos.mpr hβ)) :
      Ioi (0 : ℝ) ∈ 𝓝[≠] β⁻¹)] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    have hS := S_smul_imagPt_inv ht0
    have hsq1 := coe_imagPt_inv_pow_ten ht0
    simp only [imagPt] at hS hsq1 ⊢
    rw [hS, mul_assoc]
    rw [show ((UpperHalfPlane.ofComplex (I * ((t⁻¹ : ℝ) : ℂ)) : ℍ) : ℂ) ^ 10 * -((t : ℂ) ^ 10) = 1
      from by simpa [neg_mul] using hsq1, mul_one]

theorem isBigO_leechPlusAxis_zero {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t) :=
  (isBigO_ckmrvLeechPlusKernel_imagPt_zero_exp (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_leechPlusAxis_zero_one {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x)) :
    g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
  (isBigO_ckmrvLeechPlusKernel_imagPt_zero (imagPt β)).congr'
    (eventuallyEq_zero_of_eq_off_two hβ (inv_pos.mpr hβ) hgK).symm EventuallyEq.rfl

theorem isBigO_leechPlusAxis_atTop {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x)) :
    g =O[atTop] fun t => t * Real.exp (2 * π * t) :=
  (isBigO_ckmrvLeechPlusKernel_imagPt_atTop (imagPt β)).congr'
    (eventuallyEq_atTop_of_eq_off_two hgK).symm EventuallyEq.rfl

theorem isBigO_leechPlusAxis_sub_G {β : ℝ} {g : ℝ → ℂ}
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x)) :
    (fun t => g t - cuspProfile ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt β))
        ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c (imagPt β)) (2 * π) t)
      =O[atTop] fun t => t * Real.exp ((-π + π / 4) * t) := by
  refine (isBigO_sub_cuspProfile_of_eventuallyEq (fun t ht => ckmrvLeechPlusG_imagPt _ ht)
    ((isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -π)
      (isBigO_ckmrvLeechPlusKernel_sub_G (imagPt β))).trans
      (isBigO_sq_mul_exp_shift (c := -π) (ε := π / 4) (by positivity)))).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventuallyEq_atTop_of_eq_off_two hgK] with t ht
  rw [ht]

/-- **(5.4) on the axis, Leech plus kernel.** -/
theorem integral_ckmrvLeechPlusKernel_axis_eq {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x))
    {b : ℝ} (hb : 2 * π < b) :
    ∫ t in Ioi 0, ckmrvLeechPlusKernel (imagPt β) (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (g t - cuspProfile ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt β))
        ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c (imagPt β)) (2 * π) t) *
            (Real.exp (-b * t) : ℂ)) +
      cuspProfileLaplace ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt β))
        ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c (imagPt β)) (2 * π) b := by
  rw [← setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
  exact integral_eq_sub_cuspProfile hg (isBigO_leechPlusAxis_zero_one hβ hgK)
    (isBigO_leechPlusAxis_sub_G hgK) (by linarith [Real.pi_pos]) (by positivity) hb

/-- **On the axis the subtracted transform is `C^∞` in `b > −3π/4`.** -/
theorem contDiffOn_leechPlusAxis_sub_G_laplace {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x)) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1a (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt β))
        ((1728 * ckmrvPlusScale)⁻¹ * (Complex.I * leechPlusM1c (imagPt β)))
        ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c (imagPt β)) (2 * π) t) *
          (Real.exp (-b * t) : ℂ)) (Ioi (-π + π / 4)) :=
  contDiffOn_laplace (hg.sub (continuous_cuspProfile _ _ _ _ (2 * π)).continuousOn)
    ((isBigO_leechPlusAxis_zero_one hβ hgK).sub
      (((continuous_cuspProfile _ _ _ _ (2 * π)).tendsto 0).mono_left nhdsWithin_le_nhds
        |>.isBigO_one ℝ))
    (isBigO_leechPlusAxis_sub_G hgK)

/-- **On the axis every derivative of the kernel transform decays rapidly.** -/
theorem exists_bound_leechPlusAxis_decay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x)) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖laplaceFamily g n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay hg (isBigO_leechPlusAxis_zero hβ hgK)
    (isBigO_leechPlusAxis_atTop hgK) n k

theorem exists_bound_leechPlusAxis_cdecay {β : ℝ} (hβ : 0 < β) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ioi 0))
    (hgK : ∀ x : ℝ, x ≠ β → x ≠ β⁻¹ → g x = ckmrvLeechPlusKernel (imagPt β) (imagPt x))
    {c : ℂ} (hc : c.re = 0) (hc1 : ‖c‖ ≤ 1) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖claplaceFamily g c n s‖ ≤ C :=
  exists_bound_claplaceFamily_decay hg (isBigO_leechPlusAxis_zero hβ hgK)
    (isBigO_leechPlusAxis_atTop hgK) hc hc1 n k


end E8Leech
