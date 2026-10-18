import E8Leech.CKMRVKernelUniform

/-!
# Linear growth of `𝒦̂(iq, it)` for `q ∈ [3, 4]`

`𝒦̂(iq, it) ≥ c t` for `t ≥ T`, uniformly in `q ∈ [3, 4]`: the input `hlin` of
`e8_analyticUnitCostInput_of_kernel_bounds`. The cusp part `(G₊ − G₋)/2` has slope
`(πq/6)(E₂E₄ − E₆)(iq) ≥ (πq/6)·700 e^{−2πq}`, and the remainders are uniformly small.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold

/-! ## Bounds on the compact piece `{iq : q ∈ [3, 4]}` of the axis -/

/-- The compact piece of the axis. -/
def axis34 : Set ℍ := imagPt '' Icc (3 : ℝ) 4

theorem exists_bound_axis34 {g : ℍ → ℂ} (hg : Continuous g) :
    ∃ M : ℝ, ∀ τ ∈ axis34, ‖g τ‖ ≤ M := by
  have hc : ContinuousOn (fun q : ℝ => g (imagPt q)) (Icc (3 : ℝ) 4) :=
    (hg.comp_continuousOn continuousOn_ofComplex_I_mul).mono
      fun q hq => lt_of_lt_of_le (by norm_num) hq.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨M, by rintro _ ⟨q, hq, rfl⟩; exact hM q hq⟩

/-! ## The slope of the cusp part -/

theorem ckmrvEightG_slope {q : ℝ} (hq : 0 < q) :
    ((-(12 / (π : ℂ)) * ckmrvPlusScale⁻¹ *
        (ckmrvPhiBasis (imagPt q) 0 * ModularForm.E₆ (imagPt q) -
          ckmrvPhiBasis (imagPt q) 1 * ModularForm.E₄ (imagPt q))) -
      π * ckmrvMinusScale⁻¹ * eightMinusTauCoeff 0 (imagPt q)) / 2 =
      (π * q / 6 : ℂ) * (EisensteinSeries.E2 (imagPt q) * ModularForm.E₄ (imagPt q) -
        ModularForm.E₆ (imagPt q)) := by
  have hp0 : ckmrvPhiBasis (imagPt q) 0 = I * q := by
    show ((imagPt q : ℍ) : ℂ) = _; exact coe_imagPt hq
  have hp1 : ckmrvPhiBasis (imagPt q) 1 =
      I * q * EisensteinSeries.E2 (imagPt q) - 3 * I / (π : ℂ) := by
    show ((imagPt q : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt q) - 3 * I / (Real.pi : ℂ) = _
    rw [coe_imagPt hq]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hp0, hp1, eightMinusTauCoeff_zero, ckmrvPlusScale, ckmrvMinusScale]
  simp only [zpow_neg, zpow_two]
  field_simp
  linear_combination (exp := 1) (0 : ℂ) * Complex.I_sq

theorem axis_E2E4E6_eq {q : ℝ} (hq : 0 < q) :
    EisensteinSeries.E2 (imagPt q) * ModularForm.E₄ (imagPt q) - ModularForm.E₆ (imagPt q) =
      ((eisensteinTwoQ (imaginaryNome q) * eisensteinFourQ (imaginaryNome q) -
        eisensteinSixQ (imaginaryNome q) : ℝ) : ℂ) := by
  have h2 := eisensteinTwo_imaginary_eq_q hq
  have h4 := eisensteinFour_imaginary_eq_q hq
  have h6 := eisensteinSix_imaginary_eq_q hq
  simp only [imagPt]
  rw [h2, h4, h6]
  push_cast
  ring

/-! ## Extracting explicit constants from the uniform asymptotics -/

theorem exists_bound_of_isBigO_prod {K : Set ℍ} {f : ℍ × ℍ → ℂ} {g : ℍ × ℍ → ℝ}
    (h : f =O[𝓟 K ×ˢ atImInfty] g) :
    ∃ C Y : ℝ, ∀ τ ∈ K, ∀ z : ℍ, Y ≤ z.im → ‖f (τ, z)‖ ≤ C * ‖g (τ, z)‖ := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.mp hC
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hpb
  exact ⟨C, Y, fun τ hτ z hz => hall (eventually_principal.mp hpa τ hτ) (hY z hz)⟩

theorem mul_exp_neg_pi_le_one {t : ℝ} (ht : 0 ≤ t) : t * Real.exp (-π * t) ≤ 1 := by
  have h := Real.add_one_le_exp (π * t)
  have hpos := Real.exp_pos (π * t)
  rw [show -π * t = -(π * t) by ring, Real.exp_neg, mul_inv_le_iff₀ hpos, one_mul]
  nlinarith [Real.pi_gt_three]

/-- The constant part of the cusp term of `𝒦̂`. -/
def ckmrvEightHatG0 (τ : ℍ) : ℂ :=
  (ckmrvPlusScale⁻¹ * (36 / (Real.pi : ℂ) ^ 2 * (ckmrvPhiBasis τ 0 * ModularForm.E₆ τ)) -
    -ckmrvMinusScale⁻¹ * (eightMinusTauCoeff 0 τ * (4 * Real.log 2) +
      eightMinusTauCoeff 1 τ + eightMinusTauCoeff 2 τ)) / 2

theorem ckmrvEightG_hat_imagPt {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    (ckmrvEightPlusG (imagPt q) (imagPt t) - ckmrvEightMinusG (imagPt q) (imagPt t)) / 2 =
      (((π * q / 6) * (eisensteinTwoQ (imaginaryNome q) * eisensteinFourQ (imaginaryNome q) -
        eisensteinSixQ (imaginaryNome q)) * t : ℝ) : ℂ) + ckmrvEightHatG0 (imagPt q) := by
  have hs := ckmrvEightG_slope hq
  rw [axis_E2E4E6_eq hq] at hs
  rw [ckmrvEightPlusG_imagPt _ ht, ckmrvEightMinusG_imagPt _ ht, ckmrvEightHatG0]
  simp only [cuspProfile]
  push_cast at hs ⊢
  linear_combination (t : ℂ) * hs

/-- **Linear growth of `𝒦̂(iq, it)` uniformly in `q ∈ [3, 4]`** (the input `hlin`). -/
theorem e8_kernel_linear_growth :
    ∃ c₁ T : ℝ, 0 < c₁ ∧ 1 ≤ T ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ e8DualKernel (q, t) := by
  have hE4 : Continuous (fun τ : ℍ => ModularForm.E₄ τ) :=
    ModularFormClass.continuous ModularForm.E₄
  have hE6 : Continuous (fun τ : ℍ => ModularForm.E₆ τ) :=
    ModularFormClass.continuous ModularForm.E₆
  have hc : ∀ j : Fin 3, Continuous (fun τ : ℍ => eightMinusTauCoeff j τ) := fun j =>
    (mdifferentiable_eightMinusTauCoeff j).continuous
  have hphi : ∀ i : Fin 3, Continuous (fun τ : ℍ => ckmrvPhiBasis τ i) := fun i =>
    (mdifferentiable_ckmrvPhiBasis i).continuous
  have hmf2 : Continuous (fun τ : ℍ => ckmrvModularFactor τ 2) :=
    (mdifferentiable_ckmrvModularFactor 2).continuous
  obtain ⟨Mj, hMj⟩ := exists_bound_axis34 continuous_kleinModularJ
  obtain ⟨M0, hM0⟩ := exists_bound_axis34 (hc 0)
  obtain ⟨M1, hM1⟩ := exists_bound_axis34 (hc 1)
  obtain ⟨M2, hM2⟩ := exists_bound_axis34 (hc 2)
  obtain ⟨Ma, hMa⟩ := exists_bound_axis34 ((hphi 1).mul hE4)
  obtain ⟨Mb, hMb⟩ := exists_bound_axis34 ((hphi 0).mul hE6)
  obtain ⟨MF, hMF⟩ := exists_bound_axis34 ((hphi 2).mul hmf2)
  obtain ⟨Cm, Ym, hm⟩ := exists_bound_of_isBigO_prod
    (isBigO_ckmrvEightMinusKernel_sub_G_unif hMj hM0 hM1 hM2)
  obtain ⟨Cp, Yp, hp⟩ := exists_bound_of_isBigO_prod
    (isBigO_ckmrvEightPlusKernel_sub_G_unif hMj hMa hMb hMF)
  have hG0c : Continuous ckmrvEightHatG0 := by
    unfold ckmrvEightHatG0
    exact ((continuous_const.mul (continuous_const.mul ((hphi 0).mul hE6))).sub
      (continuous_const.mul ((((hc 0).mul continuous_const).add (hc 1)).add (hc 2)))).div_const 2
  obtain ⟨MD, hMD⟩ := exists_bound_axis34 hG0c
  have hπ := Real.pi_pos
  set s₀ := 350 * π * Real.exp (-8 * π) with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  set E := MD + (|Cp| + |Cm|) / 2 with hE
  refine ⟨s₀ / 2, max 1 (max (max Yp Ym) (2 * E / s₀)), by positivity, le_max_left _ _, ?_⟩
  intro q hq t ht
  have hq0 : 0 < q := by linarith [hq.1]
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have htY : max Yp Ym ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htE : 2 * E / s₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hτ : imagPt q ∈ axis34 := ⟨q, hq, rfl⟩
  have him := im_imagPt ht0
  have hnorm := norm_coe_imagPt ht0
  -- the remainders
  have hRm := hm (imagPt q) hτ (imagPt t) (by rw [him]; exact le_trans (le_max_right _ _) htY)
  have hRp := hp (imagPt q) hτ (imagPt t) (by rw [him]; exact le_trans (le_max_left _ _) htY)
  simp only [him, hnorm] at hRm hRp
  have hte := mul_exp_neg_pi_le_one ht0.le
  have hte0 : 0 ≤ t * Real.exp (-π * t) := by positivity
  have hte2 : t ^ 2 * Real.exp (-2 * π * t) ≤ 1 := by
    have : t ^ 2 * Real.exp (-2 * π * t) = (t * Real.exp (-π * t)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact pow_le_one₀ hte0 hte
  have hRm' : ‖ckmrvEightMinusKernel (imagPt q) (imagPt t) -
      ckmrvEightMinusG (imagPt q) (imagPt t)‖ ≤ |Cm| := by
    refine hRm.trans ?_
    rw [Real.norm_of_nonneg hte0]
    calc Cm * (t * Real.exp (-π * t)) ≤ |Cm| * (t * Real.exp (-π * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hte0
      _ ≤ |Cm| * 1 := mul_le_mul_of_nonneg_left hte (abs_nonneg _)
      _ = |Cm| := mul_one _
  have hRp' : ‖ckmrvEightPlusKernel (imagPt q) (imagPt t) -
      ckmrvEightPlusG (imagPt q) (imagPt t)‖ ≤ |Cp| := by
    refine hRp.trans ?_
    have h0 : 0 ≤ t ^ 2 * Real.exp (-2 * π * t) := by positivity
    rw [Real.norm_of_nonneg h0]
    calc Cp * (t ^ 2 * Real.exp (-2 * π * t)) ≤ |Cp| * (t ^ 2 * Real.exp (-2 * π * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cp| * 1 := mul_le_mul_of_nonneg_left hte2 (abs_nonneg _)
      _ = |Cp| := mul_one _
  -- decomposition
  have hdec : ckmrvEightHatKernel (imagPt q) (imagPt t) =
      (ckmrvEightPlusG (imagPt q) (imagPt t) - ckmrvEightMinusG (imagPt q) (imagPt t)) / 2 +
      ((ckmrvEightPlusKernel (imagPt q) (imagPt t) - ckmrvEightPlusG (imagPt q) (imagPt t)) -
        (ckmrvEightMinusKernel (imagPt q) (imagPt t) -
          ckmrvEightMinusG (imagPt q) (imagPt t))) / 2 := by
    simp only [ckmrvEightHatKernel]; ring
  rw [ckmrvEightG_hat_imagPt hq0 ht0] at hdec
  -- the slope
  set X := eisensteinTwoQ (imaginaryNome q) * eisensteinFourQ (imaginaryNome q) -
    eisensteinSixQ (imaginaryNome q) with hX
  have hn0 := (imaginaryNome_pos q).le
  have hnsmall := imaginaryNome_small (show (1 : ℝ) ≤ q by linarith [hq.1])
  have hX700 := eisenstein_two_four_six_lower hn0 hnsmall
  have hnome : Real.exp (-8 * π) ≤ imaginaryNome q := by
    unfold imaginaryNome
    exact Real.exp_le_exp.mpr (by nlinarith [hq.2])
  have hslope : s₀ ≤ π * q / 6 * X := by
    have h1 : 700 * Real.exp (-8 * π) ≤ X := le_trans (by nlinarith) hX700
    have h2 : π / 2 ≤ π * q / 6 := by nlinarith [hq.1]
    calc s₀ = (π / 2) * (700 * Real.exp (-8 * π)) := by rw [hs₀]; ring
      _ ≤ (π * q / 6) * X := mul_le_mul h2 h1 (by positivity) (by positivity)
  -- real parts
  have hD := hMD (imagPt q) hτ
  have hreD : -MD ≤ (ckmrvEightHatG0 (imagPt q)).re :=
    le_trans (neg_le_neg hD) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  set R := ((ckmrvEightPlusKernel (imagPt q) (imagPt t) - ckmrvEightPlusG (imagPt q) (imagPt t)) -
    (ckmrvEightMinusKernel (imagPt q) (imagPt t) - ckmrvEightMinusG (imagPt q) (imagPt t))) / 2
    with hR
  have hRn : ‖R‖ ≤ (|Cp| + |Cm|) / 2 := by
    rw [hR, norm_div, Complex.norm_ofNat]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add hRp' hRm')
  have hreR : -((|Cp| + |Cm|) / 2) ≤ R.re :=
    le_trans (neg_le_neg hRn) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hval : e8DualKernel (q, t) = π * q / 6 * X * t + (ckmrvEightHatG0 (imagPt q)).re + R.re := by
    simp only [e8DualKernel]
    rw [hdec, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  rw [hval]
  have hmain : s₀ * t ≤ π * q / 6 * X * t := mul_le_mul_of_nonneg_right hslope ht0.le
  have hEt : E ≤ s₀ / 2 * t := by
    rw [div_le_iff₀ hs₀pos] at htE
    linarith
  linarith

end E8Leech
