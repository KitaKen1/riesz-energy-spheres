import E8Leech.KleinNoncritical

/-!
# Actual coefficient limits at noncritical diagonal points

The coefficient formulas and their polynomial numerators are actual objects.
Their punctured diagonal limits are proved in terms of the actual j derivative,
whenever it is nonzero. Published constants follow only with an explicit
identification of this derivative with the candidate. Phi/psi contractions,
all elliptic points and modular-orbit pole classification remain outside scope.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open Filter
open scoped Topology Manifold Matrix

theorem tendsto_simple_pole_quotient {f g : ℂ → ℂ} {a dg : ℂ}
    (hf : ContinuousAt f a) (hg : HasDerivAt g dg a) (hne : dg ≠ 0) :
    Tendsto (fun w => (w - a) * (f w / (g w - g a)))
      (𝓝[≠] a) (𝓝 (f a / dg)) := by
  have hi := hg.tendsto_slope.inv₀ hne
  have h := (hf.tendsto.mono_left nhdsWithin_le_nhds).mul hi
  apply h.congr'
  filter_upwards [] with w
  rw [slope_def_field, inv_div]
  ring

theorem tendsto_ckmrvEightPlusCoefficientMatrix_diagonal
    (z : UpperHalfPlane) (hne : kleinModularJDerivative z ≠ 0) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ))
      (𝓝 (((ckmrvPlusScale * ModularForm.discriminant z ^ 2 *
        kleinModularJDerivative z)⁻¹ • ckmrvEightPlusPolynomialNumerator z z) i j)) := by
  have hN : ContinuousAt (fun w : ℂ => ckmrvEightPlusPolynomialNumerator
      (UpperHalfPlane.ofComplex w) z i j) (z : ℂ) :=
    (analyticAt_of_upperHalfPlane_mdifferentiable
      ((mdifferentiable_ckmrvEightPlusPolynomialNumerator_entry i j).comp
        (mdifferentiable_id.prodMk mdifferentiable_const)) z).continuousAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    mdifferentiable_modularDiscriminant z).continuousAt
  have hf : ContinuousAt (fun w : ℂ =>
      (ckmrvPlusScale⁻¹ * ckmrvEightPlusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j) /
      (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 1))
      (z : ℂ) :=
    (continuousAt_const.mul hN).div (hD.mul continuousAt_const) (by
      simpa only [UpperHalfPlane.ofComplex_apply] using
        mul_ne_zero (ModularForm.discriminant_ne_zero z)
          (pow_ne_zero 1 (ModularForm.discriminant_ne_zero z)))
  have h := tendsto_simple_pole_quotient hf (hasDerivAt_kleinModularJ z) hne
  have he : (fun w : ℂ => (w - (z : ℂ)) *
      ((ckmrvPlusScale⁻¹ * ckmrvEightPlusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j /
        (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 1)) /
        (kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ z)))
      =ᶠ[𝓝[≠] (z : ℂ)] (fun w => (w - (z : ℂ)) *
        ckmrvEightPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j) := by
    filter_upwards [eventually_kleinModularJ_gap_ne_zero z hne] with w hw
    have hq := ckmrvEightPlusCoefficientMatrix_quotient
      (UpperHalfPlane.ofComplex w) z hw i j
    simp only [ckmrvKleinCrossDifference_eq] at hq
    simpa only [pow_one, div_div] using
      congrArg (fun u : ℂ => (w - (z : ℂ)) * u) hq.symm
  have ht := h.congr' (by simpa only [UpperHalfPlane.ofComplex_apply] using he)
  convert ht using 1
  simp only [UpperHalfPlane.ofComplex_apply, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_inv_rev, pow_succ]
  ring_nf

theorem tendsto_ckmrvEightMinusCoefficientMatrix_diagonal
    (z : UpperHalfPlane) (hne : kleinModularJDerivative z ≠ 0) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ))
      (𝓝 (((ckmrvMinusScale * ModularForm.discriminant z ^ 2 *
        kleinModularJDerivative z)⁻¹ • ckmrvEightMinusPolynomialNumerator z z) i j)) := by
  have hN : ContinuousAt (fun w : ℂ => ckmrvEightMinusPolynomialNumerator
      (UpperHalfPlane.ofComplex w) z i j) (z : ℂ) :=
    (analyticAt_of_upperHalfPlane_mdifferentiable
      ((mdifferentiable_ckmrvEightMinusPolynomialNumerator_entry i j).comp
        (mdifferentiable_id.prodMk mdifferentiable_const)) z).continuousAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    mdifferentiable_modularDiscriminant z).continuousAt
  have hf : ContinuousAt (fun w : ℂ =>
      (ckmrvMinusScale⁻¹ * ckmrvEightMinusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j) /
      (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 1))
      (z : ℂ) :=
    (continuousAt_const.mul hN).div (hD.mul continuousAt_const) (by
      simpa only [UpperHalfPlane.ofComplex_apply] using
        mul_ne_zero (ModularForm.discriminant_ne_zero z)
          (pow_ne_zero 1 (ModularForm.discriminant_ne_zero z)))
  have h := tendsto_simple_pole_quotient hf (hasDerivAt_kleinModularJ z) hne
  have he : (fun w : ℂ => (w - (z : ℂ)) *
      ((ckmrvMinusScale⁻¹ * ckmrvEightMinusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j /
        (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 1)) /
        (kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ z)))
      =ᶠ[𝓝[≠] (z : ℂ)] (fun w => (w - (z : ℂ)) *
        ckmrvEightMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j) := by
    filter_upwards [eventually_kleinModularJ_gap_ne_zero z hne] with w hw
    have hq := ckmrvEightMinusCoefficientMatrix_quotient
      (UpperHalfPlane.ofComplex w) z hw i j
    simp only [ckmrvKleinCrossDifference_eq] at hq
    simpa only [pow_one, div_div] using
      congrArg (fun u : ℂ => (w - (z : ℂ)) * u) hq.symm
  have ht := h.congr' (by simpa only [UpperHalfPlane.ofComplex_apply] using he)
  convert ht using 1
  simp only [UpperHalfPlane.ofComplex_apply, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_inv_rev, pow_succ]
  ring_nf

theorem tendsto_ckmrvLeechPlusCoefficientMatrix_diagonal
    (z : UpperHalfPlane) (hne : kleinModularJDerivative z ≠ 0) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ))
      (𝓝 ((((1728 * ckmrvPlusScale) * ModularForm.discriminant z ^ 3 *
        kleinModularJDerivative z)⁻¹ • ckmrvLeechPlusPolynomialNumerator z z) i j)) := by
  have hN : ContinuousAt (fun w : ℂ => ckmrvLeechPlusPolynomialNumerator
      (UpperHalfPlane.ofComplex w) z i j) (z : ℂ) :=
    (analyticAt_of_upperHalfPlane_mdifferentiable
      ((mdifferentiable_ckmrvLeechPlusPolynomialNumerator_entry i j).comp
        (mdifferentiable_id.prodMk mdifferentiable_const)) z).continuousAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    mdifferentiable_modularDiscriminant z).continuousAt
  have hf : ContinuousAt (fun w : ℂ =>
      ((1728 * ckmrvPlusScale)⁻¹ * ckmrvLeechPlusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j) /
      (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 2))
      (z : ℂ) :=
    (continuousAt_const.mul hN).div (hD.mul continuousAt_const) (by
      simpa only [UpperHalfPlane.ofComplex_apply] using
        mul_ne_zero (ModularForm.discriminant_ne_zero z)
          (pow_ne_zero 2 (ModularForm.discriminant_ne_zero z)))
  have h := tendsto_simple_pole_quotient hf (hasDerivAt_kleinModularJ z) hne
  have he : (fun w : ℂ => (w - (z : ℂ)) *
      (((1728 * ckmrvPlusScale)⁻¹ * ckmrvLeechPlusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j /
        (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 2)) /
        (kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ z)))
      =ᶠ[𝓝[≠] (z : ℂ)] (fun w => (w - (z : ℂ)) *
        ckmrvLeechPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j) := by
    filter_upwards [eventually_kleinModularJ_gap_ne_zero z hne] with w hw
    have hq := ckmrvLeechPlusCoefficientMatrix_quotient
      (UpperHalfPlane.ofComplex w) z hw i j
    simp only [ckmrvLeechPolynomialDenominator_eq] at hq
    simpa only [div_div] using
      congrArg (fun u : ℂ => (w - (z : ℂ)) * u) hq.symm
  have ht := h.congr' (by simpa only [UpperHalfPlane.ofComplex_apply] using he)
  convert ht using 1
  simp only [UpperHalfPlane.ofComplex_apply, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_inv_rev, pow_succ]
  ring_nf

theorem tendsto_ckmrvLeechMinusCoefficientMatrix_diagonal
    (z : UpperHalfPlane) (hne : kleinModularJDerivative z ≠ 0) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ))
      (𝓝 (((ckmrvMinusScale * ModularForm.discriminant z ^ 3 *
        kleinModularJDerivative z)⁻¹ • ckmrvLeechMinusPolynomialNumerator z z) i j)) := by
  have hN : ContinuousAt (fun w : ℂ => ckmrvLeechMinusPolynomialNumerator
      (UpperHalfPlane.ofComplex w) z i j) (z : ℂ) :=
    (analyticAt_of_upperHalfPlane_mdifferentiable
      ((mdifferentiable_ckmrvLeechMinusPolynomialNumerator_entry i j).comp
        (mdifferentiable_id.prodMk mdifferentiable_const)) z).continuousAt
  have hD := (analyticAt_of_upperHalfPlane_mdifferentiable
    mdifferentiable_modularDiscriminant z).continuousAt
  have hf : ContinuousAt (fun w : ℂ =>
      (ckmrvMinusScale⁻¹ * ckmrvLeechMinusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j) /
      (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 2))
      (z : ℂ) :=
    (continuousAt_const.mul hN).div (hD.mul continuousAt_const) (by
      simpa only [UpperHalfPlane.ofComplex_apply] using
        mul_ne_zero (ModularForm.discriminant_ne_zero z)
          (pow_ne_zero 2 (ModularForm.discriminant_ne_zero z)))
  have h := tendsto_simple_pole_quotient hf (hasDerivAt_kleinModularJ z) hne
  have he : (fun w : ℂ => (w - (z : ℂ)) *
      ((ckmrvMinusScale⁻¹ * ckmrvLeechMinusPolynomialNumerator (UpperHalfPlane.ofComplex w) z i j /
        (ModularForm.discriminant (UpperHalfPlane.ofComplex w) * ModularForm.discriminant z ^ 2)) /
        (kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ z)))
      =ᶠ[𝓝[≠] (z : ℂ)] (fun w => (w - (z : ℂ)) *
        ckmrvLeechMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j) := by
    filter_upwards [eventually_kleinModularJ_gap_ne_zero z hne] with w hw
    have hq := ckmrvLeechMinusCoefficientMatrix_quotient
      (UpperHalfPlane.ofComplex w) z hw i j
    simp only [ckmrvLeechPolynomialDenominator_eq] at hq
    simpa only [div_div] using
      congrArg (fun u : ℂ => (w - (z : ℂ)) * u) hq.symm
  have ht := h.congr' (by simpa only [UpperHalfPlane.ofComplex_apply] using he)
  convert ht using 1
  simp only [UpperHalfPlane.ofComplex_apply, Matrix.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_inv_rev, pow_succ]
  ring_nf

theorem tendsto_ckmrvEightPlusCoefficientMatrix_published_residue_of_derivative_identification
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (hid : kleinModularJDerivative z = ckmrvKleinDerivativeCandidate z) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 ((((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) i j)) := by
  have hne : kleinModularJDerivative z ≠ 0 := by
    rw [hid]
    exact ckmrvKleinDerivativeCandidate_ne_zero z hA hB
  simpa only [hid, ckmrvEightPlus_diagonal_normalization z hA hB] using
    tendsto_ckmrvEightPlusCoefficientMatrix_diagonal z hne i j

theorem tendsto_ckmrvEightMinusCoefficientMatrix_published_residue_of_derivative_identification
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (hid : kleinModularJDerivative z = ckmrvKleinDerivativeCandidate z) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvEightMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 (((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) • ckmrvMinusResidueMatrix z) i j)) := by
  have hne : kleinModularJDerivative z ≠ 0 := by
    rw [hid]
    exact ckmrvKleinDerivativeCandidate_ne_zero z hA hB
  simpa only [hid, ckmrvEightMinus_diagonal_normalization z hA hB] using
    tendsto_ckmrvEightMinusCoefficientMatrix_diagonal z hne i j

theorem tendsto_ckmrvLeechPlusCoefficientMatrix_published_residue_of_derivative_identification
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (hid : kleinModularJDerivative z = ckmrvKleinDerivativeCandidate z) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechPlusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 ((((Real.pi : ℂ) / 72) • ckmrvPlusResidueMatrix) i j)) := by
  have hne : kleinModularJDerivative z ≠ 0 := by
    rw [hid]
    exact ckmrvKleinDerivativeCandidate_ne_zero z hA hB
  simpa only [hid, ckmrvLeechPlus_diagonal_normalization z hA hB] using
    tendsto_ckmrvLeechPlusCoefficientMatrix_diagonal z hne i j

theorem tendsto_ckmrvLeechMinusCoefficientMatrix_published_residue_of_derivative_identification
    (z : UpperHalfPlane) (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0)
    (hid : kleinModularJDerivative z = ckmrvKleinDerivativeCandidate z) (i j : Fin 3) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) *
      ckmrvLeechMinusCoefficientMatrix (UpperHalfPlane.ofComplex w) z i j)
      (𝓝[≠] (z : ℂ)) (𝓝 (((Complex.I / (6912 * (Real.pi : ℂ) ^ 2 * ModularForm.discriminant z)) • ckmrvMinusResidueMatrix z) i j)) := by
  have hne : kleinModularJDerivative z ≠ 0 := by
    rw [hid]
    exact ckmrvKleinDerivativeCandidate_ne_zero z hA hB
  simpa only [hid, ckmrvLeechMinus_diagonal_normalization z hA hB] using
    tendsto_ckmrvLeechMinusCoefficientMatrix_diagonal z hne i j

theorem not_continuousAt_of_nonzero_punctured_pole_limit
    {f : ℂ → ℂ} {a r : ℂ} (hr : r ≠ 0)
    (hlim : Tendsto (fun w => (w - a) * f w) (𝓝[≠] a) (𝓝 r)) :
    ¬ ContinuousAt f a := by
  intro hc
  have hzero : Tendsto (fun w => (w - a) * f w) (𝓝[≠] a) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => (w - a) * f w) (𝓝 a) (𝓝 ((a - a) * f a)) :=
      (tendsto_id.sub tendsto_const_nhds).mul hc.tendsto
    simpa only [sub_self, zero_mul] using h.mono_left nhdsWithin_le_nhds
  exact hr (tendsto_nhds_unique hlim hzero)

theorem not_continuousAt_ckmrvEightPlus_diagonal
    (z : UpperHalfPlane) (hne : kleinModularJDerivative z ≠ 0)
    (hA : ModularForm.E₄ z ≠ 0) (hB : ModularForm.E₆ z ≠ 0) :
    ¬ ContinuousAt (fun w : ℂ => ckmrvEightPlusCoefficientMatrix
      (UpperHalfPlane.ofComplex w) z 0 2) (z : ℂ) := by
  apply not_continuousAt_of_nonzero_punctured_pole_limit _
    (tendsto_ckmrvEightPlusCoefficientMatrix_diagonal z hne 0 2)
  change (ckmrvPlusScale * ModularForm.discriminant z ^ 2 * kleinModularJDerivative z)⁻¹ *
    (ModularForm.discriminant z * ModularForm.E₆ z * ModularForm.E₄ z ^ 2) ≠ 0
  exact mul_ne_zero
    (inv_ne_zero (mul_ne_zero (mul_ne_zero ckmrvPlusScale_ne_zero
      (pow_ne_zero 2 (ModularForm.discriminant_ne_zero z))) hne))
    (mul_ne_zero (mul_ne_zero (ModularForm.discriminant_ne_zero z) hB) (pow_ne_zero 2 hA))

theorem exists_actual_ckmrvEightPlus_diagonal_pole :
    ∃ y : ℝ, y ∈ Set.Ioo 1 4 ∧
      ¬ ContinuousAt (fun w : ℂ => ckmrvEightPlusCoefficientMatrix
        (UpperHalfPlane.ofComplex w) (UpperHalfPlane.ofComplex (Complex.I * y)) 0 2)
        ((UpperHalfPlane.ofComplex (Complex.I * y) : UpperHalfPlane) : ℂ) := by
  obtain ⟨y, hy, hj⟩ := exists_imaginary_kleinModularJDerivative_ne_zero
  refine ⟨y, hy, not_continuousAt_ckmrvEightPlus_diagonal _ hj ?_ ?_⟩
  · intro h
    have ha := eisensteinFour_imaginary_re_lower (by linarith only [hy.1] : 0 < y)
    rw [h, Complex.zero_re] at ha
    norm_num at ha
  · intro h
    have hb := eisensteinSix_imaginary_re_pos hy.1
    rw [h, Complex.zero_re] at hb
    exact lt_irrefl 0 hb

end E8Leech
