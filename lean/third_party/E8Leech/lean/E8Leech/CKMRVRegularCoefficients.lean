import E8Leech.CKMRVHolomorphic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual coefficient quotients and uniform compact bounds

The published formulas are the already checked polynomial numerator divided
by H (dimension eight) or Delta(z) H (dimension twenty-four), with exact
scalar prefactors. On the open regular locus the quotients are jointly
holomorphic and continuous. A finite product norm supplies one positive
bound for all 36 entries on each compact subset of that locus.

These are qualitative compact bounds for actual coefficient matrices. They
are not explicit cusp or tail bounds, coefficient-sign certificates, pole
order/residue statements, or analytic phi/psi kernel identification.
-/

set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 3

noncomputable section
namespace E8Leech
open Set
open scoped Manifold Matrix

def ckmrvLeechPolynomialDenominator (τ z : UpperHalfPlane) : ℂ :=
  ModularForm.discriminant z * ckmrvKleinCrossDifference τ z

theorem ckmrvLeechPolynomialDenominator_eq (τ z : UpperHalfPlane) :
    ckmrvLeechPolynomialDenominator τ z =
      ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 *
        (kleinModularJ τ - kleinModularJ z) := by
  unfold ckmrvLeechPolynomialDenominator
  rw [ckmrvKleinCrossDifference_eq]
  ring

theorem ckmrvLeechPolynomialDenominator_ne_zero_iff (τ z : UpperHalfPlane) :
    ckmrvLeechPolynomialDenominator τ z ≠ 0 ↔ (τ, z) ∈ ckmrvRegularLocus := by
  simp only [ckmrvLeechPolynomialDenominator, ne_eq, mul_eq_zero,
    ModularForm.discriminant_ne_zero, false_or]
  exact ckmrvKleinCrossDifference_ne_zero_iff τ z

theorem mdifferentiable_ckmrvLeechPolynomialDenominator :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvLeechPolynomialDenominator p.1 p.2) :=
  (mdifferentiable_modularDiscriminant.comp mdifferentiable_snd).mul
    mdifferentiable_ckmrvKleinCrossDifference

theorem ckmrvEightPlusCoefficientMatrix_quotient (τ z : UpperHalfPlane)
    (hg : (τ, z) ∈ ckmrvRegularLocus) (i j : Fin 3) :
    ckmrvEightPlusCoefficientMatrix τ z i j =
      (ckmrvPlusScale⁻¹ * ckmrvEightPlusPolynomialNumerator τ z i j) / ckmrvKleinCrossDifference τ z := by
  have hn := (ckmrvKleinCrossDifference_ne_zero_iff τ z).mpr hg
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j)
    (ckmrvEightPlusCoefficientMatrix_polynomial τ z hg)
  change (ModularForm.discriminant τ * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z)) * ckmrvEightPlusCoefficientMatrix τ z i j =
    ckmrvPlusScale⁻¹ * ckmrvEightPlusPolynomialNumerator τ z i j at h
  rw [← ckmrvKleinCrossDifference_eq] at h
  exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using h)

theorem mdifferentiableOn_ckmrvEightPlusCoefficientMatrix_entry (i j : Fin 3) :
    MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightPlusCoefficientMatrix p.1 p.2 i j) := by
  have hf : MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      (ckmrvPlusScale⁻¹ * ckmrvEightPlusPolynomialNumerator p.1 p.2 i j) / ckmrvKleinCrossDifference p.1 p.2) :=
    (mdifferentiable_const.mul (mdifferentiable_ckmrvEightPlusPolynomialNumerator_entry i j)).mdifferentiableOn.div
      mdifferentiable_ckmrvKleinCrossDifference.mdifferentiableOn
      (fun p hp => (ckmrvKleinCrossDifference_ne_zero_iff p.1 p.2).mpr hp)
  exact hf.congr (fun p hp => ckmrvEightPlusCoefficientMatrix_quotient p.1 p.2 hp i j)

theorem continuousOn_ckmrvEightPlusCoefficientMatrix_entry (i j : Fin 3) :
    ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightPlusCoefficientMatrix p.1 p.2 i j) ckmrvRegularLocus :=
  (mdifferentiableOn_ckmrvEightPlusCoefficientMatrix_entry i j).continuousOn

theorem ckmrvEightMinusCoefficientMatrix_quotient (τ z : UpperHalfPlane)
    (hg : (τ, z) ∈ ckmrvRegularLocus) (i j : Fin 3) :
    ckmrvEightMinusCoefficientMatrix τ z i j =
      (ckmrvMinusScale⁻¹ * ckmrvEightMinusPolynomialNumerator τ z i j) / ckmrvKleinCrossDifference τ z := by
  have hn := (ckmrvKleinCrossDifference_ne_zero_iff τ z).mpr hg
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j)
    (ckmrvEightMinusCoefficientMatrix_polynomial τ z hg)
  change (ModularForm.discriminant τ * ModularForm.discriminant z * (kleinModularJ τ - kleinModularJ z)) * ckmrvEightMinusCoefficientMatrix τ z i j =
    ckmrvMinusScale⁻¹ * ckmrvEightMinusPolynomialNumerator τ z i j at h
  rw [← ckmrvKleinCrossDifference_eq] at h
  exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using h)

theorem mdifferentiableOn_ckmrvEightMinusCoefficientMatrix_entry (i j : Fin 3) :
    MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightMinusCoefficientMatrix p.1 p.2 i j) := by
  have hf : MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      (ckmrvMinusScale⁻¹ * ckmrvEightMinusPolynomialNumerator p.1 p.2 i j) / ckmrvKleinCrossDifference p.1 p.2) :=
    (mdifferentiable_const.mul (mdifferentiable_ckmrvEightMinusPolynomialNumerator_entry i j)).mdifferentiableOn.div
      mdifferentiable_ckmrvKleinCrossDifference.mdifferentiableOn
      (fun p hp => (ckmrvKleinCrossDifference_ne_zero_iff p.1 p.2).mpr hp)
  exact hf.congr (fun p hp => ckmrvEightMinusCoefficientMatrix_quotient p.1 p.2 hp i j)

theorem continuousOn_ckmrvEightMinusCoefficientMatrix_entry (i j : Fin 3) :
    ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightMinusCoefficientMatrix p.1 p.2 i j) ckmrvRegularLocus :=
  (mdifferentiableOn_ckmrvEightMinusCoefficientMatrix_entry i j).continuousOn

theorem ckmrvLeechPlusCoefficientMatrix_quotient (τ z : UpperHalfPlane)
    (hg : (τ, z) ∈ ckmrvRegularLocus) (i j : Fin 3) :
    ckmrvLeechPlusCoefficientMatrix τ z i j =
      ((1728 * ckmrvPlusScale)⁻¹ * ckmrvLeechPlusPolynomialNumerator τ z i j) / ckmrvLeechPolynomialDenominator τ z := by
  have hn := (ckmrvLeechPolynomialDenominator_ne_zero_iff τ z).mpr hg
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j)
    (ckmrvLeechPlusCoefficientMatrix_polynomial τ z hg)
  change (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 * (kleinModularJ τ - kleinModularJ z)) * ckmrvLeechPlusCoefficientMatrix τ z i j =
    (1728 * ckmrvPlusScale)⁻¹ * ckmrvLeechPlusPolynomialNumerator τ z i j at h
  rw [← ckmrvLeechPolynomialDenominator_eq] at h
  exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using h)

theorem mdifferentiableOn_ckmrvLeechPlusCoefficientMatrix_entry (i j : Fin 3) :
    MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechPlusCoefficientMatrix p.1 p.2 i j) := by
  have hf : MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ((1728 * ckmrvPlusScale)⁻¹ * ckmrvLeechPlusPolynomialNumerator p.1 p.2 i j) / ckmrvLeechPolynomialDenominator p.1 p.2) :=
    (mdifferentiable_const.mul (mdifferentiable_ckmrvLeechPlusPolynomialNumerator_entry i j)).mdifferentiableOn.div
      mdifferentiable_ckmrvLeechPolynomialDenominator.mdifferentiableOn
      (fun p hp => (ckmrvLeechPolynomialDenominator_ne_zero_iff p.1 p.2).mpr hp)
  exact hf.congr (fun p hp => ckmrvLeechPlusCoefficientMatrix_quotient p.1 p.2 hp i j)

theorem continuousOn_ckmrvLeechPlusCoefficientMatrix_entry (i j : Fin 3) :
    ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechPlusCoefficientMatrix p.1 p.2 i j) ckmrvRegularLocus :=
  (mdifferentiableOn_ckmrvLeechPlusCoefficientMatrix_entry i j).continuousOn

theorem ckmrvLeechMinusCoefficientMatrix_quotient (τ z : UpperHalfPlane)
    (hg : (τ, z) ∈ ckmrvRegularLocus) (i j : Fin 3) :
    ckmrvLeechMinusCoefficientMatrix τ z i j =
      (ckmrvMinusScale⁻¹ * ckmrvLeechMinusPolynomialNumerator τ z i j) / ckmrvLeechPolynomialDenominator τ z := by
  have hn := (ckmrvLeechPolynomialDenominator_ne_zero_iff τ z).mpr hg
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j)
    (ckmrvLeechMinusCoefficientMatrix_polynomial τ z hg)
  change (ModularForm.discriminant τ * ModularForm.discriminant z ^ 2 * (kleinModularJ τ - kleinModularJ z)) * ckmrvLeechMinusCoefficientMatrix τ z i j =
    ckmrvMinusScale⁻¹ * ckmrvLeechMinusPolynomialNumerator τ z i j at h
  rw [← ckmrvLeechPolynomialDenominator_eq] at h
  exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using h)

theorem mdifferentiableOn_ckmrvLeechMinusCoefficientMatrix_entry (i j : Fin 3) :
    MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechMinusCoefficientMatrix p.1 p.2 i j) := by
  have hf : MDiff[ckmrvRegularLocus] (fun p : UpperHalfPlane × UpperHalfPlane =>
      (ckmrvMinusScale⁻¹ * ckmrvLeechMinusPolynomialNumerator p.1 p.2 i j) / ckmrvLeechPolynomialDenominator p.1 p.2) :=
    (mdifferentiable_const.mul (mdifferentiable_ckmrvLeechMinusPolynomialNumerator_entry i j)).mdifferentiableOn.div
      mdifferentiable_ckmrvLeechPolynomialDenominator.mdifferentiableOn
      (fun p hp => (ckmrvLeechPolynomialDenominator_ne_zero_iff p.1 p.2).mpr hp)
  exact hf.congr (fun p hp => ckmrvLeechMinusCoefficientMatrix_quotient p.1 p.2 hp i j)

theorem continuousOn_ckmrvLeechMinusCoefficientMatrix_entry (i j : Fin 3) :
    ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechMinusCoefficientMatrix p.1 p.2 i j) ckmrvRegularLocus :=
  (mdifferentiableOn_ckmrvLeechMinusCoefficientMatrix_entry i j).continuousOn

/-- Finite order: E8 plus, E8 minus, Leech plus, Leech minus. -/
def ckmrvCoefficientFamily (k : Fin 4) (τ z : UpperHalfPlane) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![ckmrvEightPlusCoefficientMatrix τ z, ckmrvEightMinusCoefficientMatrix τ z,
    ckmrvLeechPlusCoefficientMatrix τ z, ckmrvLeechMinusCoefficientMatrix τ z] k

theorem continuousOn_ckmrvCoefficientFamily_entry (k : Fin 4) (i j : Fin 3) :
    ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvCoefficientFamily k p.1 p.2 i j) ckmrvRegularLocus := by
  fin_cases k
  · exact continuousOn_ckmrvEightPlusCoefficientMatrix_entry i j
  · exact continuousOn_ckmrvEightMinusCoefficientMatrix_entry i j
  · exact continuousOn_ckmrvLeechPlusCoefficientMatrix_entry i j
  · exact continuousOn_ckmrvLeechMinusCoefficientMatrix_entry i j

theorem exists_uniform_ckmrvCoefficient_entry_bound
    {K : Set (UpperHalfPlane × UpperHalfPlane)} (hK : IsCompact K)
    (hreg : K ⊆ ckmrvRegularLocus) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ k : Fin 4, ∀ i j : Fin 3,
      ‖ckmrvCoefficientFamily k p.1 p.2 i j‖ ≤ C := by
  have hf : ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      fun k : Fin 4 => fun i j : Fin 3 => ckmrvCoefficientFamily k p.1 p.2 i j) K :=
    continuousOn_pi.mpr (fun k => continuousOn_pi.mpr (fun i => continuousOn_pi.mpr
      (fun j => (continuousOn_ckmrvCoefficientFamily_entry k i j).mono hreg)))
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max R 0 + 1, by positivity, ?_⟩
  intro p hp k i j
  have he : ‖ckmrvCoefficientFamily k p.1 p.2 i j‖ ≤
      ‖fun k : Fin 4 => fun i j : Fin 3 => ckmrvCoefficientFamily k p.1 p.2 i j‖ :=
    (norm_le_pi_norm (fun j : Fin 3 => ckmrvCoefficientFamily k p.1 p.2 i j) j).trans
      ((norm_le_pi_norm (fun i j : Fin 3 => ckmrvCoefficientFamily k p.1 p.2 i j) i).trans
        (norm_le_pi_norm (fun k : Fin 4 => fun i j : Fin 3 =>
          ckmrvCoefficientFamily k p.1 p.2 i j) k))
  exact he.trans ((hR p hp).trans ((le_max_left R 0).trans (le_add_of_nonneg_right (by norm_num))))

/-- Actual imaginary-axis parameter pair used by the fixed certified block. -/
def ckmrvImaginaryPair (p : ℝ × ℝ) : UpperHalfPlane × UpperHalfPlane :=
  (UpperHalfPlane.ofComplex (Complex.I * p.1), UpperHalfPlane.ofComplex (Complex.I * p.2))

def ckmrvFixedImaginaryRectangle : Set (UpperHalfPlane × UpperHalfPlane) :=
  ckmrvImaginaryPair '' (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2)

theorem continuousOn_ckmrvImaginaryPair_rectangle :
    ContinuousOn ckmrvImaginaryPair (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => UpperHalfPlane.ofComplex (Complex.I * p.1))
      (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) :=
    UpperHalfPlane.continuousOn_ofComplex_I_mul.comp continuous_fst.continuousOn
      (by intro p hp; exact lt_of_lt_of_le (by norm_num) hp.1.1)
  have hs : ContinuousOn (fun p : ℝ × ℝ => UpperHalfPlane.ofComplex (Complex.I * p.2))
      (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) :=
    UpperHalfPlane.continuousOn_ofComplex_I_mul.comp continuous_snd.continuousOn
      (by intro p hp; exact lt_of_lt_of_le (by norm_num) hp.2.1)
  exact hf.prodMk hs

theorem isCompact_ckmrvFixedImaginaryRectangle : IsCompact ckmrvFixedImaginaryRectangle :=
  (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
    continuousOn_ckmrvImaginaryPair_rectangle

theorem ckmrvFixedImaginaryRectangle_subset_regular :
    ckmrvFixedImaginaryRectangle ⊆ ckmrvRegularLocus := by
  rintro p ⟨⟨y, v⟩, hp, rfl⟩
  change kleinImaginaryJ y - kleinImaginaryJ v ≠ 0
  have hgap := kleinImaginaryJ_rectangle_real_gap hp.1 hp.2
  intro hzero
  rw [hzero] at hgap
  norm_num at hgap

theorem ckmrvFixedImaginaryRectangle_nonempty : ckmrvFixedImaginaryRectangle.Nonempty :=
  ⟨ckmrvImaginaryPair (3, 1), (3, 1), by norm_num, rfl⟩

theorem ckmrvRegularLocus_nonempty : ckmrvRegularLocus.Nonempty :=
  ckmrvFixedImaginaryRectangle_nonempty.mono ckmrvFixedImaginaryRectangle_subset_regular

theorem exists_uniform_ckmrvCoefficient_fixed_rectangle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Icc (3 : ℝ) 4, ∀ v ∈ Icc (1 : ℝ) 2,
      ∀ k : Fin 4, ∀ i j : Fin 3,
      ‖ckmrvCoefficientFamily k (UpperHalfPlane.ofComplex (Complex.I * y))
        (UpperHalfPlane.ofComplex (Complex.I * v)) i j‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_ckmrvCoefficient_entry_bound
    isCompact_ckmrvFixedImaginaryRectangle ckmrvFixedImaginaryRectangle_subset_regular
  refine ⟨C, hC, ?_⟩
  intro y hy v hv k i j
  exact hb (ckmrvImaginaryPair (y, v)) ⟨(y, v), ⟨hy, hv⟩, rfl⟩ k i j

end E8Leech
