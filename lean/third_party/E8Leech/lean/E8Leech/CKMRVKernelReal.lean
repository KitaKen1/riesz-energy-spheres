import E8Leech.E8CKMRVCertificate
import E8Leech.CKMRVLaplaceAxisClean
import E8Leech.EisensteinSixSigns
import E8Leech.EisensteinProductIdentities
import E8Leech.CKMRVKernelAsymptotics
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# The `d = 8` CKMRV kernels are real on the imaginary axis

For `β, t > 0` the kernels `K±⁽⁸⁾(iβ, it)` are real. Every modular building block is real on the
axis: `E₂, E₄, E₆, E₈, E₁₀, E₁₄, Δ, j, U, V, W, L, L_S`. So `K₋` is a real rational
expression in them. For `K₊` the `τ`-basis `φ(iβ) = i·(real)` and the scale `36π⁻²i` each carry
one factor `i`, and the two cancel.

This discharges the realness hypothesis of the E8 certificate (`E8CKMRVCertificate`). Two
analytic inputs remain: the kernel positivity (6.4)(1) and the Fourier identity (**).
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real FourierTransform

/-! ## The real subfield -/

/-- `ℝ ⊆ ℂ` as a subfield. -/
def realSubfield : Subfield ℂ := Complex.ofRealHom.fieldRange

theorem mem_realSubfield_iff {z : ℂ} : z ∈ realSubfield ↔ z.im = 0 := by
  rw [realSubfield, RingHom.mem_fieldRange]
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro h
    exact ⟨z.re, Complex.ext (by simp) (by simp [h])⟩

theorem ofReal_mem_realSubfield (r : ℝ) : (r : ℂ) ∈ realSubfield :=
  mem_realSubfield_iff.mpr (Complex.ofReal_im r)

theorem ofNat_mem_realSubfield (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℂ) ∈ realSubfield :=
  mem_realSubfield_iff.mpr (by simp)

theorem tsum_mem_realSubfield {α : Type*} {f : α → ℂ} (h : ∀ a, f a ∈ realSubfield) :
    ∑' a, f a ∈ realSubfield := by
  have hf : ∑' a, f a = ∑' a, ((f a).re : ℂ) :=
    tsum_congr fun a => Complex.ext (by simp) (by simp [mem_realSubfield_iff.mp (h a)])
  rw [hf, ← Complex.ofReal_tsum]
  exact ofReal_mem_realSubfield _

theorem I_mul_mul_inv_I (y : ℂ) : I * y * I⁻¹ = y := by
  rw [mul_comm I y, mul_assoc, mul_inv_cancel₀ I_ne_zero, mul_one]

/-! ## Modular building blocks on the axis -/

theorem imagPt_eq_imagAxisPoint {t : ℝ} (ht : 0 < t) : imagPt t = imagAxisPoint t ht :=
  UpperHalfPlane.ext (by rw [coe_imagPt ht]; rfl)

section Atoms

variable {t : ℝ} (ht : 0 < t)
include ht

theorem E4_imagPt_mem : ModularForm.E₄ (imagPt t) ∈ realSubfield :=
  mem_realSubfield_iff.mpr (by unfold imagPt; rw [eisensteinFour_imaginary_eq_q ht, ofReal_im])

theorem E6_imagPt_mem : ModularForm.E₆ (imagPt t) ∈ realSubfield :=
  mem_realSubfield_iff.mpr (by unfold imagPt; rw [eisensteinSix_imaginary_eq_q ht, ofReal_im])

theorem discriminant_imagPt_mem : ModularForm.discriminant (imagPt t) ∈ realSubfield :=
  mem_realSubfield_iff.mpr (by unfold imagPt; rw [discriminant_imaginary_eq_q ht, ofReal_im])

theorem kleinModularJ_imagPt_mem : kleinModularJ (imagPt t) ∈ realSubfield :=
  mem_realSubfield_iff.mpr (kleinImaginaryJ_im ht)

theorem E8_imagPt_mem : ModularForm.E (by norm_num : 3 ≤ 8) (imagPt t) ∈ realSubfield := by
  rw [eisensteinEight_eq_four_sq]
  exact pow_mem (E4_imagPt_mem ht) 2

theorem E10_imagPt_mem : ModularForm.E (by norm_num : 3 ≤ 10) (imagPt t) ∈ realSubfield := by
  rw [eisensteinTen_eq_four_mul_six]
  exact mul_mem (E4_imagPt_mem ht) (E6_imagPt_mem ht)

theorem E14_imagPt_mem : ModularForm.E (by norm_num : 3 ≤ 14) (imagPt t) ∈ realSubfield := by
  rw [eisensteinFourteen_eq_four_sq_mul_six]
  exact mul_mem (pow_mem (E4_imagPt_mem ht) 2) (E6_imagPt_mem ht)

theorem thetaU_imagPt_mem : thetaU (imagPt t) ∈ realSubfield := by
  obtain ⟨u, -, hu⟩ := thetaU_imagAxis_pos ht
  rw [imagPt_eq_imagAxisPoint ht, hu]
  exact ofReal_mem_realSubfield u

theorem thetaV_imagPt_mem : thetaV (imagPt t) ∈ realSubfield := by
  obtain ⟨v, -, hv⟩ := thetaV_imagAxis_pos ht
  rw [imagPt_eq_imagAxisPoint ht, hv]
  exact ofReal_mem_realSubfield v

theorem thetaW_imagPt_mem : thetaW (imagPt t) ∈ realSubfield := by
  obtain ⟨w, -, hw⟩ := thetaW_imagAxis_pos ht
  rw [imagPt_eq_imagAxisPoint ht, hw]
  exact ofReal_mem_realSubfield w

theorem ckmrvL_imagPt_mem : ckmrvL (imagPt t) ∈ realSubfield := by
  rw [imagPt_eq_imagAxisPoint ht, ckmrvL_imagAxis ht]
  exact ofReal_mem_realSubfield _

theorem ckmrvLS_imagPt_mem : ckmrvLS (imagPt t) ∈ realSubfield := by
  rw [imagPt_eq_imagAxisPoint ht, ckmrvLS_imagAxis ht]
  exact ofReal_mem_realSubfield _

/-- `E₂(it) = 1 − 24 Σ σ₁(n) e^{−2πnt}` is real. -/
theorem E2_imagPt_mem : EisensteinSeries.E2 (imagPt t) ∈ realSubfield := by
  have hq : cexp (2 * (Real.pi : ℂ) * I * ((imagPt t : ℍ) : ℂ)) =
      ((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ) := by
    rw [coe_imagPt ht, Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * t) * I_sq
  have hqm : cexp (2 * (Real.pi : ℂ) * I * ((imagPt t : ℍ) : ℂ)) ∈ realSubfield := by
    rw [hq]
    exact ofReal_mem_realSubfield _
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  exact sub_mem (one_mem _) (mul_mem (ofNat_mem_realSubfield 24)
    (tsum_mem_realSubfield fun n => mul_mem (natCast_mem _ _) (pow_mem hqm _)))

theorem ckmrvModularFactor_imagPt_mem (k : Fin 9) :
    ckmrvModularFactor (imagPt t) k ∈ realSubfield := by
  have h4 := E4_imagPt_mem ht
  have h6 := E6_imagPt_mem ht
  have h8 := E8_imagPt_mem ht
  have h10 := E10_imagPt_mem ht
  have h14 := E14_imagPt_mem ht
  have hΔ := discriminant_imagPt_mem ht
  fin_cases k
  · exact div_mem h10 hΔ
  · exact one_mem _
  · exact div_mem h14 hΔ
  · exact h4
  · exact h6
  · exact h8
  · exact h10
  · exact hΔ
  · exact h14

theorem ckmrvPsiBasis_imagPt_mem (i : Fin 3) : ckmrvPsiBasis (imagPt t) i ∈ realSubfield := by
  have hU := thetaU_imagPt_mem ht
  have hV := thetaV_imagPt_mem ht
  have hW := thetaW_imagPt_mem ht
  have hL := ckmrvL_imagPt_mem ht
  have hLS := ckmrvLS_imagPt_mem ht
  fin_cases i
  · exact one_mem _
  · show ckmrvXiTwo (imagPt t) * ckmrvL (imagPt t) +
      ckmrvXiTwoS (imagPt t) * ckmrvLS (imagPt t) ∈ realSubfield
    unfold ckmrvXiTwo ckmrvXiTwoS
    exact add_mem (mul_mem (add_mem hU hW) hL) (mul_mem (neg_mem (add_mem hU hV)) hLS)
  · show ckmrvXiFour (imagPt t) * ckmrvL (imagPt t) +
      ckmrvXiFourS (imagPt t) * ckmrvLS (imagPt t) ∈ realSubfield
    unfold ckmrvXiFour ckmrvXiFourS
    refine add_mem (mul_mem ?_ hL) (mul_mem ?_ hLS)
    · exact sub_mem (add_mem (pow_mem hU 2) (pow_mem hW 2))
        (mul_mem (ofNat_mem_realSubfield 2) (pow_mem hV 2))
    · exact sub_mem (add_mem (pow_mem hU 2) (pow_mem hV 2))
        (mul_mem (ofNat_mem_realSubfield 2) (pow_mem hW 2))

/-- `φ(it) = i · (real)`. -/
theorem ckmrvPhiBasis_imagPt_mul_inv_I_mem (i : Fin 3) :
    ckmrvPhiBasis (imagPt t) i * I⁻¹ ∈ realSubfield := by
  have hE2 := E2_imagPt_mem ht
  have hπ := ofReal_mem_realSubfield Real.pi
  have ht' := ofReal_mem_realSubfield t
  fin_cases i
  · show ((imagPt t : ℍ) : ℂ) * I⁻¹ ∈ realSubfield
    rw [coe_imagPt ht, I_mul_mul_inv_I]
    exact ht'
  · show (((imagPt t : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt t) - 3 * I / (Real.pi : ℂ)) * I⁻¹ ∈
      realSubfield
    rw [coe_imagPt ht, show I * (t : ℂ) * EisensteinSeries.E2 (imagPt t) - 3 * I / (Real.pi : ℂ) =
      I * ((t : ℂ) * EisensteinSeries.E2 (imagPt t) - 3 / (Real.pi : ℂ)) by ring, I_mul_mul_inv_I]
    exact sub_mem (mul_mem ht' hE2) (div_mem (ofNat_mem_realSubfield 3) hπ)
  · show (((imagPt t : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt t) ^ 2 -
      6 * I / (Real.pi : ℂ) * EisensteinSeries.E2 (imagPt t)) * I⁻¹ ∈ realSubfield
    rw [coe_imagPt ht, show I * (t : ℂ) * EisensteinSeries.E2 (imagPt t) ^ 2 -
      6 * I / (Real.pi : ℂ) * EisensteinSeries.E2 (imagPt t) =
      I * ((t : ℂ) * EisensteinSeries.E2 (imagPt t) ^ 2 -
        6 / (Real.pi : ℂ) * EisensteinSeries.E2 (imagPt t)) by ring, I_mul_mul_inv_I]
    exact sub_mem (mul_mem ht' (pow_mem hE2 2))
      (mul_mem (div_mem (ofNat_mem_realSubfield 6) hπ) hE2)

/-- `φ̃(it)` is real. -/
theorem ckmrvTildePhiBasis_imagPt_mem (j : Fin 3) :
    ckmrvTildePhiBasis (imagPt t) j ∈ realSubfield := by
  have hE2 := E2_imagPt_mem ht
  have hπ := ofReal_mem_realSubfield Real.pi
  have ht' := ofReal_mem_realSubfield t
  fin_cases j
  · show ((imagPt t : ℍ) : ℂ) ^ 2 ∈ realSubfield
    rw [coe_imagPt ht, show (I * (t : ℂ)) ^ 2 = -((t : ℂ) ^ 2) by
      linear_combination (t : ℂ) ^ 2 * I_sq]
    exact neg_mem (pow_mem ht' 2)
  · show ((imagPt t : ℍ) : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) -
      6 * I / (Real.pi : ℂ) * ((imagPt t : ℍ) : ℂ) ∈ realSubfield
    rw [coe_imagPt ht, show (I * (t : ℂ)) ^ 2 * EisensteinSeries.E2 (imagPt t) -
      6 * I / (Real.pi : ℂ) * (I * (t : ℂ)) =
      -((t : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t)) + 6 * (t : ℂ) / (Real.pi : ℂ) by
      linear_combination ((t : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) -
        6 * (t : ℂ) / (Real.pi : ℂ)) * I_sq]
    exact add_mem (neg_mem (mul_mem (pow_mem ht' 2) hE2))
      (div_mem (mul_mem (ofNat_mem_realSubfield 6) ht') hπ)
  · show ((imagPt t : ℍ) : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) ^ 2 -
      12 * I / (Real.pi : ℂ) * ((imagPt t : ℍ) : ℂ) * EisensteinSeries.E2 (imagPt t) -
        36 / (Real.pi : ℂ) ^ 2 ∈ realSubfield
    rw [coe_imagPt ht, show (I * (t : ℂ)) ^ 2 * EisensteinSeries.E2 (imagPt t) ^ 2 -
      12 * I / (Real.pi : ℂ) * (I * (t : ℂ)) * EisensteinSeries.E2 (imagPt t) -
        36 / (Real.pi : ℂ) ^ 2 =
      -((t : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) ^ 2) +
        12 * (t : ℂ) * EisensteinSeries.E2 (imagPt t) / (Real.pi : ℂ) -
          36 / (Real.pi : ℂ) ^ 2 by
      linear_combination ((t : ℂ) ^ 2 * EisensteinSeries.E2 (imagPt t) ^ 2 -
        12 * (t : ℂ) * EisensteinSeries.E2 (imagPt t) / (Real.pi : ℂ)) * I_sq]
    exact sub_mem (add_mem (neg_mem (mul_mem (pow_mem ht' 2) (pow_mem hE2 2)))
      (div_mem (mul_mem (mul_mem (ofNat_mem_realSubfield 12) ht') hE2) hπ))
      (div_mem (ofNat_mem_realSubfield 36) (pow_mem hπ 2))

end Atoms

/-! ## The kernels -/

theorem ckmrvEightMinusCore_mem {J : ℂ} (hJ : J ∈ realSubfield) (i j : Fin 3) :
    ckmrvEightMinusCore J i j ∈ realSubfield := by
  fin_cases i <;> fin_cases j <;>
    simp [ckmrvEightMinusCore, zero_mem, one_mem, hJ, sub_mem, mul_mem]

theorem ckmrvEightPlusCore_mem {g : ℂ} (hg : g ∈ realSubfield) (i j : Fin 3) :
    ckmrvEightPlusCore g i j ∈ realSubfield := by
  fin_cases i <;> fin_cases j <;>
    simp [ckmrvEightPlusCore, zero_mem, one_mem, hg, mul_mem]

theorem eightMinusTauCoeff_imagPt_mem {β : ℝ} (hβ : 0 < β) (j : Fin 3) :
    eightMinusTauCoeff j (imagPt β) ∈ realSubfield := by
  unfold eightMinusTauCoeff
  exact sum_mem fun i _ => mul_mem (mul_mem (ckmrvPsiBasis_imagPt_mem hβ i)
    (ckmrvModularFactor_imagPt_mem hβ _))
    (ckmrvEightMinusCore_mem (kleinModularJ_imagPt_mem hβ) i j)

/-- **`K₋⁽⁸⁾(iβ, it)` is real.** -/
theorem ckmrvEightMinusKernel_imagPt_mem {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    ckmrvEightMinusKernel (imagPt β) (imagPt t) ∈ realSubfield := by
  rw [ckmrvEightMinusKernel_eq_z, eightMinusDenZ]
  have hc : ckmrvMinusScale ∈ realSubfield := by
    unfold ckmrvMinusScale
    exact mul_mem (mul_mem (ofNat_mem_realSubfield 2) (ofNat_mem_realSubfield 1728))
      (ofReal_mem_realSubfield _)
  have h4 := E4_imagPt_mem ht
  have h6 := E6_imagPt_mem ht
  have hΔ := discriminant_imagPt_mem ht
  refine mul_mem (mul_mem (inv_mem hc) (inv_mem (sub_mem (mul_mem hΔ
    (kleinModularJ_imagPt_mem hβ)) (pow_mem h4 3)))) ?_
  refine add_mem (add_mem ?_ ?_) ?_
  · exact mul_mem (eightMinusTauCoeff_imagPt_mem hβ 0)
      (mul_mem (mul_mem h4 h6) (ckmrvL_imagPt_mem ht))
  · exact mul_mem (eightMinusTauCoeff_imagPt_mem hβ 1) (mul_mem (pow_mem h4 2)
      (thetaW_imagPt_mem ht))
  · exact mul_mem (eightMinusTauCoeff_imagPt_mem hβ 2) (mul_mem h6
      (sub_mem (pow_mem (thetaU_imagPt_mem ht) 2) (pow_mem (thetaV_imagPt_mem ht) 2)))

theorem I_mul_inv_ckmrvPlusScale (a b : ℂ) :
    I * (ckmrvPlusScale * a * b)⁻¹ = (36 * (Real.pi : ℂ) ^ (-2 : ℤ) * a * b)⁻¹ := by
  rw [ckmrvPlusScale, show 36 * (Real.pi : ℂ) ^ (-2 : ℤ) * I * a * b =
    I * (36 * (Real.pi : ℂ) ^ (-2 : ℤ) * a * b) by ring, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ I_ne_zero, one_mul]

/-- **`K₊⁽⁸⁾(iβ, it)` is real.** -/
theorem ckmrvEightPlusKernel_imagPt_mem {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    ckmrvEightPlusKernel (imagPt β) (imagPt t) ∈ realSubfield := by
  unfold ckmrvEightPlusKernel ckmrvCoreContraction
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [show ckmrvPhiBasis (imagPt β) i * ckmrvEightPlusCoefficientMatrix (imagPt β) (imagPt t) i j *
      ckmrvTildePhiBasis (imagPt t) j =
      (ckmrvPhiBasis (imagPt β) i * I⁻¹) *
        (I * ckmrvEightPlusCoefficientMatrix (imagPt β) (imagPt t) i j) *
          ckmrvTildePhiBasis (imagPt t) j by
    rw [show ckmrvPhiBasis (imagPt β) i * I⁻¹ *
        (I * ckmrvEightPlusCoefficientMatrix (imagPt β) (imagPt t) i j) =
        ckmrvPhiBasis (imagPt β) i * (I⁻¹ * I) *
          ckmrvEightPlusCoefficientMatrix (imagPt β) (imagPt t) i j by ring,
      inv_mul_cancel₀ I_ne_zero, mul_one]]
  refine mul_mem (mul_mem (ckmrvPhiBasis_imagPt_mul_inv_I_mem hβ i) ?_)
    (ckmrvTildePhiBasis_imagPt_mem ht j)
  simp only [ckmrvEightPlusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    I_mul_inv_ckmrvPlusScale, ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  have hJ := sub_mem (kleinModularJ_imagPt_mem hβ) (kleinModularJ_imagPt_mem ht)
  have hπ := ofReal_mem_realSubfield Real.pi
  have hπ2 : (Real.pi : ℂ) ^ (-2 : ℤ) ∈ realSubfield := by
    rw [zpow_neg, zpow_two]
    exact inv_mem (mul_mem hπ hπ)
  refine mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (mul_mem (mul_mem
    (ofNat_mem_realSubfield 36) hπ2) (discriminant_imagPt_mem ht)) hJ))
      (ckmrvModularFactor_imagPt_mem hβ _))
    (ckmrvEightPlusCore_mem hJ i j)) (ckmrvModularFactor_imagPt_mem ht _)

theorem ckmrvEightKernel_imagPt_im {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    (ckmrvEightKernel (imagPt β) (imagPt t)).im = 0 :=
  mem_realSubfield_iff.mp (div_mem (add_mem (ckmrvEightPlusKernel_imagPt_mem hβ ht)
    (ckmrvEightMinusKernel_imagPt_mem hβ ht)) (ofNat_mem_realSubfield 2))

theorem ckmrvEightHatKernel_imagPt_im {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    (ckmrvEightHatKernel (imagPt β) (imagPt t)).im = 0 :=
  mem_realSubfield_iff.mp (div_mem (sub_mem (ckmrvEightPlusKernel_imagPt_mem hβ ht)
    (ckmrvEightMinusKernel_imagPt_mem hβ ht)) (ofNat_mem_realSubfield 2))

/-- **E8 certificates from the CKMRV data, realness discharged.** For `α > 0`, `α ≠ π`, given the
kernel positivity (6.4)(1), there is a Schwartz function `φ` such that the identity (**) for `φ`
makes `e^{−α|·|²} + φ` a Gaussian certificate for `E8`. -/
theorem e8_exists_gaussianSchwartzCertificate_of_pos {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (hpos : ∀ q t : ℝ, 0 < q → 0 < t → 0 ≤ (ckmrvEightHatKernel (imagPt q) (imagPt t)).re) :
    ∃ φ : SchwartzMap (Ambient 8) ℂ,
      (∀ x : Ambient 8, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Set.Ioi 0, ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) ∧
      ((∀ ξ : Ambient 8, ξ ≠ 0 →
        𝓕 (⇑φ) ξ +
            (((π / α) ^ 4 : ℝ) : ℂ) * (gaussianKernel (π ^ 2 / α) ξ : ℂ) =
          ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
            ∫ t in Set.Ioi 0, ckmrvEightHatKernel (imagPt (α / π)) (imagPt t) *
              (Real.exp (-(π * ‖ξ‖ ^ 2) * t) : ℂ)) →
        GaussianSchwartzCertificate e8Set α (gaussianSchwartz hα + φ)) :=
  e8_exists_gaussianSchwartzCertificate_of_ckmrv hα hαπ
    (fun _ _ hq ht => ⟨ckmrvEightKernel_imagPt_im hq ht, ckmrvEightHatKernel_imagPt_im hq ht⟩)
    hpos

end E8Leech
