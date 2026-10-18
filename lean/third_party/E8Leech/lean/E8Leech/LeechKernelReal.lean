import E8Leech.CKMRVKernelReal
import E8Leech.LeechSchwartzProfile

/-!
# The Leech kernels are real on the imaginary axis

`K₊⁽²⁴⁾(iβ, it)` and `K₋⁽²⁴⁾(iβ, it)` are real for `β, t > 0`, by the same bookkeeping as for the
`E8` kernels (`CKMRVKernelReal`): the modular factors, the `ψ`, `ψ̃` and `φ̃` bases and the core
matrices are real on the axis, the `φ` basis is `i` times real, and the scale of the plus kernel is
`i` times real. Hence `𝒦⁽²⁴⁾` and `𝒦̂⁽²⁴⁾` are real on the axis.

The cusp coefficients of the two kernels at `τ = iβ` are real as well (`leechMinusCusp_imagPt_im`,
`leechPlusCusp_imagPt_im`): for the minus kernel every factor is real; for the plus kernel the
coefficients are computed with complex conjugation, which fixes the real factors and changes the
sign of `τ`, of the `φ` basis and of `i`.
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

/-- `ψ̃(it)` is real. -/
theorem ckmrvTildePsiBasis_imagPt_mem {t : ℝ} (ht : 0 < t) (j : Fin 3) :
    ckmrvTildePsiBasis (imagPt t) j ∈ realSubfield := by
  fin_cases j
  · show ckmrvL (imagPt t) ∈ realSubfield
    exact ckmrvL_imagPt_mem ht
  · show thetaW (imagPt t) ∈ realSubfield
    exact thetaW_imagPt_mem ht
  · show thetaU (imagPt t) ^ 2 - thetaV (imagPt t) ^ 2 ∈ realSubfield
    exact sub_mem (pow_mem (thetaU_imagPt_mem ht) 2) (pow_mem (thetaV_imagPt_mem ht) 2)

theorem ckmrvLeechMinusCore_mem {J g : ℂ} (hJ : J ∈ realSubfield) (hg : g ∈ realSubfield)
    (i j : Fin 3) : ckmrvLeechMinusCore J g i j ∈ realSubfield := by
  have h2 := ofNat_mem_realSubfield 2
  have h1728 := ofNat_mem_realSubfield 1728
  fin_cases i <;> fin_cases j
  · show (-2 * 1728 : ℂ) ∈ realSubfield
    exact mul_mem (neg_mem h2) h1728
  · show (-2 * 1728 * g : ℂ) ∈ realSubfield
    exact mul_mem (mul_mem (neg_mem h2) h1728) hg
  · show (0 : ℂ) ∈ realSubfield
    exact zero_mem _
  · show (0 : ℂ) ∈ realSubfield
    exact zero_mem _
  · show (J + 2 * g : ℂ) ∈ realSubfield
    exact add_mem hJ (mul_mem h2 hg)
  · show (-1 : ℂ) ∈ realSubfield
    exact neg_mem (one_mem _)
  · show (0 : ℂ) ∈ realSubfield
    exact zero_mem _
  · show (1728 - 2 * g - J : ℂ) ∈ realSubfield
    exact sub_mem (sub_mem h1728 (mul_mem h2 hg)) hJ
  · show (1 : ℂ) ∈ realSubfield
    exact one_mem _

theorem ckmrvLeechPlusCore_mem {J g : ℂ} (hJ : J ∈ realSubfield) (hg : g ∈ realSubfield)
    (i j : Fin 3) : ckmrvLeechPlusCore J g i j ∈ realSubfield := by
  have h2 := ofNat_mem_realSubfield 2
  have h5 := ofNat_mem_realSubfield 5
  have h6 := ofNat_mem_realSubfield 6
  have h7 := ofNat_mem_realSubfield 7
  have h12 := ofNat_mem_realSubfield 12
  have h1728 := ofNat_mem_realSubfield 1728
  fin_cases i <;> fin_cases j
  · show (6 : ℂ) ∈ realSubfield
    exact h6
  · show (0 : ℂ) ∈ realSubfield
    exact zero_mem _
  · show (1728 / g - 6 : ℂ) ∈ realSubfield
    exact sub_mem (div_mem h1728 hg) h6
  · show (-12 * J + 5 * 1728 : ℂ) ∈ realSubfield
    exact add_mem (mul_mem (neg_mem h12) hJ) (mul_mem h5 h1728)
  · show (-2 * 1728 / g : ℂ) ∈ realSubfield
    exact div_mem (mul_mem (neg_mem h2) h1728) hg
  · show (12 * J - 7 * 1728 : ℂ) ∈ realSubfield
    exact sub_mem (mul_mem h12 hJ) (mul_mem h7 h1728)
  · show (1728 / g + 6 : ℂ) ∈ realSubfield
    exact add_mem (div_mem h1728 hg) h6
  · show (0 : ℂ) ∈ realSubfield
    exact zero_mem _
  · show (-6 : ℂ) ∈ realSubfield
    exact neg_mem h6

theorem ckmrvMinusScale_mem : ckmrvMinusScale ∈ realSubfield := by
  unfold ckmrvMinusScale
  exact mul_mem (mul_mem (ofNat_mem_realSubfield 2) (ofNat_mem_realSubfield 1728))
    (ofReal_mem_realSubfield _)

/-- **`K₋⁽²⁴⁾(iβ, it)` is real.** -/
theorem ckmrvLeechMinusKernel_imagPt_mem {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    ckmrvLeechMinusKernel (imagPt β) (imagPt t) ∈ realSubfield := by
  unfold ckmrvLeechMinusKernel ckmrvCoreContraction
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  refine mul_mem (mul_mem (ckmrvPsiBasis_imagPt_mem hβ i) ?_) (ckmrvTildePsiBasis_imagPt_mem ht j)
  simp only [ckmrvLeechMinusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  have hJ := sub_mem (kleinModularJ_imagPt_mem hβ) (kleinModularJ_imagPt_mem ht)
  exact mul_mem (inv_mem (mul_mem (mul_mem ckmrvMinusScale_mem (discriminant_imagPt_mem ht)) hJ))
    (mul_mem (mul_mem (ckmrvModularFactor_imagPt_mem hβ _)
      (ckmrvLeechMinusCore_mem (kleinModularJ_imagPt_mem hβ) hJ i j))
      (ckmrvModularFactor_imagPt_mem ht _))

/-- **`K₊⁽²⁴⁾(iβ, it)` is real.** -/
theorem ckmrvLeechPlusKernel_imagPt_mem {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    ckmrvLeechPlusKernel (imagPt β) (imagPt t) ∈ realSubfield := by
  unfold ckmrvLeechPlusKernel ckmrvCoreContraction
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [show ckmrvPhiBasis (imagPt β) i * ckmrvLeechPlusCoefficientMatrix (imagPt β) (imagPt t) i j *
      ckmrvTildePhiBasis (imagPt t) j =
      (ckmrvPhiBasis (imagPt β) i * I⁻¹) *
        (I * ckmrvLeechPlusCoefficientMatrix (imagPt β) (imagPt t) i j) *
          ckmrvTildePhiBasis (imagPt t) j by
    rw [show ckmrvPhiBasis (imagPt β) i * I⁻¹ *
        (I * ckmrvLeechPlusCoefficientMatrix (imagPt β) (imagPt t) i j) =
        ckmrvPhiBasis (imagPt β) i * (I⁻¹ * I) *
          ckmrvLeechPlusCoefficientMatrix (imagPt β) (imagPt t) i j by ring,
      inv_mul_cancel₀ I_ne_zero, mul_one]]
  refine mul_mem (mul_mem (ckmrvPhiBasis_imagPt_mul_inv_I_mem hβ i) ?_)
    (ckmrvTildePhiBasis_imagPt_mem ht j)
  have hJ := sub_mem (kleinModularJ_imagPt_mem hβ) (kleinModularJ_imagPt_mem ht)
  have hπ := ofReal_mem_realSubfield Real.pi
  have hπ2 : (Real.pi : ℂ) ^ (-2 : ℤ) ∈ realSubfield := by
    rw [zpow_neg, zpow_two]
    exact inv_mem (mul_mem hπ hπ)
  have hscale : I * (1728 * ckmrvPlusScale * ModularForm.discriminant (imagPt t))⁻¹ =
      (36 * (Real.pi : ℂ) ^ (-2 : ℤ) * 1728 * ModularForm.discriminant (imagPt t))⁻¹ := by
    rw [show (1728 : ℂ) * ckmrvPlusScale * ModularForm.discriminant (imagPt t) =
      ckmrvPlusScale * 1728 * ModularForm.discriminant (imagPt t) by ring]
    exact I_mul_inv_ckmrvPlusScale _ _
  simp only [ckmrvLeechPlusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  rw [← mul_assoc, hscale]
  exact mul_mem (inv_mem (mul_mem (mul_mem (mul_mem (ofNat_mem_realSubfield 36) hπ2)
    (ofNat_mem_realSubfield 1728)) (discriminant_imagPt_mem ht)))
    (mul_mem (mul_mem (ckmrvModularFactor_imagPt_mem hβ _)
      (ckmrvLeechPlusCore_mem (kleinModularJ_imagPt_mem hβ) hJ i j))
      (ckmrvModularFactor_imagPt_mem ht _))

theorem ckmrvLeechKernel_imagPt_im {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    (ckmrvLeechKernel (imagPt β) (imagPt t)).im = 0 :=
  mem_realSubfield_iff.mp (div_mem (add_mem (ckmrvLeechPlusKernel_imagPt_mem hβ ht)
    (ckmrvLeechMinusKernel_imagPt_mem hβ ht)) (ofNat_mem_realSubfield 2))

theorem ckmrvLeechHatKernel_imagPt_im {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    (ckmrvLeechHatKernel (imagPt β) (imagPt t)).im = 0 :=
  mem_realSubfield_iff.mp (div_mem (sub_mem (ckmrvLeechPlusKernel_imagPt_mem hβ ht)
    (ckmrvLeechMinusKernel_imagPt_mem hβ ht)) (ofNat_mem_realSubfield 2))

/-- `(K₊ + s K₋)/2 (iβ, it)` is real for real `s`. -/
theorem leechAxisKernel_im {s : ℂ} (hs : s.im = 0) {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    (leechAxisKernel s β t).im = 0 :=
  mem_realSubfield_iff.mp (div_mem (add_mem (ckmrvLeechPlusKernel_imagPt_mem hβ ht)
    (mul_mem (mem_realSubfield_iff.mpr hs) (ckmrvLeechMinusKernel_imagPt_mem hβ ht)))
    (ofNat_mem_realSubfield 2))

/-! ## The cusp coefficients -/

theorem conj_of_mem_realSubfield {z : ℂ} (h : z ∈ realSubfield) : (starRingEnd ℂ) z = z :=
  Complex.conj_eq_iff_im.mpr (mem_realSubfield_iff.mp h)

/-- `z = i · (real)` changes sign under conjugation. -/
theorem conj_of_mul_inv_I_mem {z : ℂ} (h : z * I⁻¹ ∈ realSubfield) : (starRingEnd ℂ) z = -z := by
  have h1 := conj_of_mem_realSubfield h
  rw [map_mul, map_inv₀, Complex.conj_I] at h1
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  calc (starRingEnd ℂ) z = (starRingEnd ℂ) z * (-I)⁻¹ * (-I) := by field_simp
    _ = z * I⁻¹ * (-I) := by rw [h1]
    _ = -z := by field_simp

/-- The cusp coefficients of `K₋⁽²⁴⁾(iβ, ·)` are real. -/
theorem leechMinusCusp_imagPt_im {β : ℝ} (hβ : 0 < β) (k : Fin 4) :
    (leechMinusCusp (imagPt β) k).im = 0 := by
  rw [← mem_realSubfield_iff]
  have h2 := ofNat_mem_realSubfield 2
  have h4n := ofNat_mem_realSubfield 4
  have h12 := ofNat_mem_realSubfield 12
  have h408 := ofNat_mem_realSubfield 408
  have h696 := ofNat_mem_realSubfield 696
  have h720 := ofNat_mem_realSubfield 720
  have h744 := ofNat_mem_realSubfield 744
  have h1728 := ofNat_mem_realSubfield 1728
  have hπ := ofReal_mem_realSubfield Real.pi
  have hlog := ofReal_mem_realSubfield (Real.log 2)
  have h4 := E4_imagPt_mem hβ
  have h6 := E6_imagPt_mem hβ
  have hΔ := discriminant_imagPt_mem hβ
  have hj := kleinModularJ_imagPt_mem hβ
  have hsc := inv_mem ckmrvMinusScale_mem
  have hα : leechMinusAlpha (imagPt β) ∈ realSubfield :=
    sub_mem (mul_mem (ckmrvPsiBasis_imagPt_mem hβ 1) (mul_mem h4 h6))
      (mul_mem (ckmrvPsiBasis_imagPt_mem hβ 2) (pow_mem h4 2))
  have hb : leechMinusBeta (imagPt β) ∈ realSubfield :=
    sub_mem (mul_mem h2 hα) (mul_mem (mul_mem h2 h1728) hΔ)
  have hγ : leechMinusGamma (imagPt β) ∈ realSubfield :=
    add_mem (mul_mem hj hα) (mul_mem h1728 (mul_mem (ckmrvPsiBasis_imagPt_mem hβ 2) (pow_mem h4 2)))
  have hN : leechMinusNZeroC (imagPt β) ∈ realSubfield :=
    add_mem (add_mem (add_mem (mul_mem h12 (mul_mem (neg_mem (mul_mem h2 h1728)) hΔ))
      (mul_mem (sub_mem hj h744) hb)) hγ) (mul_mem h408 hα)
  have hD1 : (2 * 1728 * ModularForm.discriminant (imagPt β) : ℂ) ∈ realSubfield :=
    mul_mem (mul_mem h2 h1728) hΔ
  have hD2 : (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
      (720 - kleinModularJ (imagPt β)) : ℂ) ∈ realSubfield :=
    mul_mem (mul_mem (neg_mem (mul_mem h2 h1728)) hΔ) (sub_mem h720 hj)
  fin_cases k
  · show ckmrvMinusScale⁻¹ * (-(π : ℂ) * (2 * 1728 * ModularForm.discriminant (imagPt β))) ∈
      realSubfield
    exact mul_mem hsc (mul_mem (neg_mem hπ) hD1)
  · show ckmrvMinusScale⁻¹ * (4 * (Real.log 2 : ℂ) *
        (2 * 1728 * ModularForm.discriminant (imagPt β)) +
      (leechMinusBeta (imagPt β) + leechMinusAlpha (imagPt β))) ∈ realSubfield
    exact mul_mem hsc (add_mem (mul_mem (mul_mem h4n hlog) hD1) (add_mem hb hα))
  · show ckmrvMinusScale⁻¹ * (-(π : ℂ) * (-(2 * 1728) * ModularForm.discriminant (imagPt β) *
        (720 - kleinModularJ (imagPt β)))) ∈ realSubfield
    exact mul_mem hsc (mul_mem (neg_mem hπ) hD2)
  · show ckmrvMinusScale⁻¹ * (4 * (Real.log 2 : ℂ) *
        (-(2 * 1728) * ModularForm.discriminant (imagPt β) * (720 - kleinModularJ (imagPt β))) +
      ((-leechMinusBeta (imagPt β) - leechMinusAlpha (imagPt β)) *
        (696 - kleinModularJ (imagPt β)) - leechMinusNZeroC (imagPt β))) ∈ realSubfield
    exact mul_mem hsc (add_mem (mul_mem (mul_mem h4n hlog) hD2)
      (sub_mem (mul_mem (sub_mem (neg_mem hb) hα) (sub_mem h696 hj)) hN))

/-- The cusp coefficients of `K₊⁽²⁴⁾(iβ, ·)` are real. -/
theorem leechPlusCusp_imagPt_im {β : ℝ} (hβ : 0 < β) (k : Fin 4) :
    (leechPlusCusp (imagPt β) k).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have hτ : (starRingEnd ℂ) ((imagPt β : ℍ) : ℂ) = -((imagPt β : ℍ) : ℂ) := by
    rw [coe_imagPt hβ, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have h4 := conj_of_mem_realSubfield (E4_imagPt_mem hβ)
  have h6 := conj_of_mem_realSubfield (E6_imagPt_mem hβ)
  have hΔ := conj_of_mem_realSubfield (discriminant_imagPt_mem hβ)
  have hj := conj_of_mem_realSubfield (kleinModularJ_imagPt_mem hβ)
  have hφ1 := conj_of_mul_inv_I_mem (ckmrvPhiBasis_imagPt_mul_inv_I_mem hβ 1)
  have hφ2 := conj_of_mul_inv_I_mem (ckmrvPhiBasis_imagPt_mul_inv_I_mem hβ 2)
  have hA0 : (starRingEnd ℂ) (leechPlusA0 (imagPt β)) = -leechPlusA0 (imagPt β) := by
    simp only [leechPlusA0, map_mul, map_pow, hτ, h4, h6]
    ring
  have hA1 : (starRingEnd ℂ) (leechPlusA1 (imagPt β)) = -leechPlusA1 (imagPt β) := by
    simp only [leechPlusA1, map_mul, hφ1, hΔ]
    ring
  have hA2 : (starRingEnd ℂ) (leechPlusA2 (imagPt β)) = -leechPlusA2 (imagPt β) := by
    simp only [leechPlusA2, map_mul, hφ2, h4, h6]
    ring
  have hP2 : (starRingEnd ℂ) (leechPlusP2 (imagPt β)) = -leechPlusP2 (imagPt β) := by
    simp only [leechPlusP2, map_add, map_mul, map_sub, map_neg, map_ofNat, hA0, hA1, hA2, hj]
    ring
  have hM1a : (starRingEnd ℂ) (leechPlusM1a (imagPt β)) = leechPlusM1a (imagPt β) := by
    simp only [leechPlusM1a, map_sub, map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal, hP2, hA1]
    ring
  have hM0a : (starRingEnd ℂ) (leechPlusM0a (imagPt β)) = -leechPlusM0a (imagPt β) := by
    simp only [leechPlusM0a, map_mul, map_neg, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
      hP2]
    ring
  have hM1c : (starRingEnd ℂ) (leechPlusM1c (imagPt β)) = leechPlusM1c (imagPt β) := by
    simp only [leechPlusM1c, map_add, map_sub, map_mul, map_div₀, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal, hA0, hA1, hj]
    ring
  have hM0c : (starRingEnd ℂ) (leechPlusM0c (imagPt β)) = -leechPlusM0c (imagPt β) := by
    simp only [leechPlusM0c, map_sub, map_mul, map_neg, map_div₀, map_pow, map_ofNat,
      Complex.conj_ofReal, hP2, hA0]
    ring
  have hsc : (starRingEnd ℂ) ((1728 * ckmrvPlusScale)⁻¹) = -(1728 * ckmrvPlusScale)⁻¹ := by
    simp only [ckmrvPlusScale, map_inv₀, map_mul, map_ofNat, map_zpow₀, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  fin_cases k
  · show (starRingEnd ℂ) ((1728 * ckmrvPlusScale)⁻¹ * (I * leechPlusM1a (imagPt β))) =
      (1728 * ckmrvPlusScale)⁻¹ * (I * leechPlusM1a (imagPt β))
    rw [map_mul, map_mul, hsc, Complex.conj_I, hM1a]
    ring
  · show (starRingEnd ℂ) ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt β)) =
      (1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt β)
    rw [map_mul, hsc, hM0a]
    ring
  · show (starRingEnd ℂ) ((1728 * ckmrvPlusScale)⁻¹ * (I * leechPlusM1c (imagPt β))) =
      (1728 * ckmrvPlusScale)⁻¹ * (I * leechPlusM1c (imagPt β))
    rw [map_mul, map_mul, hsc, Complex.conj_I, hM1c]
    ring
  · show (starRingEnd ℂ) ((1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c (imagPt β)) =
      (1728 * ckmrvPlusScale)⁻¹ * leechPlusM0c (imagPt β)
    rw [map_mul, hsc, hM0c]
    ring

/-- The cusp coefficients of `(K₊ + s K₋)/2 (iβ, ·)` are real for real `s`. -/
theorem leechAxisCusp_im {s : ℂ} (hs : s.im = 0) {β : ℝ} (hβ : 0 < β) (k : Fin 4) :
    (leechAxisCusp s β k).im = 0 := by
  have hp := mem_realSubfield_iff.mpr (leechPlusCusp_imagPt_im hβ k)
  have hm := mem_realSubfield_iff.mpr (leechMinusCusp_imagPt_im hβ k)
  exact mem_realSubfield_iff.mp (div_mem (add_mem hp (mul_mem (mem_realSubfield_iff.mpr hs) hm))
    (ofNat_mem_realSubfield 2))

end E8Leech
