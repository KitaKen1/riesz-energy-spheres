import Riesz.FCLeechShells24
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
open UpperHalfPlane ModularForm EisensteinSeries
open scoped MatrixGroups
namespace SphericalRiesz

private theorem weightTwelve_eq_of_first_coeff (f g : ModularForm 𝒮ℒ 12)
    (h0 : (qExpansion 1 f).coeff 0 = (qExpansion 1 g).coeff 0)
    (h1 : (qExpansion 1 f).coeff 1 = (qExpansion 1 g).coeff 1) : f = g := by
  have hf : IsCuspForm (f - g) := by
    rw [isCuspForm_iff_coeffZero_eq_zero]
    simp only [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      map_sub, h0, sub_self]
  obtain ⟨h, hh⟩ := hf
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve h
  have hhFun : (h : ℍ → ℂ) = (f - g : ModularForm 𝒮ℒ 12) := congrArg DFunLike.coe hh
  have hcFun : (c • CuspForm.discriminant : ℍ → ℂ) = h := congrArg DFunLike.coe hc
  have hq := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant
  rw [hcFun, hhFun] at hq
  have hz : c = 0 := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 1) hq
    simpa only [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      map_sub, h1, sub_self, PowerSeries.coeff_smul, CuspForm.coe_discriminant, discriminant_qExpansion_coeff_one,
      smul_eq_mul, mul_one] using h.symm
  have hh0 : h = 0 := by rw [← hc, hz, zero_smul]
  apply sub_eq_zero.mp
  rw [← hh, hh0]
  rfl

def leechModularTarget : ModularForm 𝒮ℒ 12 :=
  (7 / 12 : ℂ) • ModularForm.mcast (by decide) (E₄.pow 3) +
    (5 / 12 : ℂ) • ModularForm.mcast (by decide) (E₆.pow 2)

theorem leechModularTarget_apply (τ : ℍ) :
    leechModularTarget τ = (7 * E₄ τ ^ 3 + 5 * E₆ τ ^ 2) / 12 := by
  change (7 / 12 : ℂ) * E₄ τ ^ 3 + (5 / 12 : ℂ) * E₆ τ ^ 2 = _
  ring

private theorem leechModularTarget_qExpansion :
    qExpansion 1 leechModularTarget =
      (7 / 12 : ℂ) • (qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄) +
        (5 / 12 : ℂ) • (qExpansion 1 E₆ * qExpansion 1 E₆) := by
  let A : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3)
  let B : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₆.pow 2)
  change qExpansion 1 (⇑((7 / 12 : ℂ) • A) + ⇑((5 / 12 : ℂ) • B)) = _
  rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL
    ((7 / 12 : ℂ) • A) ((5 / 12 : ℂ) • B)]
  rw [show (⇑((7 / 12 : ℂ) • A) : ℍ → ℂ) = (7 / 12 : ℂ) • ⇑A from rfl,
    show (⇑((5 / 12 : ℂ) • B) : ℍ → ℂ) = (5 / 12 : ℂ) • ⇑B from rfl,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (7 / 12) A,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (5 / 12) B]
  dsimp only [A, B]
  simp only [coe_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  congr 1 <;> congr 1 <;> ring

private theorem leechModularTarget_qExpansion_zero :
    (qExpansion 1 leechModularTarget).coeff 0 = 1 := by
  rw [leechModularTarget_qExpansion]
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_smul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

private theorem leechModularTarget_qExpansion_one :
    (qExpansion 1 leechModularTarget).coeff 1 = 0 := by
  rw [leechModularTarget_qExpansion]
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_smul, -PowerSeries.coeff_zero_eq_constantCoeff, Finset.Nat.antidiagonal_succ,
    E₄_qExpansion_coeff_one, E₆_qExpansion_coeff_one,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

theorem leechThetaModularForm_eq : leechThetaModularForm = leechModularTarget := by
  apply weightTwelve_eq_of_first_coeff
  · rw [leechThetaModularForm_qExpansion_zero, leechModularTarget_qExpansion_zero]
  · rw [show (qExpansion 1 leechThetaModularForm).coeff 1 = 0 from
      leechThetaUpper_qExpansion_one, leechModularTarget_qExpansion_one]

theorem leechTheta_eq_E4_E6 (τ : ℍ) :
    leechTheta τ = (7 * E₄ τ ^ 3 + 5 * E₆ τ ^ 2) / 12 := by
  have h := congrArg (fun f : ModularForm 𝒮ℒ 12 => f τ) leechThetaModularForm_eq
  exact h.trans (leechModularTarget_apply τ)

end SphericalRiesz
