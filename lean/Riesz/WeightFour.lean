import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# A one-coefficient shortcut for E8 theta identification

These lemmas apply to a genuine weight-four modular form. They do not provide
the missing modularity proof for the concrete E8 lattice theta expression.
Once that proof and constant coefficient one are available, the entire
q-expansion follows without separately enumerating every lattice shell.
-/

set_option autoImplicit false
noncomputable section
open UpperHalfPlane ModularForm EisensteinSeries
open scoped MatrixGroups
open scoped ArithmeticFunction.sigma

namespace SphericalRiesz

theorem weightFour_eq_constant_smul (f : ModularForm 𝒮ℒ 4) :
    f = (qExpansion 1 f).coeff 0 • E₄ := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • E₄ = f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp
        ModularForm.levelOne_weight_four_rank_one) f
  have hq : (qExpansion 1 f).coeff 0 = c := by
    rw [← hc, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_smul, E_qExpansion_coeff_zero _ ⟨2, rfl⟩, smul_eq_mul, mul_one]
  rw [hq]
  exact hc.symm

theorem weightFour_eq_of_constant_coeff (f g : ModularForm 𝒮ℒ 4)
    (h : (qExpansion 1 f).coeff 0 = (qExpansion 1 g).coeff 0) : f = g := by
  rw [weightFour_eq_constant_smul f, weightFour_eq_constant_smul g, h]

theorem weightFour_eq_E4 (f : ModularForm 𝒮ℒ 4)
    (h : (qExpansion 1 f).coeff 0 = 1) : f = E₄ := by
  rw [weightFour_eq_constant_smul f, h, one_smul]

theorem weightFour_first_coeff (f : ModularForm 𝒮ℒ 4)
    (h : (qExpansion 1 f).coeff 0 = 1) : (qExpansion 1 f).coeff 1 = 240 := by
  rw [weightFour_eq_E4 f h]
  exact ModularForm.E₄_qExpansion_coeff_one

theorem weightFour_positive_coeff (f : ModularForm 𝒮ℒ 4)
    (h : (qExpansion 1 f).coeff 0 = 1) (n : ℕ) (hn : n ≠ 0) :
    (qExpansion 1 f).coeff n = 240 * (ArithmeticFunction.sigma 3 n : ℂ) := by
  rw [weightFour_eq_E4 f h, E_qExpansion_coeff _ ⟨2, rfl⟩]
  norm_num [hn, show bernoulli 4 = -1/30 by decide +kernel]

#print axioms weightFour_eq_constant_smul
#print axioms weightFour_eq_of_constant_coeff
#print axioms weightFour_eq_E4
#print axioms weightFour_first_coeff
#print axioms weightFour_positive_coeff

end SphericalRiesz
