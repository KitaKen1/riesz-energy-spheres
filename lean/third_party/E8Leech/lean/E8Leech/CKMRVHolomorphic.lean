import E8Leech.CKMRVPolynomialNumerators
import Mathlib.Geometry.Manifold.Notation

/-!
# Holomorphic polynomial numerators and the regular CKMRV coefficient locus

Use the already checked polynomial answer rather than differentiating a q-series.
All four numerator entries are jointly complex differentiable on H x H.
The actual coefficient formulas are jointly complex differentiable away from
j(tau) = j(z). This does not classify that locus into modular orbits, bound
pole orders, identify analytic residues or construct the phi/psi kernels.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3

noncomputable section
namespace E8Leech
open Set
open scoped Manifold Matrix

theorem mdifferentiable_modularDiscriminant : MDiff ModularForm.discriminant := by
  simpa only [CuspForm.coe_discriminant] using ModularFormClass.holo CuspForm.discriminant

theorem mdifferentiable_kleinModularJ : MDiff kleinModularJ :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    mdifferentiable_modularDiscriminant ModularForm.discriminant_ne_zero

def ckmrvRegularLocus : Set (UpperHalfPlane × UpperHalfPlane) :=
  {p | kleinModularJ p.1 - kleinModularJ p.2 ≠ 0}

theorem isOpen_ckmrvRegularLocus : IsOpen ckmrvRegularLocus :=
  isOpen_ne.preimage (continuous_kleinModularJ.comp continuous_fst |>.sub
    (continuous_kleinModularJ.comp continuous_snd))

theorem ckmrvKleinCrossDifference_ne_zero_iff (τ z : UpperHalfPlane) :
    ckmrvKleinCrossDifference τ z ≠ 0 ↔ (τ, z) ∈ ckmrvRegularLocus := by
  change ckmrvKleinCrossDifference τ z ≠ 0 ↔ kleinModularJ τ - kleinModularJ z ≠ 0
  rw [ckmrvKleinCrossDifference_eq]
  simp only [ne_eq, mul_eq_zero, ModularForm.discriminant_ne_zero, false_or]

theorem mdifferentiable_ckmrvKleinCrossDifference :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvKleinCrossDifference p.1 p.2) :=
  (((ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_fst).pow 3 |>.mul
    (mdifferentiable_modularDiscriminant.comp mdifferentiable_snd)).sub
      ((mdifferentiable_modularDiscriminant.comp mdifferentiable_fst).mul
        (((ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_snd).pow 3))

theorem mdifferentiable_ckmrvEightPlusPolynomialNumerator_entry (i j : Fin 3) :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvEightPlusPolynomialNumerator p.1 p.2 i j) := by
  have hA : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_fst
  have hB : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.1)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_fst
  have hD : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.1)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_fst
  have ha : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.2)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_snd
  have hb : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.2)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_snd
  have hd : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.2)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_snd
  have hH := mdifferentiable_ckmrvKleinCrossDifference
  fin_cases i <;> fin_cases j
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.E₆ p.1) * (ckmrvKleinCrossDifference p.1 p.2) : ℂ))
    exact (hB).mul (hH)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.discriminant p.1) * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) ^ 2 : ℂ))
    exact ((hD).mul (hB)).mul ((ha).pow 2)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-2 * (ModularForm.E₄ p.1) * (ckmrvKleinCrossDifference p.1 p.2) : ℂ))
    exact (((mdifferentiable_const).neg).mul (hA)).mul (hH)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-2 * (ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2) : ℂ))
    exact (((((mdifferentiable_const).neg).mul (hD)).mul (hA)).mul (ha)).mul (hb)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.discriminant p.2) : ℂ))
    exact (((hA).pow 2).mul (hB)).mul (hd)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const

theorem mdifferentiable_ckmrvEightMinusPolynomialNumerator_entry (i j : Fin 3) :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvEightMinusPolynomialNumerator p.1 p.2 i j) := by
  have hA : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_fst
  have hB : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.1)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_fst
  have hD : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.1)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_fst
  have ha : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.2)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_snd
  have hb : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.2)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_snd
  fin_cases i <;> fin_cases j
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-2 * 1728 * (ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2) : ℂ))
    exact ((((((mdifferentiable_const).neg).mul (mdifferentiable_const)).mul (hD)).mul (hA)).mul (ha)).mul (hb)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) ^ 2 : ℂ))
    exact (((hA).pow 2).mul (hB)).mul ((ha).pow 2)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-(ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.E₆ p.2) : ℂ))
    exact ((((hA).pow 2).neg).mul (hB)).mul (hb)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((1728 * (ModularForm.discriminant p.1) - (ModularForm.E₄ p.1) ^ 3) * (ModularForm.E₄ p.2) ^ 2 : ℂ))
    exact (((mdifferentiable_const).mul (hD)).sub ((hA).pow 3)).mul ((ha).pow 2)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.E₄ p.1) ^ 3 * (ModularForm.E₆ p.2) : ℂ))
    exact ((hA).pow 3).mul (hb)

theorem mdifferentiable_ckmrvLeechPlusPolynomialNumerator_entry (i j : Fin 3) :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvLeechPlusPolynomialNumerator p.1 p.2 i j) := by
  have hA : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_fst
  have hB : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.1)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_fst
  have hD : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.1)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_fst
  have ha : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.2)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_snd
  have hb : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.2)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_snd
  have hd : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.2)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_snd
  have hH := mdifferentiable_ckmrvKleinCrossDifference
  fin_cases i <;> fin_cases j
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (6 * (ckmrvKleinCrossDifference p.1 p.2) * (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) : ℂ))
    exact ((((mdifferentiable_const).mul (hH)).mul ((hA).pow 2)).mul (hB)).mul (ha)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((1728 * (ModularForm.discriminant p.1) * (ModularForm.discriminant p.2) - 6 * (ckmrvKleinCrossDifference p.1 p.2)) * (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₆ p.1) : ℂ))
    exact (((((mdifferentiable_const).mul (hD)).mul (hd)).sub ((mdifferentiable_const).mul (hH))).mul ((hA).pow 2)).mul (hB)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((-12 * (ModularForm.E₄ p.1) ^ 3 + 5 * 1728 * (ModularForm.discriminant p.1)) * (ckmrvKleinCrossDifference p.1 p.2) * (ModularForm.E₄ p.2) : ℂ))
    exact (((((mdifferentiable_const).neg).mul ((hA).pow 3)).add (((mdifferentiable_const).mul (mdifferentiable_const)).mul (hD))).mul (hH)).mul (ha)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-2 * 1728 * (ModularForm.discriminant p.1) ^ 2 * (ModularForm.E₄ p.2) ^ 2 * (ModularForm.E₆ p.2) : ℂ))
    exact (((((mdifferentiable_const).neg).mul (mdifferentiable_const)).mul ((hD).pow 2)).mul ((ha).pow 2)).mul (hb)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((12 * (ModularForm.E₄ p.1) ^ 3 - 7 * 1728 * (ModularForm.discriminant p.1)) * (ckmrvKleinCrossDifference p.1 p.2) : ℂ))
    exact (((mdifferentiable_const).mul ((hA).pow 3)).sub (((mdifferentiable_const).mul (mdifferentiable_const)).mul (hD))).mul (hH)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((1728 * (ModularForm.discriminant p.1) * (ModularForm.discriminant p.2) + 6 * (ckmrvKleinCrossDifference p.1 p.2)) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) : ℂ))
    exact ((((((mdifferentiable_const).mul (hD)).mul (hd)).add ((mdifferentiable_const).mul (hH))).mul (hA)).mul (hB)).mul (ha)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-6 * (ckmrvKleinCrossDifference p.1 p.2) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1) : ℂ))
    exact ((((mdifferentiable_const).neg).mul (hH)).mul (hA)).mul (hB)

theorem mdifferentiable_ckmrvLeechMinusPolynomialNumerator_entry (i j : Fin 3) :
    MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvLeechMinusPolynomialNumerator p.1 p.2 i j) := by
  have hA : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.1)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_fst
  have hB : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.1)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_fst
  have hD : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.1)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_fst
  have ha : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₄ p.2)) :=
    (ModularFormClass.holo ModularForm.E₄).comp mdifferentiable_snd
  have hb : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.E₆ p.2)) :=
    (ModularFormClass.holo ModularForm.E₆).comp mdifferentiable_snd
  have hd : MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (ModularForm.discriminant p.2)) :=
    mdifferentiable_modularDiscriminant.comp mdifferentiable_snd
  have hH := mdifferentiable_ckmrvKleinCrossDifference
  fin_cases i <;> fin_cases j
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-2 * 1728 * (ModularForm.discriminant p.1) ^ 2 * (ModularForm.E₄ p.2) ^ 2 * (ModularForm.E₆ p.2) : ℂ))
    exact (((((mdifferentiable_const).neg).mul (mdifferentiable_const)).mul ((hD).pow 2)).mul ((ha).pow 2)).mul (hb)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-2 * 1728 * (ModularForm.discriminant p.1) * (ckmrvKleinCrossDifference p.1 p.2) : ℂ))
    exact ((((mdifferentiable_const).neg).mul (mdifferentiable_const)).mul (hD)).mul (hH)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (((ModularForm.E₄ p.1) ^ 3 * (ModularForm.discriminant p.2) + 2 * (ckmrvKleinCrossDifference p.1 p.2)) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1) : ℂ))
    exact (((((hA).pow 3).mul (hd)).add ((mdifferentiable_const).mul (hH))).mul (hA)).mul (hB)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => (-(ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) * (ModularForm.E₆ p.1) * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2) : ℂ))
    exact (((((hD).neg).mul (hA)).mul (hB)).mul (ha)).mul (hb)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((0 : ℂ) : ℂ))
    exact mdifferentiable_const
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((1728 * (ModularForm.discriminant p.1) * (ModularForm.discriminant p.2) - 2 * (ckmrvKleinCrossDifference p.1 p.2) - (ModularForm.E₄ p.1) ^ 3 * (ModularForm.discriminant p.2)) * (ModularForm.E₄ p.1) ^ 2 : ℂ))
    exact (((((mdifferentiable_const).mul (hD)).mul (hd)).sub ((mdifferentiable_const).mul (hH))).sub (((hA).pow 3).mul (hd))).mul ((hA).pow 2)
  · change MDiff (fun p : UpperHalfPlane × UpperHalfPlane => ((ModularForm.discriminant p.1) * (ModularForm.E₄ p.1) ^ 2 * (ModularForm.E₄ p.2) * (ModularForm.E₆ p.2) : ℂ))
    exact (((hD).mul ((hA).pow 2)).mul (ha)).mul (hb)

end E8Leech
