-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.Eta
import Mathlib.NumberTheory.ModularForms.QExpansion

public import SpherePacking.ForMathlib.Cusps


/-!
# Discriminant Product Formula

This file proves results such as `DiscriminantProductFormula`, `Delta_eq_eta_pow`,
`Discriminant_T_invariant`, `Discriminant_S_invariant`, `I_in_atImInfty`.
-/

open scoped BigOperators Real Nat

open ModularForm UpperHalfPlane Complex MatrixGroups Function Set Filter

noncomputable section Definitions

/-- The discriminant modular form `Δ` as an explicit infinite product. -/
@[expose] public def Δ (z : UpperHalfPlane) := cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

/-- Reindex `Δ` from a product over `ℕ` to a product over `ℕ+`. -/
public lemma DiscriminantProductFormula (z : ℍ) :
    Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
  simpa [Δ, Nat.cast_add, Nat.cast_one, add_mul] using
    (tprod_pnat_eq_tprod_succ (f := fun n : ℕ =>
      (1 - cexp (2 * π * Complex.I * (n : ℂ) * z)) ^ 24)).symm

/-- The discriminant form is the 24th power of the Dedekind eta function. -/
public lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (etaSP z) ^ 24 := by
  rw [etaSP, Δ, mul_pow]
  congr
  · rw [← Complex.exp_nat_mul]
    congr 1
    simp [field]
  rw [tprod_pow]
  apply MultipliableEtaProductExpansion


/-- The discriminant `Δ z` is nonzero on the upper half-plane. -/
public lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  simpa [Delta_eq_eta_pow] using pow_ne_zero 24 (eta_nonzero_on_UpperHalfPlane z)

/-- Invariance of `Δ` under the translation `T : z ↦ z + 1`. -/
public lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [ modular_slash_T_apply, Δ, Δ]
  simp only [coe_vadd, ofReal_one]
  congr 1
  · simpa using exp_periodo z 1
  · refine tprod_congr fun b => ?_
    simpa [Nat.cast_add, Nat.cast_one] using
      congrArg (fun t => (1 - t) ^ (24 : ℕ)) (exp_periodo z (b + 1))


/-- Invariance of `Δ` under the inversion `S : z ↦ -1/z`. -/
public lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [modular_slash_S_apply, Delta_eq_eta_pow, Delta_eq_eta_pow]
  have he : etaSP ((-z : ℂ)⁻¹) = (csqrt Complex.I)⁻¹ * (csqrt (z : ℂ) * etaSP (z : ℂ)) := by
    simpa [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, div_eq_mul_inv] using
      (eta_equality z.2)
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  rw [he]
  simp [mul_pow, inv_pow, csqrt_I, csqrt_pow_24 (z := (z : ℂ)) hz, zpow_neg]
  field_simp [hz]

/-- Δ as a SlashInvariantForm of weight 12 -/
@[expose] public def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' :=
    slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant

/-- Δ is 1-periodic: Δ(z + 1) = Δ(z) -/
public lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z :=
  by
  have h := congrFun Discriminant_T_invariant z
  rwa [modular_slash_T_apply] at h

/-- Δ transforms under S as: Δ(-1/z) = z¹² · Δ(z) -/
public lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := congrFun Discriminant_S_invariant z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  rw [h, mul_comm]


lemma I_in_atImInfty (A : ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty := by
  rw [atImInfty_mem]
  exact ⟨A, fun _ hz ↦ hz⟩


/-- Scalar multiplication of `ℍ` by a positive natural number. -/
public instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by
    have hx : 0 < (x : ℝ) := by exact_mod_cast x.pos
    simpa [mul_im] using mul_pos hx z.2

/-- Coercion formula for the `ℕ+`-scalar action on `ℍ`. -/
public theorem natPosSMul_apply (c : ℕ+) (z : ℍ) :
    ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := rfl

/-- A set `S ⊆ ℍ` is stable under scaling by positive naturals. -/
@[expose] public def pnat_smul_stable (S : Set ℍ) :=
    ∀ n : ℕ+, ∀ (s : ℍ), s ∈ S → n • s ∈ S

/-- Inside `atImInfty`, shrink to a subset stable under positive-integer scaling. -/
public lemma atImInfy_pnat_mono (S : Set ℍ) (hS : S ∈ atImInfty) (B : ℝ) :
    ∃ A : ℝ,
      pnat_smul_stable (S ∩ {z : ℍ | max A B ≤ z.im}) ∧
        S ∩ {z : ℍ | max A B ≤ z.im} ∈ atImInfty := by
  have hS2 := hS
  rw [atImInfty_mem] at hS
  obtain ⟨A, hA⟩ := hS
  use A
  constructor
  · intro n s hs
    rcases hs with ⟨hsS, hsIm⟩
    have hsIm' : A ≤ s.im ∧ B ≤ s.im := by
      simpa [max_le_iff] using hsIm
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (PNat.one_le n)
    have hmul : s.im ≤ (n : ℝ) * s.im := (le_mul_iff_one_le_left s.2).2 hn
    have K : max A B ≤ (n • s).im := by
      rw [UpperHalfPlane.im, natPosSMul_apply]
      simp only [mul_im, natCast_re, coe_im, natCast_im, coe_re, zero_mul, add_zero]
      exact (max_le_iff.2 ⟨le_trans hsIm'.1 hmul, le_trans hsIm'.2 hmul⟩)
    exact ⟨hA _ (le_trans (le_max_left A B) K), K⟩
  · exact Filter.inter_mem hS2 (I_in_atImInfty (A := max A B))

end Definitions
