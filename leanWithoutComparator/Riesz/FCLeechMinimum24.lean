import Riesz.LeechLattice24
import Mathlib
import Std.Tactic
import Init.Data.Fin.Fold
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases

/-
Adapted from the existing Sphere-Packing-Lean norm-spectrum proof in the E8Leach port.
Apache-2.0; upstream attribution and licences are retained under third_party/E8Leech.
Only imports and the aliases below specialize it to Riesz.LeechLattice24.
-/

namespace SphericalRiesz
noncomputable def leechGeneratorRowsUnscaled (i : Fin 24) : LeechAmbient :=
  WithLp.toLp 2 fun j : Fin 24 => (leechMatrixInt i j : ℝ)
noncomputable def leechGeneratorRows (i : Fin 24) : LeechAmbient :=
  ((Real.sqrt 8)⁻¹ : ℝ) • leechGeneratorRowsUnscaled i
noncomputable def LeechLattice : Submodule ℤ LeechAmbient :=
  Submodule.span ℤ (Set.range leechGeneratorRows)

theorem leechGeneratorRows_eq (i : Fin 24) :
    leechGeneratorRows i = WithLp.toLp 2 (leechMatrix.row i) := by
  rfl
end SphericalRiesz
/-
Leech lattice: norm-spectrum facts.

These are the geometric properties used in the packing construction.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.


/-!
# Leech lattice norm bounds

Auxiliary parity code used to rule out vectors of squared norm `2` and to prove a lower bound on
the norm of nonzero Leech lattice vectors.

This is a finite computation: we use a fixed 12-generator binary code with minimum weight `8`.

## Main statements
* `leech_norm_sq_eq_two_mul`
* `leech_norm_lower_bound`
-/

open scoped BigOperators
open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SphericalRiesz.LeechNorm
def rowInt (i : Fin 24) : Fin 24 → ℤ :=
  leechMatrixInt i

def leechDot (i j : Fin 24) : ℤ :=
  (rowInt i) ⬝ᵥ (rowInt j)

lemma leechDot_mod8 (i j : Fin 24) : (8 : ℤ) ∣ leechDot i j := by
  fin_cases i <;> fin_cases j <;> decide

lemma leechDot_diag_mod16 (i : Fin 24) : (16 : ℤ) ∣ leechDot i i := by
  fin_cases i <;> decide

def combInt (c : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun k : Fin 24 => ∑ i : Fin 24, c i * rowInt i k

def combReal (c : Fin 24 → ℤ) : ℝ²⁴ :=
  WithLp.toLp 2 fun k : Fin 24 => (combInt c k : ℝ)

private lemma leechGeneratorRowsUnscaled_eq_rowInt (i : Fin 24) :
    leechGeneratorRowsUnscaled i = WithLp.toLp 2 fun k : Fin 24 => (rowInt i k : ℝ) := rfl

lemma sum_smul_leechGeneratorRowsUnscaled_eq_combReal (c : Fin 24 → ℤ) :
    (∑ i : Fin 24, (c i : ℝ) • leechGeneratorRowsUnscaled i) = combReal c := by
  ext k
  simp [combReal, combInt, rowInt, leechGeneratorRowsUnscaled]

lemma sum_smul_leechGeneratorRows_eq_smul_combReal (c : Fin 24 → ℤ) :
    (∑ i : Fin 24, (c i : ℝ) • leechGeneratorRows i) =
      ((Real.sqrt 8)⁻¹ : ℝ) • combReal c := by
  calc
    (∑ i : Fin 24, (c i : ℝ) • leechGeneratorRows i) =
        ∑ i : Fin 24, ((Real.sqrt 8)⁻¹ : ℝ) • ((c i : ℝ) • leechGeneratorRowsUnscaled i) := by
          simp [leechGeneratorRows, smul_smul, mul_comm]
    _ = ((Real.sqrt 8)⁻¹ : ℝ) • ∑ i : Fin 24, (c i : ℝ) • leechGeneratorRowsUnscaled i := by
          simp [Finset.smul_sum, smul_smul]
    _ = ((Real.sqrt 8)⁻¹ : ℝ) • combReal c := by
          simp [sum_smul_leechGeneratorRowsUnscaled_eq_combReal]

lemma combReal_norm_sq (c : Fin 24 → ℤ) :
    ‖combReal c‖ ^ 2 = ((combInt c ⬝ᵥ combInt c : ℤ) : ℝ) := by
  -- Avoid inner product search; use the explicit `L2`-norm formula on `EuclideanSpace`.
  calc
    ‖combReal c‖ ^ 2 = ∑ k : Fin 24, ‖(combReal c) k‖ ^ 2 := by
          simpa using! (EuclideanSpace.norm_sq_eq (combReal c))
    _ = ∑ k : Fin 24, ((combInt c k : ℝ) ^ 2) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          simp [combReal, Real.norm_eq_abs, sq_abs]
    _ = ((combInt c ⬝ᵥ combInt c : ℤ) : ℝ) := by
          simp [dotProduct, pow_two, Int.cast_sum, Int.cast_mul]

lemma combInt_dot_eq_sum (c : Fin 24 → ℤ) :
    (combInt c ⬝ᵥ combInt c) = ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * leechDot i j := by
  -- Expand using bilinearity of `dotProduct` and the definition of `combInt`.
  let f : Fin 24 → (Fin 24 → ℤ) := fun i => fun k => c i * rowInt i k
  have hcomb : combInt c = ∑ i : Fin 24, f i := by
    ext k
    simp [combInt, f]
  calc
    combInt c ⬝ᵥ combInt c
        = (∑ i : Fin 24, f i) ⬝ᵥ (∑ j : Fin 24, f j) := by simp [hcomb]
    _ = ∑ i : Fin 24, f i ⬝ᵥ (∑ j : Fin 24, f j) :=
          sum_dotProduct Finset.univ f (∑ j, f j)
    _ = ∑ i : Fin 24, ∑ j : Fin 24, f i ⬝ᵥ f j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simpa using!
            (dotProduct_sum (u := f i) (s := (Finset.univ : Finset (Fin 24))) (v := f))
    _ = ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * leechDot i j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp [f, leechDot, dotProduct, mul_assoc, mul_left_comm, Finset.mul_sum]

lemma combInt_dot_divisible_by_16 (c : Fin 24 → ℤ) :
    (16 : ℤ) ∣ (combInt c ⬝ᵥ combInt c) := by
  -- Write the dot product as `8 * S`, where `S` is an integer, and show `S` is even by a mod-2
  -- symmetry argument.
  let g : Fin 24 → Fin 24 → ℤ := fun i j => leechDot i j / 8
  have hg_symm : ∀ i j, g i j = g j i := by
    intro i j
    have h : leechDot i j = leechDot j i := by
      simp [leechDot, rowInt, dotProduct_comm]
    simp [g, h]
  have hg_diag_even : ∀ i, (2 : ℤ) ∣ g i i := by
    intro i
    rcases leechDot_diag_mod16 i with ⟨m, hm⟩
    lia
  let S : ℤ := ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * g i j
  have hdot : (combInt c ⬝ᵥ combInt c) = 8 * S := by
    have hleech : ∀ i j, leechDot i j = g i j * 8 := by
      intro i j
      simpa [g] using!
        (Int.ediv_mul_cancel (a := leechDot i j) (b := (8 : ℤ)) (leechDot_mod8 i j)).symm
    have h1 :
        (combInt c ⬝ᵥ combInt c) =
          ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * (g i j * 8) := by
      simpa [hleech] using! (combInt_dot_eq_sum c)
    have hinner : ∀ i, (∑ j : Fin 24, 8 * (c i * c j * g i j)) =
        8 * (∑ j : Fin 24, c i * c j * g i j) :=
      fun i => Eq.symm (Finset.mul_sum Finset.univ (fun i_1 => c i * c i_1 * g i i_1) 8)
    calc
      combInt c ⬝ᵥ combInt c
          = ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * (g i j * 8) := h1
      _ = ∑ i : Fin 24, ∑ j : Fin 24, 8 * (c i * c j * g i j) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
      _ = ∑ i : Fin 24, 8 * (∑ j : Fin 24, c i * c j * g i j) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simpa using! (hinner i)
      _ = 8 * (∑ i : Fin 24, ∑ j : Fin 24, c i * c j * g i j) :=
            Eq.symm (Finset.mul_sum Finset.univ (fun i => ∑ j, c i * c j * g i j) 8)
      _ = 8 * S := by rfl
  have hS_even : (2 : ℤ) ∣ S := by
    -- Work in `ZMod 2`.
    let c2 : Fin 24 → ZMod 2 := fun i => (c i : ZMod 2)
    let g2 : Fin 24 → Fin 24 → ZMod 2 := fun i j => (g i j : ZMod 2)
    let F : (Fin 24 × Fin 24) → ZMod 2 := fun p => c2 p.1 * c2 p.2 * g2 p.1 p.2
    have hg2_diag : ∀ i, g2 i i = 0 := by
      intro i
      have : (2 : ℤ) ∣ g i i := hg_diag_even i
      simpa [g2] using! (ZMod.intCast_zmod_eq_zero_iff_dvd (g i i) 2).2 this
    have hg2_symm : ∀ i j, g2 i j = g2 j i := by
      intro i j
      simpa [g2] using! congrArg (fun t : ℤ => (t : ZMod 2)) (hg_symm i j)
    let s : Finset (Fin 24) := Finset.univ
    have hoff : ∑ p ∈ s.offDiag, F p = 0 := by
      refine Finset.sum_involution (s := s.offDiag) (f := F)
        (g := fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
      · intro p hp
        have hswap : F (Prod.swap p) = F p := by
          cases p with
          | mk i j =>
            simp [F, c2, g2, hg2_symm, mul_assoc, mul_left_comm]
        exact CharTwo.add_eq_zero.mpr (id (Eq.symm hswap))
      · intro p hp hFp
        have hneq : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
        intro hEq
        apply hneq
        cases p with
        | mk i j =>
          have : (j, i) = (i, j) := by simpa [Prod.swap] using! hEq
          simpa using! congrArg Prod.snd this
      · intro p hp
        rcases Finset.mem_offDiag.1 hp with ⟨hi, hj, hij⟩
        exact Finset.mem_offDiag.2 ⟨hj, hi, Ne.symm hij⟩
      · intro p hp
        rfl
    have hdiag0 : ∑ p ∈ s.diag, F p = 0 := by
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have hpEq : p.1 = p.2 := (Finset.mem_diag.1 hp).2
      cases p with
      | mk i j =>
        have hij : i = j := by simpa using! hpEq
        subst hij
        simp [F, c2, g2, hg2_diag]
    have hprod :
        (∑ i : Fin 24, ∑ j : Fin 24, c2 i * c2 j * g2 i j) = ∑ p ∈ s ×ˢ s, F p := by
      simpa [s, F, c2, g2] using!
        (Finset.sum_product (s := s) (t := s) (f := fun p : Fin 24 × Fin 24 => F p)).symm
    have hsplit :
        (∑ p ∈ s ×ˢ s, F p) = (∑ p ∈ s.diag, F p) + ∑ p ∈ s.offDiag, F p := by
      have hU : s.diag ∪ s.offDiag = s ×ˢ s :=
        Finset.diag_union_offDiag (s := s)
      have hdisj : Disjoint s.diag s.offDiag := Finset.disjoint_diag_offDiag (s := s)
      -- rewrite the product sum as a sum over the disjoint union `diag ∪ offDiag`
      rw [hU.symm]
      simpa using! (Finset.sum_union hdisj (f := F))
    have hsum0 : (∑ i : Fin 24, ∑ j : Fin 24, c2 i * c2 j * g2 i j) = 0 := by
      calc
        (∑ i : Fin 24, ∑ j : Fin 24, c2 i * c2 j * g2 i j) = ∑ p ∈ s ×ˢ s, F p := hprod
        _ = (∑ p ∈ s.diag, F p) + ∑ p ∈ s.offDiag, F p := hsplit
        _ = 0 := by simp [hdiag0, hoff]
    have hS0 : (S : ZMod 2) = 0 := by
      simp [S, c2, g2, Int.cast_sum, Int.cast_mul, hsum0]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd S 2).1 hS0
  rcases hS_even with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  calc
    combInt c ⬝ᵥ combInt c = 8 * S := hdot
    _ = 8 * (2 * t) := by simp [ht]
    _ = 16 * t := by ring

end LeechNorm

/-- Evenness: squared norms are even integers (`(v,v) ∈ 2ℤ`). -/
theorem leech_norm_sq_eq_two_mul (v : ℝ²⁴) (hv : v ∈ LeechLattice) :
    ∃ n : ℕ, ‖v‖ ^ 2 = (2 : ℝ) * n := by
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := leechGeneratorRows) (x := v)).1 hv
    with ⟨c, rfl⟩
  have hvR :
      (∑ i : Fin 24, c i • leechGeneratorRows i) =
        ∑ i : Fin 24, (c i : ℝ) • leechGeneratorRows i := by
    simp [Int.cast_smul_eq_zsmul]
  have hvEq :
      (∑ i : Fin 24, c i • leechGeneratorRows i) =
        ((Real.sqrt 8)⁻¹ : ℝ) • LeechNorm.combReal c := by
    calc
      (∑ i : Fin 24, c i • leechGeneratorRows i)
          = ∑ i : Fin 24, (c i : ℝ) • leechGeneratorRows i := hvR
      _ = ((Real.sqrt 8)⁻¹ : ℝ) • LeechNorm.combReal c := by
            simpa using! LeechNorm.sum_smul_leechGeneratorRows_eq_smul_combReal c
  have hnorm_smul (r : ℝ) (x : ℝ²⁴) : ‖r • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖r • x‖ ^ 2 = (‖r‖ * ‖x‖) ^ 2 := by simp [norm_smul]
      _ = ‖r‖ ^ 2 * ‖x‖ ^ 2 := by simpa using! (mul_pow ‖r‖ ‖x‖ 2)
      _ = r ^ 2 * ‖x‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  have hnorm :
      ‖∑ i : Fin 24, c i • leechGeneratorRows i‖ ^ 2 =
        ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 * ‖LeechNorm.combReal c‖ ^ 2 := by
    simpa [hvEq] using! hnorm_smul ((Real.sqrt 8)⁻¹ : ℝ) (LeechNorm.combReal c)
  rcases (LeechNorm.combInt_dot_divisible_by_16 c) with ⟨m, hm⟩
  have hcomb : ‖LeechNorm.combReal c‖ ^ 2 = (16 : ℝ) * (m : ℝ) := by
    have hsq :
        ‖LeechNorm.combReal c‖ ^ 2 =
          ((LeechNorm.combInt c ⬝ᵥ LeechNorm.combInt c : ℤ) : ℝ) :=
      LeechNorm.combReal_norm_sq c
    have hmR :
        ((LeechNorm.combInt c ⬝ᵥ LeechNorm.combInt c : ℤ) : ℝ) = (16 : ℝ) * (m : ℝ) := by
      have hm' := congrArg (fun z : ℤ => (z : ℝ)) hm
      simpa [Int.cast_mul, Int.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using! hm'
    simpa [hmR] using! hsq
  have hsqrt8 : ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 = (1 / 8 : ℝ) := by
    norm_num
  have hmain : ‖∑ i : Fin 24, c i • leechGeneratorRows i‖ ^ 2 = (2 : ℝ) * (m : ℝ) := by
    have : ‖∑ i : Fin 24, c i • leechGeneratorRows i‖ ^ 2 =
        ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 * ((16 : ℝ) * (m : ℝ)) := by
      simpa [hcomb, mul_assoc] using! congrArg (fun t => t) hnorm
    calc
      ‖∑ i : Fin 24, c i • leechGeneratorRows i‖ ^ 2
          = ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 * ((16 : ℝ) * (m : ℝ)) := this
      _ = (1 / 8 : ℝ) * ((16 : ℝ) * (m : ℝ)) := by simp [hsqrt8]
      _ = (2 : ℝ) * (m : ℝ) := by ring
  have hm_nonneg : (0 : ℤ) ≤ m := by
    have hsq : (0 : ℝ) ≤ ‖LeechNorm.combReal c‖ ^ 2 := sq_nonneg _
    have hsq' : (0 : ℝ) ≤ (16 : ℝ) * (m : ℝ) := by simpa [hcomb] using! hsq
    have hmR : (0 : ℝ) ≤ (m : ℝ) :=
      nonneg_of_mul_nonneg_right hsq' (by norm_num : (0 : ℝ) < (16 : ℝ))
    exact_mod_cast hmR
  refine ⟨Int.toNat m, ?_⟩
  have hmNat : (m : ℝ) = (Int.toNat m : ℝ) := by
    have hmInt : (Int.ofNat (Int.toNat m)) = m := Int.toNat_of_nonneg hm_nonneg
    have hmR : (Int.toNat m : ℝ) = (m : ℝ) := by exact_mod_cast hmInt
    simpa using! hmR.symm
  simpa [hmNat] using! hmain


def leechParityVec (i : Fin 24) : (Fin 24 → ZMod 2) :=
  if i = (23 : Fin 24) then
    fun j : Fin 24 => (leechMatrixInt i j : ZMod 2)
  else
    fun j : Fin 24 => ((leechMatrixInt i j / 2 : ℤ) : ZMod 2)

def leechParityBasisIdx : Fin 12 → Fin 24
  := ![
    ⟨23, by decide⟩, ⟨22, by decide⟩, ⟨21, by decide⟩, ⟨20, by decide⟩,
    ⟨19, by decide⟩, ⟨18, by decide⟩, ⟨17, by decide⟩, ⟨15, by decide⟩,
    ⟨14, by decide⟩, ⟨13, by decide⟩, ⟨11, by decide⟩, ⟨7, by decide⟩
  ]

def leechParityBasisVec (t : Fin 12) : (Fin 24 → ZMod 2) :=
  leechParityVec (leechParityBasisIdx t)

def leechParityWeight (w : Fin 24 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun j : Fin 24 => w j ≠ 0).card

/-!
For the minimum-weight computation we switch to an explicit `BitVec` representation of the
12-generator binary code spanned by `leechParityBasisVec`.

The constants below were obtained by evaluating the 12 vectors `leechParityBasisVec t` and encoding
them as `BitVec 24` (bit `k` is `1` iff the coordinate `k` is nonzero in `ZMod 2`).
-/

def leechParityBasisMask : Fin 12 → Nat
  := ![
    16777215, 5592320, 3355392, 1118494, 592211, 329017,
    197525, 39321, 21845, 13107, 3855, 255
  ]

def leechParityBasisBit (t : Fin 12) (k : Fin 24) : Bool :=
  Nat.testBit (leechParityBasisMask t) k.1

structure Coeff12 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b9 : Bool
  b10 : Bool
  b11 : Bool
deriving DecidableEq

def Coeff12.get (c : Coeff12) : Fin 12 → Bool
  | ⟨0, _⟩ => c.b0
  | ⟨1, _⟩ => c.b1
  | ⟨2, _⟩ => c.b2
  | ⟨3, _⟩ => c.b3
  | ⟨4, _⟩ => c.b4
  | ⟨5, _⟩ => c.b5
  | ⟨6, _⟩ => c.b6
  | ⟨7, _⟩ => c.b7
  | ⟨8, _⟩ => c.b8
  | ⟨9, _⟩ => c.b9
  | ⟨10, _⟩ => c.b10
  | ⟨11, _⟩ => c.b11

def Coeff12.ofFun (f : Fin 12 → Bool) : Coeff12 where
  b0 := f 0
  b1 := f 1
  b2 := f 2
  b3 := f 3
  b4 := f 4
  b5 := f 5
  b6 := f 6
  b7 := f 7
  b8 := f 8
  b9 := f 9
  b10 := f 10
  b11 := f 11

@[simp]
lemma Coeff12.get_ofFun (f : Fin 12 → Bool) (t : Fin 12) :
    Coeff12.get (Coeff12.ofFun f) t = f t := by
  fin_cases t <;> rfl

@[simp]
lemma Coeff12.ofFun_get (c : Coeff12) : Coeff12.ofFun (Coeff12.get c) = c := by
  cases c
  rfl

def Coeff12.equivFun : Coeff12 ≃ (Fin 12 → Bool) where
  toFun := Coeff12.get
  invFun := Coeff12.ofFun
  left_inv := Coeff12.ofFun_get
  right_inv := by
    intro f
    funext t
    simp

instance : Fintype Coeff12 :=
  Fintype.ofEquiv (Fin 12 → Bool) Coeff12.equivFun.symm

def coeff12ToNat (c : Coeff12) : Nat :=
  Nat.ofBits (Coeff12.get c)

lemma coeff12ToNat_lt_4096 (c : Coeff12) : coeff12ToNat c < 4096 := by
  -- `coeff12ToNat` is a 12-bit number, hence `< 2^12 = 4096`.
  simpa [coeff12ToNat] using! (Nat.ofBits_lt_two_pow (f := Coeff12.get c) (n := 12))

def coeff12ToFin (c : Coeff12) : Fin 4096 :=
  ⟨coeff12ToNat c, coeff12ToNat_lt_4096 c⟩

def coeff12OfFin (n : Fin 4096) : Coeff12 where
  b0 := Nat.testBit n.1 0
  b1 := Nat.testBit n.1 1
  b2 := Nat.testBit n.1 2
  b3 := Nat.testBit n.1 3
  b4 := Nat.testBit n.1 4
  b5 := Nat.testBit n.1 5
  b6 := Nat.testBit n.1 6
  b7 := Nat.testBit n.1 7
  b8 := Nat.testBit n.1 8
  b9 := Nat.testBit n.1 9
  b10 := Nat.testBit n.1 10
  b11 := Nat.testBit n.1 11

lemma coeff12OfFin_toFin (c : Coeff12) : coeff12OfFin (coeff12ToFin c) = c := by
  -- Compare via the equivalence `Coeff12 ≃ (Fin 12 → Bool)`.
  have hinj : Function.Injective Coeff12.equivFun := Coeff12.equivFun.injective
  apply hinj
  funext t
  have hget :
      Coeff12.equivFun (coeff12OfFin (coeff12ToFin c)) t = Nat.testBit (coeff12ToNat c) t.1 := by
    fin_cases t <;> rfl
  -- Rewrite the `t`-th bit of `coeff12ToNat c = Nat.ofBits (Coeff12.get c)`.
  rw [hget]
  simp [Coeff12.equivFun, coeff12ToNat,
    Nat.testBit_ofBits_lt (f := Coeff12.get c) (i := t.1) (h := t.2)]

def coeff12OfFun (c12 : Fin 12 → ZMod 2) : Coeff12 where
  b0 := decide (c12 0 ≠ 0)
  b1 := decide (c12 1 ≠ 0)
  b2 := decide (c12 2 ≠ 0)
  b3 := decide (c12 3 ≠ 0)
  b4 := decide (c12 4 ≠ 0)
  b5 := decide (c12 5 ≠ 0)
  b6 := decide (c12 6 ≠ 0)
  b7 := decide (c12 7 ≠ 0)
  b8 := decide (c12 8 ≠ 0)
  b9 := decide (c12 9 ≠ 0)
  b10 := decide (c12 10 ≠ 0)
  b11 := decide (c12 11 ≠ 0)

lemma coeff12OfFun_get (c12 : Fin 12 → ZMod 2) (t : Fin 12) :
    (Coeff12.get (coeff12OfFun c12) t) = decide (c12 t ≠ 0) := by
  fin_cases t <;> rfl

local instance : Std.Commutative xor :=
  ⟨Bool.xor_comm⟩

local instance : Std.Associative xor :=
  ⟨Bool.xor_assoc⟩

local instance : Std.Commutative Nat.xor :=
  ⟨Nat.xor_comm⟩

local instance : Std.Associative Nat.xor :=
  ⟨Nat.xor_assoc⟩

lemma testBit_fold_xor (s : Finset (Fin 12)) (f : Fin 12 → Nat) (n : Nat) :
    Nat.testBit (Finset.fold Nat.xor 0 f s) n =
      Finset.fold xor false (fun t : Fin 12 => Nat.testBit (f t) n) s := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    -- Expand both folds at the inserted element, then use `Nat.testBit_xor`.
    simp only [ha, not_false_eq_true, Finset.fold_insert]
    change ((f a) ^^^ (Finset.fold Nat.xor 0 f s)).testBit n =
      ((f a).testBit n ^^ Finset.fold xor false (fun t => (f t).testBit n) s)
    simp [hs, Nat.testBit_xor (f a) (Finset.fold Nat.xor 0 f s) n]

lemma testBit_ite (b : Bool) (m n : Nat) :
    Nat.testBit (if b then m else 0) n = (b && Nat.testBit m n) := by
  cases b <;> simp [Nat.testBit]

def codewordBit (c : Coeff12) (k : Fin 24) : Bool :=
  Fin.foldl 12 (fun acc (t : Fin 12) => xor acc (Coeff12.get c t && leechParityBasisBit t k)) false

lemma leechParityBasisMask_spec (t : Fin 12) (k : Fin 24) :
    (if leechParityBasisBit t k then (1 : ZMod 2) else 0) = leechParityBasisVec t k := by
  fin_cases t <;> fin_cases k <;> decide

lemma leechParityBasisVec_apply (t : Fin 12) (k : Fin 24) :
    leechParityBasisVec t k = (if leechParityBasisBit t k then (1 : ZMod 2) else 0) := by
  simpa using! (leechParityBasisMask_spec t k).symm

def codewordMask : Coeff12 → Nat
  | ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ =>
      (if b0 then leechParityBasisMask ⟨0, by decide⟩ else 0) ^^^
      (if b1 then leechParityBasisMask ⟨1, by decide⟩ else 0) ^^^
      (if b2 then leechParityBasisMask ⟨2, by decide⟩ else 0) ^^^
      (if b3 then leechParityBasisMask ⟨3, by decide⟩ else 0) ^^^
      (if b4 then leechParityBasisMask ⟨4, by decide⟩ else 0) ^^^
      (if b5 then leechParityBasisMask ⟨5, by decide⟩ else 0) ^^^
      (if b6 then leechParityBasisMask ⟨6, by decide⟩ else 0) ^^^
      (if b7 then leechParityBasisMask ⟨7, by decide⟩ else 0) ^^^
      (if b8 then leechParityBasisMask ⟨8, by decide⟩ else 0) ^^^
      (if b9 then leechParityBasisMask ⟨9, by decide⟩ else 0) ^^^
      (if b10 then leechParityBasisMask ⟨10, by decide⟩ else 0) ^^^
      (if b11 then leechParityBasisMask ⟨11, by decide⟩ else 0)

private def codewordMaskFold (c : Coeff12) : Nat :=
  Fin.foldl 12
    (fun acc (t : Fin 12) =>
      acc ^^^ (if Coeff12.get c t then leechParityBasisMask t else 0))
    0

private lemma codewordMask_eq_codewordMaskFold (c : Coeff12) :
    codewordMask c = codewordMaskFold c := by
  cases c with
  | mk b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
    simp [codewordMaskFold, codewordMask, Coeff12.get, Fin.foldl_succ, Fin.foldl_zero]
    rfl

lemma testBit_foldl_xor_init (n : Nat) (f : Fin n → Nat) (init bit : Nat) :
    Nat.testBit (Fin.foldl n (fun acc (t : Fin n) => acc ^^^ f t) init) bit =
      Fin.foldl n (fun acc (t : Fin n) => xor acc (Nat.testBit (f t) bit))
        (Nat.testBit init bit) := by
  induction n generalizing init bit with
  | zero =>
      simp [Fin.foldl_zero]
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, Fin.foldl_succ, Nat.testBit_xor] using!
        (ih (f := fun t : Fin n => f t.succ) (init := init ^^^ f 0) (bit := bit))

lemma testBit_foldl_xor (n : Nat) (f : Fin n → Nat) (bit : Nat) :
    Nat.testBit (Fin.foldl n (fun acc (t : Fin n) => acc ^^^ f t) 0) bit =
      Fin.foldl n (fun acc (t : Fin n) => xor acc (Nat.testBit (f t) bit)) false := by
  simpa using! (testBit_foldl_xor_init n f 0 bit)

lemma codewordBit_eq_testBit_codewordMask (c : Coeff12) (k : Fin 24) :
    codewordBit c k = Nat.testBit (codewordMask c) k.1 := by
  have htb :
      Nat.testBit (codewordMask c) k.1 =
        Fin.foldl 12
          (fun acc (t : Fin 12) =>
            xor acc (Nat.testBit (if Coeff12.get c t then leechParityBasisMask t else 0) k.1))
          false := by
    -- Rewrite `codewordMask c` to the fold form and apply `testBit_foldl_xor`.
    simpa [codewordMask_eq_codewordMaskFold (c := c), codewordMaskFold] using!
      (testBit_foldl_xor (n := 12)
        (f := fun t : Fin 12 => if Coeff12.get c t then leechParityBasisMask t else 0) (bit := k.1))
  -- Simplify the `testBit` of an `if` and identify the remaining fold with `codewordBit`.
  simp [codewordBit, leechParityBasisBit, testBit_ite, htb]

def weightMask (m : Nat) : Nat :=
  ∑ k : Fin 24, Bool.toNat (Nat.testBit m k.1)

lemma weightMask_eq_card (m : Nat) :
    weightMask m = (Finset.univ.filter fun k : Fin 24 => Nat.testBit m k.1 = true).card := by
  let p : Fin 24 → Prop := fun k => Nat.testBit m k.1 = true
  have htoNat : ∀ k : Fin 24, Bool.toNat (Nat.testBit m k.1) = (if p k then 1 else 0) := by
    intro k
    dsimp [p]
    cases h : Nat.testBit m k.1 <;> rfl
  calc
    weightMask m = ∑ k : Fin 24, Bool.toNat (Nat.testBit m k.1) := by simp [weightMask]
    _ = ∑ k : Fin 24, if p k then 1 else 0 :=
      Finset.sum_congr rfl (fun k _ => htoNat k)
    _ = (Finset.univ.filter p).card :=
      (Finset.sum_boole (R := Nat) p (Finset.univ : Finset (Fin 24)))
    _ = (Finset.univ.filter fun k : Fin 24 => Nat.testBit m k.1 = true).card := by rfl

def leechParityVecCoeffMask (i : Fin 24) : Nat :=
  match i.1 with
  | 7 => 2048
  | 11 => 1024
  | 13 => 512
  | 14 => 256
  | 15 => 128
  | 17 => 64
  | 18 => 32
  | 19 => 16
  | 20 => 8
  | 21 => 4
  | 22 => 2
  | 23 => 1
  | _ => 0

def leechParityVecCoeff (i : Fin 24) (t : Fin 12) : ZMod 2 :=
  if Nat.testBit (leechParityVecCoeffMask i) t.1 then 1 else 0

lemma leechParityVec_mem_span_basis (i : Fin 24) :
    ∃ c : (Fin 12 → ZMod 2), ∑ t : Fin 12, c t • leechParityBasisVec t = leechParityVec i := by
  refine ⟨leechParityVecCoeff i, by
    ext k
    fin_cases i <;> fin_cases k <;> decide⟩

def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0

lemma boolToZMod2_xor (a b : Bool) :
    boolToZMod2 (xor a b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

lemma boolToZMod2_and (a b : Bool) :
    boolToZMod2 (a && b) = boolToZMod2 a * boolToZMod2 b := by
  cases a <;> cases b <;> decide

lemma boolToZMod2_decide_ne_zero (x : ZMod 2) :
    boolToZMod2 (decide (x ≠ 0)) = x := by
  revert x
  decide

def codewordZMod2 (c : Coeff12) : Fin 24 → ZMod 2 :=
  fun k : Fin 24 => boolToZMod2 (codewordBit c k)

lemma sum_boolToZMod2_eq_fold_xor (s : Finset (Fin 12)) (f : Fin 12 → Bool) :
    (Finset.sum s (fun t : Fin 12 => boolToZMod2 (f t))) =
      boolToZMod2 (Finset.fold xor false f s) := by
  refine Finset.induction_on s (by simp [boolToZMod2]) ?_
  intro a s ha hs
  simp [Finset.sum_insert, ha, Finset.fold_insert, hs, boolToZMod2_xor]

lemma foldl_xor_init (n : Nat) (f : Fin n → Bool) (b : Bool) :
    Fin.foldl n (fun acc (t : Fin n) => xor acc (f t)) b =
      xor b (Fin.foldl n (fun acc (t : Fin n) => xor acc (f t)) false) := by
  simpa using! (Fin.foldl_assoc (n := n) (op := xor) (f := f) (a₁ := b) (a₂ := false))

lemma sum_boolToZMod2_eq_foldl_xor (n : Nat) (f : Fin n → Bool) :
    (∑ t : Fin n, boolToZMod2 (f t)) =
      boolToZMod2 (Fin.foldl n (fun acc (t : Fin n) => xor acc (f t)) false) := by
  induction n with
  | zero =>
      simp [Fin.foldl_zero, boolToZMod2]
  | succ n ih =>
      have hsum :
          (∑ t : Fin (n + 1), boolToZMod2 (f t)) =
            boolToZMod2 (f 0) + ∑ t : Fin n, boolToZMod2 (f t.succ) := by
        simpa [Nat.succ_eq_add_one] using!
          (Fin.sum_univ_succ (f := fun t : Fin (n + 1) => boolToZMod2 (f t)))
      have hfold :
          Fin.foldl (n + 1) (fun acc (t : Fin (n + 1)) => xor acc (f t)) false =
            xor (f 0) (Fin.foldl n (fun acc (t : Fin n) => xor acc (f t.succ)) false) := by
        have hstep :
            Fin.foldl (n + 1) (fun acc (t : Fin (n + 1)) => xor acc (f t)) false =
              Fin.foldl n (fun acc (t : Fin n) => xor acc (f t.succ)) (f 0) := by
          simpa [Nat.succ_eq_add_one] using!
            (Fin.foldl_succ (f := fun acc (t : Fin (n + 1)) => xor acc (f t)) false)
        have hinit :
            Fin.foldl n (fun acc (t : Fin n) => xor acc (f t.succ)) (f 0) =
              xor (f 0) (Fin.foldl n (fun acc (t : Fin n) => xor acc (f t.succ)) false) :=
          foldl_xor_init (n := n) (f := fun t : Fin n => f t.succ) (b := f 0)
        exact hstep.trans hinit
      calc
        (∑ t : Fin (n + 1), boolToZMod2 (f t)) =
            boolToZMod2 (f 0) + ∑ t : Fin n, boolToZMod2 (f t.succ) := hsum
        _ =
            boolToZMod2 (f 0) +
              boolToZMod2
                (Fin.foldl n (fun acc (t : Fin n) => xor acc (f t.succ)) false) := by
            simp [ih (f := fun t : Fin n => f t.succ)]
        _ =
            boolToZMod2
              (xor (f 0) (Fin.foldl n (fun acc (t : Fin n) => xor acc (f t.succ)) false)) := by
            simp [boolToZMod2_xor]
        _ = boolToZMod2 (Fin.foldl (n + 1) (fun acc (t : Fin (n + 1)) => xor acc (f t)) false) := by
            simp [hfold]

lemma boolToZMod2_ne_zero_iff (b : Bool) : boolToZMod2 b ≠ (0 : ZMod 2) ↔ b = true := by
  cases b <;> decide

lemma codewordBit_spec_zmod (c12 : Fin 12 → ZMod 2) (k : Fin 24) :
    (∑ t : Fin 12, c12 t • leechParityBasisVec t) k =
      boolToZMod2 (codewordBit (coeff12OfFun c12) k) := by
  have hterm (t : Fin 12) :
      c12 t • leechParityBasisVec t k =
        boolToZMod2 ((Coeff12.get (coeff12OfFun c12) t) && leechParityBasisBit t k) := by
    cases h : leechParityBasisBit t k with
    | false =>
        simp [leechParityBasisVec_apply, h, coeff12OfFun_get, boolToZMod2, smul_eq_mul]
    | true =>
        have hdec : c12 t = boolToZMod2 (decide (c12 t ≠ 0)) := by
          simpa using! (boolToZMod2_decide_ne_zero (x := c12 t)).symm
        simpa [leechParityBasisVec_apply, h, coeff12OfFun_get, boolToZMod2, smul_eq_mul] using! hdec
  calc
    (∑ t : Fin 12, c12 t • leechParityBasisVec t) k =
        ∑ t : Fin 12, c12 t • leechParityBasisVec t k := by
          simp [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ t : Fin 12,
          boolToZMod2 ((Coeff12.get (coeff12OfFun c12) t) && leechParityBasisBit t k) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          simpa using! hterm t
    _ = boolToZMod2 (codewordBit (coeff12OfFun c12) k) := by
          simpa [codewordBit] using!
            (sum_boolToZMod2_eq_foldl_xor (n := 12)
              (f := fun t : Fin 12 =>
                (Coeff12.get (coeff12OfFun c12) t) && leechParityBasisBit t k))

-- Minimum weight computation for the parity-check code generated by `leechParityBasisMask`.
-- We prove it by verified brute-force enumeration. To avoid recursion-depth and heartbeat
-- issues, we split on the first three coefficient bits and let `decide` enumerate the
-- remaining nine bits (512 cases) in each separate declaration.

lemma leechParityWeight_codewordMask_ge_8_000 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨false, false, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨false, false, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_001 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨false, false, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨false, false, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_010 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨false, true, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨false, true, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_011 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨false, true, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨false, true, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_100 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨true, false, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨true, false, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_101 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨true, false, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨true, false, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_110 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨true, true, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤
          weightMask
            (codewordMask ⟨true, true, false, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8_111 :
    ∀ b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
      codewordMask ⟨true, true, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ ≠ 0 →
        8 ≤ weightMask (codewordMask ⟨true, true, true, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩) := by
  decide

lemma leechParityWeight_codewordMask_ge_8 :
    ∀ c : Coeff12, codewordMask c ≠ 0 → 8 ≤ weightMask (codewordMask c) := by
  intro c hc
  cases c with
  | mk b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
    cases b0 <;> cases b1 <;> cases b2
    · exact leechParityWeight_codewordMask_ge_8_000 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_001 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_010 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_011 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_100 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_101 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_110 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc
    · exact leechParityWeight_codewordMask_ge_8_111 b3 b4 b5 b6 b7 b8 b9 b10 b11 hc

lemma codewordMask_ne_zero_of_exists_codewordBit (c : Coeff12)
    (h : ∃ k : Fin 24, codewordBit c k = true) : codewordMask c ≠ 0 := by
  rcases h with ⟨k, hk⟩
  intro h0
  have htb : Nat.testBit (codewordMask c) k.1 = true := by
    simpa [codewordBit_eq_testBit_codewordMask] using! hk
  have htb0 := htb
  simp [h0] at htb0

lemma leechParityWeight_codewordZMod2_eq_weightMask (c : Coeff12) :
    leechParityWeight (codewordZMod2 c) = weightMask (codewordMask c) := by
  calc
    leechParityWeight (codewordZMod2 c) =
        (Finset.univ.filter fun k : Fin 24 => Nat.testBit (codewordMask c) k.1 = true).card := by
          simp [leechParityWeight, codewordZMod2, boolToZMod2, codewordBit_eq_testBit_codewordMask]
    _ = weightMask (codewordMask c) := by
          simpa using! (weightMask_eq_card (m := codewordMask c)).symm

lemma leechParityWeight_codewordZMod2_ge_8 (c : Coeff12)
    (h : ∃ k : Fin 24, codewordBit c k = true) : 8 ≤ leechParityWeight (codewordZMod2 c) := by
  have hmask_ne0 : codewordMask c ≠ 0 := codewordMask_ne_zero_of_exists_codewordBit c h
  have hw : 8 ≤ weightMask (codewordMask c) := leechParityWeight_codewordMask_ge_8 c hmask_ne0
  simpa [leechParityWeight_codewordZMod2_eq_weightMask (c := c)] using! hw

private lemma exists_ne_zero_of_ne_zero_fun {α : Type} {β : Type} [Zero β] {f : α → β}
    (hf : f ≠ 0) :
    ∃ a, f a ≠ 0 := by
  by_contra h
  apply hf
  funext a
  by_contra ha
  exact h ⟨a, ha⟩

lemma leechParityWeight_ge_8_of_mem_span (w : Fin 24 → ZMod 2)
    (hw : w ∈ Submodule.span (ZMod 2) (Set.range leechParityBasisVec)) (hw0 : w ≠ 0) :
    8 ≤ leechParityWeight w := by
  rcases
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := leechParityBasisVec) (x := w)).1
        hw with ⟨c12, rfl⟩
  let cB : Coeff12 := coeff12OfFun c12
  have hw_eq : (∑ t : Fin 12, c12 t • leechParityBasisVec t) = codewordZMod2 cB := by
    ext k
    simpa [codewordZMod2, cB] using! (codewordBit_spec_zmod (c12 := c12) (k := k))
  have hnonzero_sum : ∃ k : Fin 24, (∑ t : Fin 12, c12 t • leechParityBasisVec t) k ≠ 0 :=
    exists_ne_zero_of_ne_zero_fun hw0
  rcases hnonzero_sum with ⟨k, hk⟩
  have hkZ : (codewordZMod2 cB) k ≠ 0 :=
    Ne.symm (Ne.trans_eq (id (Ne.symm hk)) (congrFun hw_eq k))
  have hk' : boolToZMod2 (codewordBit cB k) ≠ (0 : ZMod 2) := by
    simpa [codewordZMod2] using! hkZ
  have hcw : ∃ k : Fin 24, codewordBit cB k = true := ⟨k, (boolToZMod2_ne_zero_iff _).1 hk'⟩
  have : 8 ≤ leechParityWeight (codewordZMod2 cB) :=
    leechParityWeight_codewordZMod2_ge_8 (c := cB) hcw
  simpa [hw_eq] using! this

private lemma one_le_sq_of_int_ne0 (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
  have habs_int : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have habs_real : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℝ) ≤ (|z| : ℝ) := by exact_mod_cast habs_int
    simpa [Int.cast_abs] using! this
  exact (one_le_sq_iff_one_le_abs (z : ℝ)).2 habs_real

lemma leech_no_norm_sq_two_contra_w_ne0
    (yZ : Fin 24 → ℤ) (hyZdot : (yZ ⬝ᵥ yZ : ℤ) = 4)
    (hw_mem :
      (fun k : Fin 24 => (yZ k : ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range leechParityBasisVec))
    (hw0 : (fun k : Fin 24 => (yZ k : ZMod 2)) ≠ 0) :
    False := by
  let w : Fin 24 → ZMod 2 := fun k : Fin 24 => (yZ k : ZMod 2)
  have hwgt : 8 ≤ leechParityWeight w := leechParityWeight_ge_8_of_mem_span w hw_mem (by
    simpa [w] using! hw0)
  have hyZsq_eq : (∑ k : Fin 24, (yZ k : ℝ) ^ 2) = (4 : ℝ) := by
    have : ((yZ ⬝ᵥ yZ : ℤ) : ℝ) = (4 : ℝ) := by exact_mod_cast hyZdot
    simpa [dotProduct, pow_two, Int.cast_sum, Int.cast_mul] using! this
  have hsum_ge : (leechParityWeight w : ℝ) ≤ ∑ k : Fin 24, (yZ k : ℝ) ^ 2 := by
    let s : Finset (Fin 24) := Finset.univ.filter fun k : Fin 24 => w k ≠ 0
    have hs : (leechParityWeight w : ℝ) = Finset.sum s (fun _k : Fin 24 => (1 : ℝ)) := by
      have hs' : (leechParityWeight w : ℝ) = (s.card : ℝ) := by simp [leechParityWeight, s]
      have hsum : (s.card : ℝ) = Finset.sum s (fun _k : Fin 24 => (1 : ℝ)) := by
        rw [Finset.sum_const]
        simp
      exact hs'.trans hsum
    have hterm : ∀ k : Fin 24, w k ≠ 0 → (1 : ℝ) ≤ (yZ k : ℝ) ^ 2 := by
      intro k hk
      have hy_ne0 : yZ k ≠ 0 := by
        intro h0'
        exact hk (by simp [w, h0'])
      exact one_le_sq_of_int_ne0 (z := yZ k) hy_ne0
    have hle_s :
        Finset.sum s (fun _k : Fin 24 => (1 : ℝ))
          ≤ Finset.sum s (fun k : Fin 24 => (yZ k : ℝ) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk' : w k ≠ 0 := (Finset.mem_filter.1 hk).2
      exact hterm k hk'
    have hsub : s ⊆ (Finset.univ : Finset (Fin 24)) := Finset.filter_subset _ _
    have hle_univ :
        (Finset.sum s (fun k : Fin 24 => (yZ k : ℝ) ^ 2)) ≤ ∑ k : Fin 24, (yZ k : ℝ) ^ 2 := by
      simpa using!
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro k _ hk
          exact sq_nonneg (yZ k : ℝ)))
    calc
      (leechParityWeight w : ℝ) = Finset.sum s (fun _k : Fin 24 => (1 : ℝ)) := hs
      _ ≤ Finset.sum s (fun k : Fin 24 => (yZ k : ℝ) ^ 2) := hle_s
      _ ≤ ∑ k : Fin 24, (yZ k : ℝ) ^ 2 := hle_univ
  have : (8 : ℝ) ≤ ∑ k : Fin 24, (yZ k : ℝ) ^ 2 :=
    le_trans (by exact_mod_cast hwgt) hsum_ge
  linarith [hyZsq_eq, this]

lemma leech_no_norm_sq_two_contra_w_eq0 (c yZ : Fin 24 → ℤ)
    (hxZ_eq_two_mul_yZ : ∀ k : Fin 24, LeechNorm.combInt c k = 2 * yZ k)
    (hyZdot : (yZ ⬝ᵥ yZ : ℤ) = 4)
    (hcLast_even : (2 : ℤ) ∣ c (23 : Fin 24))
    (hw0 : (fun k : Fin 24 => (yZ k : ZMod 2)) = 0) :
    False := by
  let last : Fin 24 := 23
  let xZ : Fin 24 → ℤ := LeechNorm.combInt c
  have hxZ_eq_two_mul_yZ' : ∀ k : Fin 24, xZ k = 2 * yZ k := by
    intro k
    simpa [xZ] using! hxZ_eq_two_mul_yZ k
  have hcLast_even' : (2 : ℤ) ∣ c last := by
    simpa [last] using! hcLast_even
  let w : Fin 24 → ZMod 2 := fun k : Fin 24 => (yZ k : ZMod 2)
  have hw0' : w = 0 := by simpa [w] using! hw0
  have hy_even : ∀ k : Fin 24, (2 : ℤ) ∣ yZ k := by
    intro k
    have : (w k) = 0 := by simp [hw0']
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (yZ k) 2).1 this
  let zZ : Fin 24 → ℤ := fun k : Fin 24 => yZ k / 2
  have hyZ_eq_two_mul_zZ : ∀ k : Fin 24, yZ k = 2 * zZ k :=
    fun k => Eq.symm (Int.mul_ediv_cancel' (hy_even k))
  have hxZ_eq_four_mul_zZ : ∀ k : Fin 24, xZ k = 4 * zZ k := by
    intro k
    calc
      xZ k = 2 * yZ k := hxZ_eq_two_mul_yZ' k
      _ = 2 * (2 * zZ k) := by simp [hyZ_eq_two_mul_zZ k]
      _ = 4 * zZ k := by ring
  have hzZdot : (zZ ⬝ᵥ zZ : ℤ) = 1 := by
    have hyZdot_eq : (yZ ⬝ᵥ yZ : ℤ) = 4 * (zZ ⬝ᵥ zZ : ℤ) := by
      have : (yZ ⬝ᵥ yZ : ℤ) = ∑ k : Fin 24, (2 * zZ k) * (2 * zZ k) := by
        simp [dotProduct, hyZ_eq_two_mul_zZ]
      calc
        (yZ ⬝ᵥ yZ : ℤ) = ∑ k : Fin 24, (2 * zZ k) * (2 * zZ k) := this
        _ = ∑ k : Fin 24, 4 * (zZ k * zZ k) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              ring
        _ = 4 * (∑ k : Fin 24, zZ k * zZ k) := by
              simp [Finset.mul_sum]
        _ = 4 * (zZ ⬝ᵥ zZ : ℤ) := by simp [dotProduct]
    linarith
  -- `8 ∣ ∑ xZ` since `c last` is even and all non-last row sums are multiples of 8.
  let rowSum : Fin 24 → ℤ := fun i : Fin 24 => ∑ k : Fin 24, leechMatrixInt i k
  have hrowSum8 : ∀ i : Fin 24, i ≠ last → (8 : ℤ) ∣ rowSum i := by
    intro i hi
    fin_cases i <;> (try (cases hi rfl)) <;> decide
  have hrowSum_last : rowSum last = 20 := by
    have : rowSum (23 : Fin 24) = 20 := by decide
    simpa [last] using! this
  have hxZ_sum : (∑ k : Fin 24, xZ k) = ∑ i : Fin 24, c i * rowSum i := by
    calc
      (∑ k : Fin 24, xZ k) =
          ∑ k : Fin 24, ∑ i : Fin 24, c i * leechMatrixInt i k := by
            simp [xZ, LeechNorm.combInt, LeechNorm.rowInt]
      _ = ∑ i : Fin 24, ∑ k : Fin 24, c i * leechMatrixInt i k :=
            Finset.sum_comm
      _ = ∑ i : Fin 24, c i * ∑ k : Fin 24, leechMatrixInt i k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simpa [rowSum] using!
              (Finset.mul_sum (a := c i) (s := (Finset.univ : Finset (Fin 24)))
                (f := fun k : Fin 24 => leechMatrixInt i k)).symm
      _ = ∑ i : Fin 24, c i * rowSum i := by rfl
  have hxZ_sum_dvd8 : (8 : ℤ) ∣ ∑ k : Fin 24, xZ k := by
    have hlast8 : (8 : ℤ) ∣ c last * rowSum last := by
      rcases hcLast_even' with ⟨t, ht⟩
      refine ⟨5 * t, ?_⟩
      simp [ht, hrowSum_last, mul_assoc, mul_comm]
    have hsum8 : (8 : ℤ) ∣ ∑ i : Fin 24, c i * rowSum i := by
      refine Finset.dvd_sum (s := (Finset.univ : Finset (Fin 24))) ?_
      intro i _
      by_cases hi : i = last
      · subst hi
        simpa using! hlast8
      · rcases hrowSum8 i hi with ⟨t, ht⟩
        refine ⟨c i * t, ?_⟩
        simp [ht, mul_assoc, mul_left_comm, mul_comm]
    simpa [hxZ_sum] using! hsum8
  have hzZ_sum_odd : ¬ (2 : ℤ) ∣ ∑ k : Fin 24, zZ k := by
    have hdiff : (2 : ℤ) ∣ (zZ ⬝ᵥ zZ : ℤ) - ∑ k : Fin 24, zZ k := by
      -- pointwise: `z*z - z = z*(z-1)` is even
      have hterm : ∀ k : Fin 24, (2 : ℤ) ∣ (zZ k * zZ k - zZ k) := by
        intro k
        have : Even (zZ k) ∨ Even (zZ k - 1) := by
          by_cases hk : Even (zZ k)
          · exact Or.inl hk
          · exact Or.inr ((Int.even_sub_one (n := zZ k)).2 hk)
        have heven : Even (zZ k * (zZ k - 1)) := (Int.even_mul).2 this
        rcases heven with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have : zZ k * zZ k - zZ k = zZ k * (zZ k - 1) := by ring
        simpa [this, two_mul] using! ht
      have : (2 : ℤ) ∣ ∑ k : Fin 24, (zZ k * zZ k - zZ k) := by
        exact Finset.dvd_sum fun i a => hterm i
      simpa [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        Finset.sum_sub_distrib] using! this
    intro hsum
    have : (2 : ℤ) ∣ (zZ ⬝ᵥ zZ : ℤ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! dvd_add hdiff hsum
    have hdiv := this
    simp [hzZdot] at hdiv
  have hxZ_sum_not_dvd8 : ¬ (8 : ℤ) ∣ ∑ k : Fin 24, xZ k := by
    have hxZ_sum_eq : (∑ k : Fin 24, xZ k) = 4 * (∑ k : Fin 24, zZ k) := by
      simp [hxZ_eq_four_mul_zZ, Finset.mul_sum, mul_comm]
    intro h8
    rcases h8 with ⟨t, ht⟩
    have : (2 : ℤ) ∣ ∑ k : Fin 24, zZ k := by
      refine ⟨t, ?_⟩
      linarith
    exact hzZ_sum_odd this
  exact hxZ_sum_not_dvd8 hxZ_sum_dvd8

lemma leechParity_w_mem_span_basis (c : Fin 24 → ℤ) (yZ : Fin 24 → ℤ)
    (hyZ :
      yZ =
        fun k : Fin 24 =>
          ∑ i : Fin 24,
            if i = (23 : Fin 24) then (c i / 2) * leechMatrixInt i k
            else c i * (leechMatrixInt i k / 2)) :
    (fun k : Fin 24 => (yZ k : ZMod 2)) ∈
      Submodule.span (ZMod 2) (Set.range leechParityBasisVec) := by
  let w : Fin 24 → ZMod 2 := fun k : Fin 24 => (yZ k : ZMod 2)
  let d : Fin 24 → ZMod 2 :=
    fun i : Fin 24 => if i = (23 : Fin 24) then ((c i / 2 : ℤ) : ZMod 2) else (c i : ZMod 2)
  have hw_spanAll : w ∈ Submodule.span (ZMod 2) (Set.range leechParityVec) := by
    refine
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := leechParityVec) (x := w)).2 ?_
    refine ⟨d, ?_⟩
    ext k
    -- Push coercions into the sum and simplify each summand by cases on `i = 23`.
    simp only [w, hyZ, d, leechParityVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Int.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i = (23 : Fin 24)
    · subst hi
      simp
    · simp [hi]
  have hgen :
      ∀ i : Fin 24,
        leechParityVec i ∈ Submodule.span (ZMod 2) (Set.range leechParityBasisVec) := by
    intro i
    rcases leechParityVec_mem_span_basis i with ⟨e, he⟩
    exact
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := leechParityBasisVec)
            (x := leechParityVec i)).2 ⟨e, he⟩
  have hle :
      Submodule.span (ZMod 2) (Set.range leechParityVec) ≤
        Submodule.span (ZMod 2) (Set.range leechParityBasisVec) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hgen i
  simpa [w] using! hle hw_spanAll

theorem leech_no_norm_sq_two (v : ℝ²⁴) (hv : v ∈ LeechLattice) (h0 : v ≠ 0) :
    ‖v‖ ^ 2 ≠ (2 : ℝ) := by
  rcases
      (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := leechGeneratorRows) (x := v)).1 hv
    with ⟨c, rfl⟩
  let last : Fin 24 := 23
  let xZ : Fin 24 → ℤ := LeechNorm.combInt c
  let x : ℝ²⁴ := LeechNorm.combReal c
  have hvEq : (∑ i : Fin 24, c i • leechGeneratorRows i) = ((Real.sqrt 8)⁻¹ : ℝ) • x := by
    have hvR :
        (∑ i : Fin 24, c i • leechGeneratorRows i) =
          ∑ i : Fin 24, (c i : ℝ) • leechGeneratorRows i := by
      simp [Int.cast_smul_eq_zsmul]
    calc
      (∑ i : Fin 24, c i • leechGeneratorRows i)
          = ∑ i : Fin 24, (c i : ℝ) • leechGeneratorRows i := hvR
      _ = ((Real.sqrt 8)⁻¹ : ℝ) • x := by
            simpa [x] using! LeechNorm.sum_smul_leechGeneratorRows_eq_smul_combReal c
  have hnorm_smul (r : ℝ) (y : ℝ²⁴) : ‖r • y‖ ^ 2 = r ^ 2 * ‖y‖ ^ 2 := by
    calc
      ‖r • y‖ ^ 2 = (‖r‖ * ‖y‖) ^ 2 := by simp [norm_smul]
      _ = ‖r‖ ^ 2 * ‖y‖ ^ 2 := by simpa using! (mul_pow ‖r‖ ‖y‖ 2)
      _ = r ^ 2 * ‖y‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  have hsqrt8 : ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 = (1 / 8 : ℝ) := by
    norm_num
  intro hvSq
  have hxSq : ‖x‖ ^ 2 = (16 : ℝ) := by
    have hvSq' : ‖((Real.sqrt 8)⁻¹ : ℝ) • x‖ ^ 2 = (2 : ℝ) := by
      simpa [hvEq] using! hvSq
    have hvSq'' :
        ((Real.sqrt 8)⁻¹ : ℝ) ^ 2 * ‖x‖ ^ 2 = (2 : ℝ) := by
      simpa [hnorm_smul] using! hvSq'
    have : (1 / 8 : ℝ) * ‖x‖ ^ 2 = (2 : ℝ) := by
      simpa [hsqrt8] using! hvSq''
    have hmul := congrArg (fun t : ℝ => (8 : ℝ) * t) this
    have hmul' : ‖x‖ ^ 2 = (8 : ℝ) * 2 := by
      have h88 : (8 : ℝ) * (1 / 8 : ℝ) = 1 := by norm_num
      -- rearrange `8 * ((1/8) * t)` and cancel.
      have : ((8 : ℝ) * (1 / 8 : ℝ)) * ‖x‖ ^ 2 = (8 : ℝ) * 2 := by
        simpa [mul_assoc] using! hmul
      simpa [h88] using! this
    exact hmul'.trans (by norm_num)
  have hxZdot : (xZ ⬝ᵥ xZ : ℤ) = 16 := by
    have hxZdotR : ((xZ ⬝ᵥ xZ : ℤ) : ℝ) = (16 : ℝ) := by
      have hsq : ‖x‖ ^ 2 = ((xZ ⬝ᵥ xZ : ℤ) : ℝ) := by
        simpa [x, xZ] using! LeechNorm.combReal_norm_sq c
      simpa [hxSq] using! hsq.symm
    exact_mod_cast hxZdotR
  -- Parity: only the last row contributes odd entries.
  have hrow_even :
      ∀ i : Fin 24, i ≠ last → ∀ j : Fin 24, (2 : ℤ) ∣ leechMatrixInt i j := by
    intro i hi j
    fin_cases i <;> (try (cases hi rfl)) <;> fin_cases j <;> decide
  have hlast_mod2 : ∀ j : Fin 24, (leechMatrixInt last j : ZMod 2) = 1 := by
    intro j
    fin_cases j <;> decide
  have hxZ_mod2 : ∀ j : Fin 24, (xZ j : ZMod 2) = (c last : ZMod 2) := by
    intro j
    have hxZ_cast :
        (xZ j : ZMod 2) =
          ∑ i : Fin 24, (c i : ZMod 2) * (leechMatrixInt i j : ZMod 2) := by
      simp [xZ, LeechNorm.combInt, LeechNorm.rowInt, Int.cast_sum, Int.cast_mul]
    -- all summands are `0` except `i = last`.
    have hsum :
        (∑ i : Fin 24, (c i : ZMod 2) * (leechMatrixInt i j : ZMod 2)) =
          (c last : ZMod 2) * (leechMatrixInt last j : ZMod 2) := by
      refine Finset.sum_eq_single last ?_ ?_
      · intro i hi hne
        have hdiv : (2 : ℤ) ∣ leechMatrixInt i j := hrow_even i hne j
        have hm0 : (leechMatrixInt i j : ZMod 2) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (leechMatrixInt i j) 2).2 hdiv
        simp [hm0]
      · intro hnot
        exact (hnot (Finset.mem_univ last)).elim
    -- simplify the last term
    simp [hxZ_cast, hsum, hlast_mod2 j]
  have hcLast_even : (2 : ℤ) ∣ c last := by
    by_contra hodd
    have hcLast_ne0 : (c last : ZMod 2) ≠ 0 := by
      intro h0'
      exact hodd ((ZMod.intCast_zmod_eq_zero_iff_dvd (c last) 2).1 h0')
    have hxZ_ne0 : ∀ j : Fin 24, (xZ j : ZMod 2) ≠ 0 := by
      intro j
      simpa [hxZ_mod2 j] using! hcLast_ne0
    have hterm : ∀ j : Fin 24, (1 : ℝ) ≤ (xZ j : ℝ) ^ 2 := by
      intro j
      have hxZj_ne0 : xZ j ≠ 0 := by
        intro hx0'
        exact hxZ_ne0 j (by simp [hx0'])
      exact one_le_sq_of_int_ne0 (z := xZ j) hxZj_ne0
    have h24_le :
        (24 : ℝ) ≤ ∑ j : Fin 24, (xZ j : ℝ) ^ 2 := by
      have : (24 : ℝ) = ∑ j : Fin 24, (1 : ℝ) := by simp
      calc
        (24 : ℝ) = ∑ j : Fin 24, (1 : ℝ) := this
        _ ≤ ∑ j : Fin 24, (xZ j : ℝ) ^ 2 := by
              refine Finset.sum_le_sum ?_
              intro j _
              exact hterm j
    have hxZsq_eq : ∑ j : Fin 24, (xZ j : ℝ) ^ 2 = (16 : ℝ) := by
      have : ((xZ ⬝ᵥ xZ : ℤ) : ℝ) = (16 : ℝ) := by exact_mod_cast hxZdot
      simpa [dotProduct, pow_two, Int.cast_sum, Int.cast_mul] using! this
    have : (24 : ℝ) ≤ (16 : ℝ) := by simpa [hxZsq_eq] using! h24_le
    linarith
  -- Define the half-vector `yZ` with integer coordinates: `xZ = 2 * yZ`.
  let yZ : Fin 24 → ℤ := fun k : Fin 24 =>
    ∑ i : Fin 24,
      if i = last then (c i / 2) * leechMatrixInt i k
      else c i * (leechMatrixInt i k / 2)
  have hxZ_eq_two_mul_yZ : ∀ k : Fin 24, xZ k = 2 * yZ k := by
    intro k
    have hxZk :
        xZ k = ∑ i : Fin 24, c i * leechMatrixInt i k := by
      simp [xZ, LeechNorm.combInt, LeechNorm.rowInt]
    have hterm :
        ∀ i : Fin 24,
          c i * leechMatrixInt i k =
            2 *
              (if i = last then (c i / 2) * leechMatrixInt i k
               else c i * (leechMatrixInt i k / 2)) := by
      intro i
      by_cases hi : i = last
      · subst hi
        rcases hcLast_even with ⟨t, ht⟩
        have hcEven : Even (c last) := by
          refine ⟨t, ?_⟩
          simpa [two_mul] using! ht
        have htwo : (2 : ℤ) * (c last / 2) = c last :=
          Int.two_mul_ediv_two_of_even (n := c last) hcEven
        calc
          c last * leechMatrixInt last k =
              (2 * (c last / 2)) * leechMatrixInt last k := by
                simp [htwo]
          _ = 2 * ((c last / 2) * leechMatrixInt last k) := by
                ring
          _ =
              2 *
                (if last = last then (c last / 2) * leechMatrixInt last k
                 else c last * (leechMatrixInt last k / 2)) := by
                simp
      · have hdiv : (2 : ℤ) ∣ leechMatrixInt i k := hrow_even i hi k
        rcases hdiv with ⟨t, ht⟩
        have hEven : Even (leechMatrixInt i k) := by
          refine ⟨t, ?_⟩
          simpa [two_mul] using! ht
        have htwo : (2 : ℤ) * (leechMatrixInt i k / 2) = leechMatrixInt i k :=
          Int.two_mul_ediv_two_of_even (n := leechMatrixInt i k) hEven
        calc
          c i * leechMatrixInt i k =
              c i * (2 * (leechMatrixInt i k / 2)) := by
                simp [htwo]
          _ = 2 * (c i * (leechMatrixInt i k / 2)) := by
                ring
          _ =
              2 *
                (if i = last then (c i / 2) * leechMatrixInt i k
                 else c i * (leechMatrixInt i k / 2)) := by
                simp [hi]
    calc
      xZ k = ∑ i : Fin 24, c i * leechMatrixInt i k := hxZk
      _ =
          ∑ i : Fin 24,
            2 *
              (if i = last then (c i / 2) * leechMatrixInt i k
               else c i * (leechMatrixInt i k / 2)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simpa using! (hterm i)
      _ =
          2 *
            (∑ i : Fin 24,
              if i = last then (c i / 2) * leechMatrixInt i k
              else c i * (leechMatrixInt i k / 2)) := by
          simp [Finset.mul_sum]
      _ = 2 * yZ k := by rfl
  have hyZdot : (yZ ⬝ᵥ yZ : ℤ) = 4 := by
    have hxZdot_eq : (xZ ⬝ᵥ xZ : ℤ) = 4 * (yZ ⬝ᵥ yZ : ℤ) := by
      -- expand the dot product and use `xZ k = 2 * yZ k`
      have : (xZ ⬝ᵥ xZ : ℤ) = ∑ k : Fin 24, (2 * yZ k) * (2 * yZ k) := by
        simp [dotProduct, hxZ_eq_two_mul_yZ]
      calc
        (xZ ⬝ᵥ xZ : ℤ) = ∑ k : Fin 24, (2 * yZ k) * (2 * yZ k) := this
        _ = ∑ k : Fin 24, 4 * (yZ k * yZ k) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              ring
        _ = 4 * (∑ k : Fin 24, yZ k * yZ k) := by
              simp [Finset.mul_sum]
        _ = 4 * (yZ ⬝ᵥ yZ : ℤ) := by simp [dotProduct]
    have h4 : (4 : ℤ) ≠ 0 := by norm_num
    have hmul : (4 : ℤ) * (yZ ⬝ᵥ yZ : ℤ) = (16 : ℤ) := by
      simpa [hxZdot_eq] using! hxZdot
    have hmul' : (4 : ℤ) * (yZ ⬝ᵥ yZ : ℤ) = (4 : ℤ) * 4 := by
      simpa [show (16 : ℤ) = (4 : ℤ) * 4 by norm_num] using! hmul
    exact mul_left_cancel₀ h4 hmul'
  -- Define the parity pattern of `yZ`.
  let w : Fin 24 → ZMod 2 := fun k : Fin 24 => (yZ k : ZMod 2)
  have hyZ23 :
      yZ =
        fun k : Fin 24 =>
          ∑ i : Fin 24,
            if i = (23 : Fin 24) then (c i / 2) * leechMatrixInt i k
            else c i * (leechMatrixInt i k / 2) := by
    funext k
    simp [yZ, last]
  have hw_mem :
      w ∈ Submodule.span (ZMod 2) (Set.range leechParityBasisVec) := by
    simpa [w] using! leechParity_w_mem_span_basis (c := c) (yZ := yZ) hyZ23
  -- If `w ≠ 0`, then it has weight at least 8, contradicting `yZ ⬝ᵥ yZ = 4`.
  by_cases hw0 : w = 0
  · -- Then `yZ` is even, hence `xZ` is divisible by `4`, forcing a contradiction with a mod-8
    -- coordinate sum invariant.
    exact leech_no_norm_sq_two_contra_w_eq0 c yZ hxZ_eq_two_mul_yZ hyZdot hcLast_even hw0
  · -- Apply the min-weight bound.
    exact leech_no_norm_sq_two_contra_w_ne0 yZ hyZdot hw_mem (by simpa [w] using! hw0)

/-- Minimal norm property: the shortest nonzero Leech vectors have norm at least `2`. -/
theorem leech_norm_lower_bound (v : ℝ²⁴) (hv : v ∈ LeechLattice) (h0 : v ≠ 0) :
    (2 : ℝ) ≤ ‖v‖ := by
  /- Proof sketch:
  From `leech_norm_sq_eq_two_mul` show `‖v‖^2 ≥ 4` for `v ≠ 0`, hence `‖v‖ ≥ 2`.
  In the concrete construction, this is the key "no vectors of norm sqrt(2)" statement. -/
  rcases leech_norm_sq_eq_two_mul v hv with ⟨n, hn⟩
  have hn_ne0 : n ≠ 0 := by
    intro hn0
    simp_all
  have hn_ne1 : n ≠ 1 := by
    intro hn1
    have : ‖v‖ ^ 2 ≠ (2 : ℝ) := leech_no_norm_sq_two v hv h0
    apply this
    simpa [hn1] using! hn
  have hn_ge2 : 2 ≤ n := (Nat.two_le_iff n).2 ⟨hn_ne0, hn_ne1⟩
  have hsq : (4 : ℝ) ≤ ‖v‖ ^ 2 := by
    calc
      (4 : ℝ) = (2 : ℝ) * (2 : ℝ) := by ring
        _ ≤ (2 : ℝ) * (n : ℝ) := by
              gcongr
              exact_mod_cast hn_ge2
        _ = ‖v‖ ^ 2 := by
              exact hn.symm
  have hsq' : (2 : ℝ) ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa [show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num] using! hsq
  exact le_of_sq_le_sq hsq' (norm_nonneg _)

end SphericalRiesz
