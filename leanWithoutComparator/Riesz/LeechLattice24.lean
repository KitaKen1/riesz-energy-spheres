/-
Copyright (c) 2025 the Sphere-Packing-Lean authors. All rights reserved.
Released under Apache 2.0 license; see third_party/SpherePacking/LICENSE.

The integer generator matrix of the Leech lattice, the triangular determinant argument and the
evenness argument below are adapted from Sphere-Packing-Lean at commit
1e98fb493088948ca7bbf47d7faed49cc5b39fc4, SpherePacking/Dim24/LeechLattice/Defs.lean,
Basis.lean and Norm.lean (evenness part only). Names are specialized to this project; the
real coordinate map, the Euclidean lattice API and the determinant-one statement for the scaled
matrix are added here, mirroring `E8Coordinates` and `E8Lattice`.
-/
import Riesz.E8Covolume
import Riesz.E8Volume
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic

/-! # The Leech lattice (stage P24-1)

The rows of an integer lower-triangular generator matrix, scaled by `1/√8`, span the Leech
lattice in `ℝ^24`. The scaled matrix has determinant one (the diagonal product is `2^36`), all
pairwise dot products of the integer rows are divisible by `8` and the squared row norms by `16`,
so every lattice vector has even squared norm. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SphericalRiesz

def leechMatrixInt : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0],
    ![0, 2, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0],
    ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  ]

theorem leechMatrixInt_aboveDiag : ∀ i j : Fin 24, i < j → leechMatrixInt i j = 0 := by
  have h : ∀ i j : Fin 24, decide (i < j → leechMatrixInt i j = 0) = true := by decide
  intro i j
  exact of_decide_eq_true (h i j)

theorem leechMatrixInt_diag_prod : (∏ i : Fin 24, leechMatrixInt i i) = (2:ℤ)^36 := by
  decide

/-- The scaled real generator matrix. -/
def leechMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  (Real.sqrt 8)⁻¹ • leechMatrixInt.map (fun z : ℤ => (z:ℝ))

theorem leechMatrixInt_real_det :
    (leechMatrixInt.map (fun z : ℤ => (z:ℝ))).det = (2:ℝ)^36 := by
  have htri : (leechMatrixInt.map (fun z : ℤ => (z:ℝ))).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h0 : leechMatrixInt i j = 0 := leechMatrixInt_aboveDiag i j (by simpa using hij)
    simp [Matrix.map_apply, h0]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  have : (∏ i : Fin 24, (leechMatrixInt i i : ℝ)) = (2:ℝ)^36 := by
    exact_mod_cast leechMatrixInt_diag_prod
  simpa [Matrix.map_apply] using this

theorem leechMatrix_det : leechMatrix.det = 1 := by
  rw [leechMatrix, Matrix.det_smul, Fintype.card_fin, leechMatrixInt_real_det, inv_pow]
  have h8 : Real.sqrt 8^24 = (2:ℝ)^36 := by
    rw [show (24:ℕ) = 2*12 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h8]
  exact inv_mul_cancel₀ (by positivity)

theorem leechMatrix_is_basis : LinearIndependent ℝ leechMatrix.row ∧
    Submodule.span ℝ (Set.range leechMatrix.row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det_apply]
  change IsUnit leechMatrix.det
  rw [leechMatrix_det]
  simp

def leechBasis : Module.Basis (Fin 24) ℝ (Fin 24 → ℝ) :=
  Module.Basis.mk leechMatrix_is_basis.1 leechMatrix_is_basis.2.ge

theorem leechBasis_apply (i : Fin 24) : leechBasis i = leechMatrix.row i := by
  rw [leechBasis, Module.Basis.coe_mk]

/-- The Leech coordinate map: integer coordinates go to lattice points. -/
def leechMap : (Fin 24 → ℝ) →L[ℝ] (Fin 24 → ℝ) :=
  leechBasis.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem leechMap_injective : Function.Injective leechMap :=
  leechBasis.equivFun.symm.injective

theorem leechMap_eq_sum (v : Fin 24 → ℝ) : leechMap v = ∑ i, v i • leechMatrix.row i := by
  change leechBasis.equivFun.symm v = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [leechBasis_apply]

/-! ## Evenness (adapted from `SpherePacking.Dim24.LeechNorm`) -/

def leechRowInt (i : Fin 24) : Fin 24 → ℤ := leechMatrixInt i

def leechDot (i j : Fin 24) : ℤ := (leechRowInt i) ⬝ᵥ (leechRowInt j)

theorem leechDot_mod8 (i j : Fin 24) : (8:ℤ) ∣ leechDot i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem leechDot_diag_mod16 (i : Fin 24) : (16:ℤ) ∣ leechDot i i := by
  fin_cases i <;> decide

def leechCombInt (c : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun k : Fin 24 => ∑ i : Fin 24, c i * leechRowInt i k

theorem leechCombInt_dot_eq_sum (c : Fin 24 → ℤ) :
    (leechCombInt c ⬝ᵥ leechCombInt c) = ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * leechDot i j := by
  let f : Fin 24 → (Fin 24 → ℤ) := fun i => fun k => c i * leechRowInt i k
  have hcomb : leechCombInt c = ∑ i : Fin 24, f i := by
    ext k
    simp [leechCombInt, f]
  calc
    leechCombInt c ⬝ᵥ leechCombInt c
        = (∑ i : Fin 24, f i) ⬝ᵥ (∑ j : Fin 24, f j) := by simp [hcomb]
    _ = ∑ i : Fin 24, f i ⬝ᵥ (∑ j : Fin 24, f j) :=
          sum_dotProduct Finset.univ f (∑ j, f j)
    _ = ∑ i : Fin 24, ∑ j : Fin 24, f i ⬝ᵥ f j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simpa using
            (dotProduct_sum (u := f i) (s := (Finset.univ : Finset (Fin 24))) (v := f))
    _ = ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * leechDot i j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp [f, leechDot, dotProduct, mul_assoc, mul_left_comm, Finset.mul_sum]

theorem leechCombInt_dot_divisible_by_16 (c : Fin 24 → ℤ) :
    (16:ℤ) ∣ (leechCombInt c ⬝ᵥ leechCombInt c) := by
  let g : Fin 24 → Fin 24 → ℤ := fun i j => leechDot i j / 8
  have hg_symm : ∀ i j, g i j = g j i := by
    intro i j
    have h : leechDot i j = leechDot j i := by
      simp [leechDot, leechRowInt, dotProduct_comm]
    simp [g, h]
  have hg_diag_even : ∀ i, (2:ℤ) ∣ g i i := by
    intro i
    rcases leechDot_diag_mod16 i with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    simp only [g, hm]
    omega
  let S : ℤ := ∑ i : Fin 24, ∑ j : Fin 24, c i * c j * g i j
  have hdot : (leechCombInt c ⬝ᵥ leechCombInt c) = 8 * S := by
    have hleech : ∀ i j, leechDot i j = g i j * 8 := by
      intro i j
      simpa [g] using
        (Int.ediv_mul_cancel (a := leechDot i j) (b := (8:ℤ)) (leechDot_mod8 i j)).symm
    rw [leechCombInt_dot_eq_sum]
    simp only [hleech, S, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hS_even : (2:ℤ) ∣ S := by
    let c2 : Fin 24 → ZMod 2 := fun i => (c i : ZMod 2)
    let g2 : Fin 24 → Fin 24 → ZMod 2 := fun i j => (g i j : ZMod 2)
    let F : (Fin 24 × Fin 24) → ZMod 2 := fun p => c2 p.1 * c2 p.2 * g2 p.1 p.2
    have hg2_diag : ∀ i, g2 i i = 0 := by
      intro i
      simpa [g2] using (ZMod.intCast_zmod_eq_zero_iff_dvd (g i i) 2).2 (hg_diag_even i)
    have hg2_symm : ∀ i j, g2 i j = g2 j i := by
      intro i j
      simpa [g2] using congrArg (fun t : ℤ => (t : ZMod 2)) (hg_symm i j)
    let s : Finset (Fin 24) := Finset.univ
    have hoff : ∑ p ∈ s.offDiag, F p = 0 := by
      refine Finset.sum_involution (s := s.offDiag) (f := F)
        (g := fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
      · intro p _
        have hswap : F (Prod.swap p) = F p := by
          cases p with
          | mk i j => simp [F, c2, g2, hg2_symm, mul_comm]
        exact CharTwo.add_eq_zero.mpr (Eq.symm hswap)
      · intro p hp _
        have hneq : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
        intro hEq
        apply hneq
        cases p with
        | mk i j =>
          have : (j, i) = (i, j) := by simpa [Prod.swap] using hEq
          simpa using congrArg Prod.snd this
      · intro p hp
        rcases Finset.mem_offDiag.1 hp with ⟨hi, hj, hij⟩
        exact Finset.mem_offDiag.2 ⟨hj, hi, Ne.symm hij⟩
      · intro p _
        rfl
    have hdiag0 : ∑ p ∈ s.diag, F p = 0 := by
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have hpEq : p.1 = p.2 := (Finset.mem_diag.1 hp).2
      cases p with
      | mk i j =>
        have hij : i = j := by simpa using hpEq
        subst hij
        simp [F, c2, g2, hg2_diag]
    have hprod : (∑ i : Fin 24, ∑ j : Fin 24, c2 i * c2 j * g2 i j) = ∑ p ∈ s ×ˢ s, F p := by
      simpa [s, F, c2, g2] using
        (Finset.sum_product (s := s) (t := s) (f := fun p : Fin 24 × Fin 24 => F p)).symm
    have hsplit : (∑ p ∈ s ×ˢ s, F p) = (∑ p ∈ s.diag, F p) + ∑ p ∈ s.offDiag, F p := by
      rw [← Finset.diag_union_offDiag (s := s)]
      exact Finset.sum_union (Finset.disjoint_diag_offDiag (s := s))
    have hsum0 : (∑ i : Fin 24, ∑ j : Fin 24, c2 i * c2 j * g2 i j) = 0 := by
      rw [hprod, hsplit, hdiag0, hoff, add_zero]
    have hS0 : (S : ZMod 2) = 0 := by
      simp [S, c2, g2, Int.cast_sum, Int.cast_mul, hsum0]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd S 2).1 hS0
  rcases hS_even with ⟨t, ht⟩
  exact ⟨t, by rw [hdot, ht]; ring⟩

/-! ## The Euclidean Leech lattice -/

abbrev LeechAmbient := EuclideanSpace ℝ (Fin 24)

def leechEuclideanBasis : Module.Basis (Fin 24) ℝ LeechAmbient :=
  leechBasis.map (WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ)).symm

def leechLattice : Submodule ℤ LeechAmbient :=
  Submodule.span ℤ (Set.range leechEuclideanBasis)

instance : DiscreteTopology leechLattice := by
  unfold leechLattice
  infer_instance

instance : IsZLattice ℝ leechLattice := by
  unfold leechLattice
  infer_instance

theorem leechEuclideanBasis_apply (i : Fin 24) :
    (leechEuclideanBasis i : LeechAmbient) = WithLp.toLp 2 (leechMatrix.row i) := by
  rw [leechEuclideanBasis, Module.Basis.map_apply, leechBasis_apply]
  rfl

/-- Integer combinations of the scaled rows. -/
def leechIntegerPoint (z : Fin 24 → ℤ) : LeechAmbient :=
  WithLp.toLp 2 (leechMap (fun i => (z i : ℝ)))

theorem leechLattice_mem_iff (x : LeechAmbient) :
    x ∈ leechLattice ↔ ∃ z : Fin 24 → ℤ, leechIntegerPoint z = x := by
  rw [leechLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [leechIntegerPoint, leechMap_eq_sum]
    simp only [leechEuclideanBasis_apply, ← WithLp.toLp_sum, Int.cast_smul_eq_zsmul ℝ]
    congr 1
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [leechIntegerPoint, leechMap_eq_sum]
    simp only [leechEuclideanBasis_apply]
    rw [← WithLp.toLp_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Int.cast_smul_eq_zsmul ℝ]
    rfl

theorem leechIntegerPoint_norm_sq (z : Fin 24 → ℤ) :
    ‖leechIntegerPoint z‖^2 = (1/8:ℝ)*((leechCombInt z ⬝ᵥ leechCombInt z : ℤ):ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hk : ∀ k : Fin 24, (leechIntegerPoint z) k = (Real.sqrt 8)⁻¹*(leechCombInt z k:ℝ) := by
    intro k
    simp only [leechIntegerPoint, PiLp.toLp_apply, leechMap_eq_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, leechMatrix, Matrix.row, Matrix.smul_apply, Matrix.map_apply,
      leechCombInt, leechRowInt]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp only [hk, mul_pow, inv_pow]
  rw [← Finset.mul_sum, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8)]
  simp only [dotProduct, Int.cast_sum, ← pow_two]
  push_cast
  ring

theorem leechLattice_even (x : leechLattice) :
    ∃ k : ℕ, ‖(x : LeechAmbient)‖^2 = 2*(k:ℝ) := by
  obtain ⟨z, hz⟩ := (leechLattice_mem_iff x).mp x.property
  rw [← hz, leechIntegerPoint_norm_sq]
  obtain ⟨m, hm⟩ := leechCombInt_dot_divisible_by_16 z
  have hm0 : 0 ≤ m := by
    have h0 : 0 ≤ leechCombInt z ⬝ᵥ leechCombInt z := by
      simp only [dotProduct]
      exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    omega
  refine ⟨Int.toNat m, ?_⟩
  rw [hm]
  have : ((Int.toNat m : ℕ) : ℝ) = ((m : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm0
  rw [this]
  push_cast
  ring

theorem leechLattice_rank : Module.finrank ℤ leechLattice = 24 := by
  rw [ZLattice.rank ℝ]
  exact finrank_euclideanSpace_fin

theorem leechLattice_finite_norm_lt (R : ℝ) :
    {x : leechLattice | ‖(x : LeechAmbient)‖ < R}.Finite := by
  have hf := ZSpan.setFinite_inter leechEuclideanBasis
    (s := Metric.ball (0 : LeechAmbient) R) Metric.isBounded_ball
  have hpre := hf.preimage_embedding (Function.Embedding.subtype (fun x => x ∈ leechLattice))
  convert hpre using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.Embedding.subtype_apply,
    Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨h, x.property⟩
  · intro h
    exact h.1

#print axioms leechMatrixInt_aboveDiag
#print axioms leechMatrixInt_diag_prod
#print axioms leechMatrix_det
#print axioms leechMap_eq_sum
#print axioms leechDot_mod8
#print axioms leechDot_diag_mod16
#print axioms leechCombInt_dot_divisible_by_16
#print axioms leechLattice_mem_iff
#print axioms leechIntegerPoint_norm_sq
#print axioms leechLattice_even
#print axioms leechLattice_rank
#print axioms leechLattice_finite_norm_lt

/-! ## Volume preservation and covolume one -/

theorem leechMap_eq_matrixTranspose (v : Fin 24 → ℝ) :
    leechMap v = Matrix.toLin' leechMatrix.transpose v := by
  rw [leechMap_eq_sum, Matrix.toLin'_apply]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row,
    Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem leechMap_det : LinearMap.det leechMap.toLinearMap = 1 := by
  have h : leechMap.toLinearMap = Matrix.toLin' leechMatrix.transpose :=
    LinearMap.ext leechMap_eq_matrixTranspose
  rw [h, LinearMap.det_toLin', Matrix.det_transpose, leechMatrix_det]

theorem leechMap_map_volume :
    MeasureTheory.Measure.map leechMap (MeasureTheory.volume : MeasureTheory.Measure (Fin 24 → ℝ)) =
      MeasureTheory.volume := by
  have hdet : LinearMap.det leechMap.toLinearMap ≠ 0 := by rw [leechMap_det]; norm_num
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  simpa only [ContinuousLinearMap.coe_coe, leechMap_det, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul] using h

theorem leechMap_measurePreserving :
    MeasureTheory.MeasurePreserving leechMap (MeasureTheory.volume : MeasureTheory.Measure (Fin 24 → ℝ))
      MeasureTheory.volume :=
  ⟨leechMap.measurable, leechMap_map_volume⟩

theorem leechMap_measurableEmbedding :
    MeasurableEmbedding (leechMap : (Fin 24 → ℝ) → (Fin 24 → ℝ)) :=
  leechBasis.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

theorem leechEuclideanFundamentalDomain_volume :
    (MeasureTheory.volume : MeasureTheory.Measure LeechAmbient).real
      (ZSpan.fundamentalDomain leechEuclideanBasis) = 1 := by
  have hp : (WithLp.ofLp : LeechAmbient → (Fin 24 → ℝ)) ⁻¹'
      ZSpan.fundamentalDomain leechBasis = ZSpan.fundamentalDomain leechEuclideanBasis := by
    ext x
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, leechEuclideanBasis,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    rfl
  have hm : (Matrix.of leechBasis : Matrix (Fin 24) (Fin 24) ℝ) = leechMatrix := by
    ext i j
    simp only [Matrix.of_apply, leechBasis_apply]
    rfl
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (Fin 24 → ℝ)).real
      (ZSpan.fundamentalDomain leechBasis) = 1 := by
    rw [ZSpan.volume_real_fundamentalDomain, hm, leechMatrix_det, abs_one]
  have h := (PiLp.volume_preserving_ofLp (ι := Fin 24)).measureReal_preimage
    (ZSpan.fundamentalDomain_measurableSet (b := leechBasis)).nullMeasurableSet
  simpa only [hp, hv] using h

/-- The Leech lattice is unimodular: its covolume is one. -/
theorem leechLattice_covolume : ZLattice.covolume leechLattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain leechLattice MeasureTheory.volume
    (ZSpan.isAddFundamentalDomain leechEuclideanBasis MeasureTheory.volume)]
  exact leechEuclideanFundamentalDomain_volume

#print axioms leechMap_det
#print axioms leechMap_measurePreserving
#print axioms leechMap_measurableEmbedding
#print axioms leechEuclideanFundamentalDomain_volume
#print axioms leechLattice_covolume

end SphericalRiesz
