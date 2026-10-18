import Riesz.EqualAreaChart8
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The Gram determinant of the actual derivative of the explicit chart

The columns are evaluations of the proved continuous linear derivative
on the eight actual coordinate basis vectors. The rank-one determinant
lemma replaces a seven-by-seven determinant expansion. Determinant one
is a geometric result; actual surface measure is not identified here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

abbrev EqualAreaBasisIndex := Fin 1 ⊕ Fin 7

def equalAreaBasisVector (j : EqualAreaBasisIndex) : Fin 8 → ℝ :=
  Sum.elim (fun _ => Pi.single 0 1) (fun k => Pi.single k.succ 1) j

def equalAreaDerivativeMatrix (p : Fin 8 → ℝ) : Matrix (Fin 9) EqualAreaBasisIndex ℝ :=
  fun i j => equalAreaPhiDerivative p (equalAreaBasisVector j) i

def equalAreaGramMatrix (p : Fin 8 → ℝ) : Matrix EqualAreaBasisIndex EqualAreaBasisIndex ℝ :=
  (equalAreaDerivativeMatrix p).transpose*equalAreaDerivativeMatrix p

def equalAreaGramBlock (p : Fin 8 → ℝ) : Matrix EqualAreaBasisIndex EqualAreaBasisIndex ℝ :=
  Matrix.fromBlocks (fun _ _ => equalAreaHeight p^2) 0 0
    (1+Matrix.replicateCol Unit (fun j : Fin 7 => p j.succ/equalAreaHeight p)*
      Matrix.replicateRow Unit (fun j : Fin 7 => p j.succ/equalAreaHeight p))

theorem equalAreaDerivativeMatrix_angle (p : Fin 8 → ℝ) (j : Fin 1) :
    (fun i => equalAreaDerivativeMatrix p i (.inl j)) =
      Fin.cons (-equalAreaHeight p*Real.sin (p 0))
        (Fin.cons (equalAreaHeight p*Real.cos (p 0)) 0) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [equalAreaDerivativeMatrix,equalAreaBasisVector,equalAreaPhiDerivative,
      equalAreaHeightGradient,equalAreaNormGradient]
  · refine Fin.cases ?_ (fun k => ?_) k <;>
      simp [equalAreaDerivativeMatrix,equalAreaBasisVector,equalAreaPhiDerivative,
        equalAreaHeightGradient,equalAreaNormGradient]

theorem equalAreaDerivativeMatrix_transverse (p : Fin 8 → ℝ) (j : Fin 7) :
    (fun i => equalAreaDerivativeMatrix p i (.inr j)) =
      Fin.cons (-p j.succ*Real.cos (p 0)/equalAreaHeight p)
        (Fin.cons (-p j.succ*Real.sin (p 0)/equalAreaHeight p) (Pi.single j 1)) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [equalAreaDerivativeMatrix,equalAreaBasisVector,equalAreaPhiDerivative,
      equalAreaHeightGradient,equalAreaNormGradient,Pi.single_apply]
    ring
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp [equalAreaDerivativeMatrix,equalAreaBasisVector,equalAreaPhiDerivative,
        equalAreaHeightGradient,equalAreaNormGradient,Pi.single_apply]
      ring
    · simp [equalAreaDerivativeMatrix,equalAreaBasisVector,equalAreaPhiDerivative,
        equalAreaHeightGradient,equalAreaNormGradient,Pi.single_apply]

theorem equalAreaGramMatrix_eq_block (p : Fin 8 → ℝ) :
    equalAreaGramMatrix p = equalAreaGramBlock p := by
  have ht := equalAreaDerivativeMatrix_angle p
  have hu := equalAreaDerivativeMatrix_transverse p
  have hs := Real.sin_sq_add_cos_sq (p 0)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [equalAreaGramMatrix,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (ht i),congrFun (ht j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,mul_zero,
      Finset.sum_const_zero,add_zero,equalAreaGramBlock,Matrix.fromBlocks_apply₁₁]
    calc
      _ = equalAreaHeight p^2*(Real.sin (p 0)^2+Real.cos (p 0)^2) := by ring
      _ = _ := by rw [hs,mul_one]
  · simp only [equalAreaGramMatrix,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (ht i),congrFun (hu j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,zero_mul,
      Finset.sum_const_zero,add_zero,equalAreaGramBlock,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply]
    ring
  · simp only [equalAreaGramMatrix,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (hu i),congrFun (ht j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,mul_zero,
      Finset.sum_const_zero,add_zero,equalAreaGramBlock,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply]
    ring
  · simp only [equalAreaGramMatrix,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (hu i),congrFun (hu j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,equalAreaGramBlock,
      Matrix.fromBlocks_apply₂₂,Matrix.add_apply,Matrix.mul_apply,Matrix.replicateCol_apply,
      Matrix.replicateRow_apply,Fintype.sum_unique]
    have hsingle : (∑ k : Fin 7, Pi.single i (1:ℝ) k*Pi.single j 1 k) =
        (1 : Matrix (Fin 7) (Fin 7) ℝ) i j := by
      simp [Pi.single_apply,Matrix.one_apply,eq_comm]
    rw [hsingle]
    calc
      _ = (1 : Matrix (Fin 7) (Fin 7) ℝ) i j +
          (p i.succ/equalAreaHeight p)*(p j.succ/equalAreaHeight p)*
            (Real.sin (p 0)^2+Real.cos (p 0)^2) := by ring
      _ = _ := by rw [hs,mul_one]

theorem equalAreaGramMatrix_det_one (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    (equalAreaGramMatrix p).det = 1 := by
  have hr := (equalAreaHeight_pos p hp).ne'
  have hs := equalAreaHeight_sq p hp
  rw [equalAreaGramMatrix_eq_block,equalAreaGramBlock,Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_unique,Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : (fun j : Fin 7 => p j.succ/equalAreaHeight p) ⬝ᵥ
      (fun j : Fin 7 => p j.succ/equalAreaHeight p) =
      equalAreaSquaredNorm p/equalAreaHeight p^2 := by
    unfold dotProduct equalAreaSquaredNorm
    simp_rw [div_mul_div_comm,← pow_two]
    rw [Finset.sum_div]
  rw [hdot]
  field_simp [hr]
  nlinarith

theorem equalAreaGramMatrix_sqrt_det (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    Real.sqrt (equalAreaGramMatrix p).det = 1 := by
  rw [equalAreaGramMatrix_det_one p hp,Real.sqrt_one]

/-- The Gram determinant is computed from the actual Fréchet derivative,
not merely a proposed derivative matrix. -/
theorem equalAreaPhi_fderiv_gram_det (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    (Matrix.of (fun i j : EqualAreaBasisIndex => ∑ k : Fin 9,
      (fderiv ℝ equalAreaPhi p (equalAreaBasisVector i)) k *
      (fderiv ℝ equalAreaPhi p (equalAreaBasisVector j)) k)).det = 1 := by
  rw [equalAreaPhi_fderiv p hp]
  exact equalAreaGramMatrix_det_one p hp

end SphericalRiesz
