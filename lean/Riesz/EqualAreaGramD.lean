import Riesz.EqualAreaChartD
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

variable {n : ℕ}

abbrev EqualAreaBasisIndexD (n : ℕ) := Fin 1 ⊕ Fin n

def equalAreaBasisVectorD (j : (EqualAreaBasisIndexD n)) : Fin (n+1) → ℝ :=
  Sum.elim (fun _ => Pi.single 0 1) (fun k => Pi.single k.succ 1) j

def equalAreaDerivativeMatrixD (p : Fin (n+1) → ℝ) : Matrix (Fin (n+1+1)) (EqualAreaBasisIndexD n) ℝ :=
  fun i j => equalAreaPhiDerivativeD p (equalAreaBasisVectorD j) i

def equalAreaGramMatrixD (p : Fin (n+1) → ℝ) : Matrix (EqualAreaBasisIndexD n) (EqualAreaBasisIndexD n) ℝ :=
  (equalAreaDerivativeMatrixD p).transpose*equalAreaDerivativeMatrixD p

def equalAreaGramBlockD (p : Fin (n+1) → ℝ) : Matrix (EqualAreaBasisIndexD n) (EqualAreaBasisIndexD n) ℝ :=
  Matrix.fromBlocks (fun _ _ => equalAreaHeightD p^2) 0 0
    (1+Matrix.replicateCol Unit (fun j : Fin n => p j.succ/equalAreaHeightD p)*
      Matrix.replicateRow Unit (fun j : Fin n => p j.succ/equalAreaHeightD p))

theorem equalAreaDerivativeMatrixD_angle (p : Fin (n+1) → ℝ) (j : Fin 1) :
    (fun i => equalAreaDerivativeMatrixD p i (.inl j)) =
      Fin.cons (-equalAreaHeightD p*Real.sin (p 0))
        (Fin.cons (equalAreaHeightD p*Real.cos (p 0)) 0) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [equalAreaDerivativeMatrixD,equalAreaBasisVectorD,equalAreaPhiDerivativeD,
      equalAreaHeightGradientD,equalAreaNormGradientD]
  · refine Fin.cases ?_ (fun k => ?_) k <;>
      simp [equalAreaDerivativeMatrixD,equalAreaBasisVectorD,equalAreaPhiDerivativeD,
        equalAreaHeightGradientD,equalAreaNormGradientD]

theorem equalAreaDerivativeMatrixD_transverse (p : Fin (n+1) → ℝ) (j : Fin n) :
    (fun i => equalAreaDerivativeMatrixD p i (.inr j)) =
      Fin.cons (-p j.succ*Real.cos (p 0)/equalAreaHeightD p)
        (Fin.cons (-p j.succ*Real.sin (p 0)/equalAreaHeightD p) (Pi.single j 1)) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [equalAreaDerivativeMatrixD,equalAreaBasisVectorD,equalAreaPhiDerivativeD,
      equalAreaHeightGradientD,equalAreaNormGradientD,Pi.single_apply]
    ring
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp [equalAreaDerivativeMatrixD,equalAreaBasisVectorD,equalAreaPhiDerivativeD,
        equalAreaHeightGradientD,equalAreaNormGradientD,Pi.single_apply]
      ring
    · simp [equalAreaDerivativeMatrixD,equalAreaBasisVectorD,equalAreaPhiDerivativeD,
        equalAreaHeightGradientD,equalAreaNormGradientD,Pi.single_apply]

theorem equalAreaGramMatrixD_eq_block (p : Fin (n+1) → ℝ) :
    equalAreaGramMatrixD p = equalAreaGramBlockD p := by
  have ht := equalAreaDerivativeMatrixD_angle p
  have hu := equalAreaDerivativeMatrixD_transverse p
  have hs := Real.sin_sq_add_cos_sq (p 0)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [equalAreaGramMatrixD,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (ht i),congrFun (ht j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,mul_zero,
      Finset.sum_const_zero,add_zero,equalAreaGramBlockD,Matrix.fromBlocks_apply₁₁]
    calc
      _ = equalAreaHeightD p^2*(Real.sin (p 0)^2+Real.cos (p 0)^2) := by ring
      _ = _ := by rw [hs,mul_one]
  · simp only [equalAreaGramMatrixD,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (ht i),congrFun (hu j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,zero_mul,
      Finset.sum_const_zero,add_zero,equalAreaGramBlockD,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply]
    ring
  · simp only [equalAreaGramMatrixD,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (hu i),congrFun (ht j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply,mul_zero,
      Finset.sum_const_zero,add_zero,equalAreaGramBlockD,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply]
    ring
  · simp only [equalAreaGramMatrixD,Matrix.mul_apply,Matrix.transpose_apply]
    simp_rw [congrFun (hu i),congrFun (hu j)]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,equalAreaGramBlockD,
      Matrix.fromBlocks_apply₂₂,Matrix.add_apply,Matrix.mul_apply,Matrix.replicateCol_apply,
      Matrix.replicateRow_apply,Fintype.sum_unique]
    have hsingle : (∑ k : Fin n, Pi.single i (1:ℝ) k*Pi.single j 1 k) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      simp [Pi.single_apply,Matrix.one_apply,eq_comm]
    rw [hsingle]
    calc
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) i j +
          (p i.succ/equalAreaHeightD p)*(p j.succ/equalAreaHeightD p)*
            (Real.sin (p 0)^2+Real.cos (p 0)^2) := by ring
      _ = _ := by rw [hs,mul_one]

theorem equalAreaGramMatrixD_det_one (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    (equalAreaGramMatrixD p).det = 1 := by
  have hr := (equalAreaHeightD_pos p hp).ne'
  have hs := equalAreaHeightD_sq p hp
  rw [equalAreaGramMatrixD_eq_block,equalAreaGramBlockD,Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_unique,Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : (fun j : Fin n => p j.succ/equalAreaHeightD p) ⬝ᵥ
      (fun j : Fin n => p j.succ/equalAreaHeightD p) =
      equalAreaSquaredNormD p/equalAreaHeightD p^2 := by
    unfold dotProduct equalAreaSquaredNormD
    simp_rw [div_mul_div_comm,← pow_two]
    rw [Finset.sum_div]
  rw [hdot]
  field_simp [hr]
  nlinarith

theorem equalAreaGramMatrixD_sqrt_det (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    Real.sqrt (equalAreaGramMatrixD p).det = 1 := by
  rw [equalAreaGramMatrixD_det_one p hp,Real.sqrt_one]

/-- The Gram determinant is computed from the actual Fréchet derivative,
not merely a proposed derivative matrix. -/
theorem equalAreaPhiD_fderiv_gram_det (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    (Matrix.of (fun i j : (EqualAreaBasisIndexD n) => ∑ k : Fin (n+1+1),
      (fderiv ℝ equalAreaPhiD p (equalAreaBasisVectorD i)) k *
      (fderiv ℝ equalAreaPhiD p (equalAreaBasisVectorD j)) k)).det = 1 := by
  rw [equalAreaPhiD_fderiv p hp]
  exact equalAreaGramMatrixD_det_one p hp

end SphericalRiesz
