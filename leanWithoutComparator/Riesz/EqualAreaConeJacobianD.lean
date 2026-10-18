import Riesz.EqualAreaConeDerivativeD
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual `(n+2)`-dimensional radial-cone Jacobian. The Gram matrix has
blocks 1 and t^2 times the already proved actual chart Gram matrix.
Taking determinants, then the nonnegative square root, avoids expanding
any determinant entrywise. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

variable {n : ℕ}

def equalAreaBasisEquivD : (EqualAreaBasisIndexD n) ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl 0) Sum.inr
  left_inv := by
    intro j
    cases j with
    | inl j => simp only [Sum.elim_inl,Fin.cases_zero]; congr 1; exact Subsingleton.elim _ _
    | inr j => rfl
  right_inv := by
    intro j
    exact Fin.cases rfl (fun _ => rfl) j

abbrev EqualAreaConeBasisIndexD (n : ℕ) := Fin 1 ⊕ (EqualAreaBasisIndexD n)

def equalAreaConeBasisEquivD : (EqualAreaConeBasisIndexD n) ≃ Fin (n+1+1) where
  toFun := Sum.elim (fun _ => 0) (fun j => (equalAreaBasisEquivD j).succ)
  invFun := Fin.cases (Sum.inl 0) (fun j => Sum.inr (equalAreaBasisEquivD.symm j))
  left_inv := by
    intro j
    cases j with
    | inl j => simp only [Sum.elim_inl,Fin.cases_zero]; congr 1; exact Subsingleton.elim _ _
    | inr j => simp
  right_inv := by
    intro j
    refine Fin.cases rfl (fun k => ?_) j
    simp

theorem equalAreaBasisVectorD_eq_single (j : (EqualAreaBasisIndexD n)) :
    equalAreaBasisVectorD j = Pi.single (equalAreaBasisEquivD j) 1 := by
  cases j <;> rfl

def equalAreaConeColumnD (z : Fin (n+1+1) → ℝ) : (EqualAreaConeBasisIndexD n) → (AmbientD (n+1)) :=
  Sum.elim (fun _ => equalAreaPhiD (Fin.tail z))
    (fun j => z 0 • equalAreaPhiDerivativeD (Fin.tail z) (equalAreaBasisVectorD j))

def equalAreaConeMatrixD (z : Fin (n+1+1) → ℝ) :
    Matrix (EqualAreaConeBasisIndexD n) (EqualAreaConeBasisIndexD n) ℝ :=
  fun i j => equalAreaConeColumnD z j (equalAreaConeBasisEquivD i)

theorem equalAreaConeDerivativeD_radial (z : Fin (n+1+1) → ℝ) :
    equalAreaConeDerivativeD z (Pi.single 0 1) = equalAreaPhiD (Fin.tail z) := by
  have ht : Fin.tail (Pi.single (0:Fin (n+1+1)) (1:ℝ) : Fin (n+1+1) → ℝ) = 0 := by
    ext i
    simp [Fin.tail]
  simp [equalAreaConeDerivativeD,equalAreaTailProjection9D_apply,ht]

theorem equalAreaConeDerivativeD_tangent (z : Fin (n+1+1) → ℝ) (j : (EqualAreaBasisIndexD n)) :
    equalAreaConeDerivativeD z (Pi.single (equalAreaBasisEquivD j).succ 1) =
      z 0 • equalAreaPhiDerivativeD (Fin.tail z) (equalAreaBasisVectorD j) := by
  have ht : Fin.tail (Pi.single (equalAreaBasisEquivD j).succ (1:ℝ) : Fin (n+1+1) → ℝ) =
      equalAreaBasisVectorD j := by
    rw [equalAreaBasisVectorD_eq_single]
    ext i
    simp [Fin.tail,Pi.single_apply]
  simp [equalAreaConeDerivativeD,equalAreaTailProjection9D_apply,ht]

theorem equalAreaConeMatrixD_eq_toMatrix (z : Fin (n+1+1) → ℝ) :
    equalAreaConeMatrixD z =
      (LinearMap.toMatrix' (equalAreaConeCoordinateDerivativeD z).toLinearMap).submatrix
        equalAreaConeBasisEquivD equalAreaConeBasisEquivD := by
  ext i j
  simp only [Matrix.submatrix_apply,LinearMap.toMatrix'_apply,
    equalAreaConeCoordinateDerivativeD,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,PiLp.coe_continuousLinearEquiv,
    ContinuousLinearMap.coe_coe,equalAreaConeMatrixD]
  cases j with
  | inl j =>
    change _ = equalAreaConeDerivativeD z (Pi.single 0 1) _
    rw [equalAreaConeDerivativeD_radial]
    rfl
  | inr j =>
    change _ = equalAreaConeDerivativeD z (Pi.single (equalAreaBasisEquivD j).succ 1) _
    rw [equalAreaConeDerivativeD_tangent]
    rfl

theorem equalAreaGramMatrixD_eq_inner (p : Fin (n+1) → ℝ) (i j : (EqualAreaBasisIndexD n)) :
    equalAreaGramMatrixD p i j =
      inner ℝ (equalAreaPhiDerivativeD p (equalAreaBasisVectorD i))
        (equalAreaPhiDerivativeD p (equalAreaBasisVectorD j)) := by
  simp [equalAreaGramMatrixD,equalAreaDerivativeMatrixD,Matrix.mul_apply,
    Matrix.transpose_apply,PiLp.inner_apply,mul_comm]

theorem equalAreaConeMatrixD_gram (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    (equalAreaConeMatrixD z).transpose*equalAreaConeMatrixD z =
      Matrix.fromBlocks (fun _ : Fin 1 => fun _ : Fin 1 => (1:ℝ)) 0 0
        ((z 0)^2 • equalAreaGramMatrixD (Fin.tail z)) := by
  have hm : ∀ i j, ((equalAreaConeMatrixD z).transpose*equalAreaConeMatrixD z) i j =
      inner ℝ (equalAreaConeColumnD z i) (equalAreaConeColumnD z j) := by
    intro i j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,equalAreaConeMatrixD]
    rw [equalAreaConeBasisEquivD.sum_comp
      (fun k : Fin (n+1+1) => equalAreaConeColumnD z i k*equalAreaConeColumnD z j k)]
    simp [PiLp.inner_apply,mul_comm]
  ext i j
  rw [hm]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [equalAreaConeColumnD,Sum.elim_inl,Matrix.fromBlocks_apply₁₁,
        real_inner_self_eq_norm_sq]
      rw [equalAreaPhiD_norm_sq,equalAreaHeightD_sq _ hz]
      ring
    | inr j =>
      simp only [equalAreaConeColumnD,Sum.elim_inl,Sum.elim_inr,
        Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,real_inner_smul_right]
      rw [equalAreaPhiD_derivative_orthogonal _ _ hz,mul_zero]
  | inr i =>
    cases j with
    | inl j =>
      simp only [equalAreaConeColumnD,Sum.elim_inl,Sum.elim_inr,
        Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,real_inner_smul_left]
      rw [real_inner_comm,equalAreaPhiD_derivative_orthogonal _ _ hz,mul_zero]
    | inr j =>
      simp only [equalAreaConeColumnD,Sum.elim_inr,Matrix.fromBlocks_apply₂₂,
        Matrix.smul_apply,smul_eq_mul,real_inner_smul_left,real_inner_smul_right,
        equalAreaGramMatrixD_eq_inner]
      ring

theorem equalAreaConeMatrixD_det_sq (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    (equalAreaConeMatrixD z).det^2 = (z 0)^(2*(n+1)) := by
  have h := congrArg Matrix.det (equalAreaConeMatrixD_gram z hz)
  have hd : Matrix.det (fun _ : Fin 1 => fun _ : Fin 1 => (1:ℝ)) = 1 := by
    rw [Matrix.det_unique]
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_fromBlocks_zero₁₂,
    hd,Matrix.det_smul,equalAreaGramMatrixD_det_one _ hz] at h
  have hc : Fintype.card (EqualAreaBasisIndexD n) = n+1 := by
    simp [Fintype.card_sum, add_comm]
  rw [hc, one_mul, mul_one] at h
  rw [pow_mul, ← h]
  ring

theorem equalAreaConeMatrixD_abs_det (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    |(equalAreaConeMatrixD z).det| = |z 0|^(n+1) := by
  apply (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, equalAreaConeMatrixD_det_sq z hz, ← abs_pow, sq_abs]
  ring

theorem equalAreaConeCoordinateDerivativeD_abs_det (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    |(equalAreaConeCoordinateDerivativeD z).det| = |z 0|^(n+1) := by
  change |LinearMap.det (equalAreaConeCoordinateDerivativeD z).toLinearMap| = _
  rw [←LinearMap.det_toMatrix']
  have h := equalAreaConeMatrixD_abs_det z hz
  rw [equalAreaConeMatrixD_eq_toMatrix,Matrix.det_submatrix_equiv_self] at h
  exact h

theorem equalAreaConeCoordinatesD_fderiv_abs_det (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    |(fderiv ℝ equalAreaConeCoordinatesD z).det| = |z 0|^(n+1) := by
  rw [equalAreaConeCoordinatesD_fderiv z hz]
  exact equalAreaConeCoordinateDerivativeD_abs_det z hz

end SphericalRiesz
