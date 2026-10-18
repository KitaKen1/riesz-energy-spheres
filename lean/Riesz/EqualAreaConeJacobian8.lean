import Riesz.EqualAreaConeDerivative8
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual nine-dimensional radial-cone Jacobian. The Gram matrix has
blocks 1 and t^2 times the already proved actual chart Gram matrix.
Taking determinants, then the nonnegative square root, avoids expanding
any nine-by-nine determinant. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

def equalAreaBasisEquiv8 : EqualAreaBasisIndex ≃ Fin 8 where
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

abbrev EqualAreaConeBasisIndex := Fin 1 ⊕ EqualAreaBasisIndex

def equalAreaConeBasisEquiv : EqualAreaConeBasisIndex ≃ Fin 9 where
  toFun := Sum.elim (fun _ => 0) (fun j => (equalAreaBasisEquiv8 j).succ)
  invFun := Fin.cases (Sum.inl 0) (fun j => Sum.inr (equalAreaBasisEquiv8.symm j))
  left_inv := by
    intro j
    cases j with
    | inl j => simp only [Sum.elim_inl,Fin.cases_zero]; congr 1; exact Subsingleton.elim _ _
    | inr j => simp
  right_inv := by
    intro j
    refine Fin.cases rfl (fun k => ?_) j
    simp

theorem equalAreaBasisVector_eq_single (j : EqualAreaBasisIndex) :
    equalAreaBasisVector j = Pi.single (equalAreaBasisEquiv8 j) 1 := by
  cases j <;> rfl

def equalAreaConeColumn (z : Fin 9 → ℝ) : EqualAreaConeBasisIndex → Ambient9 :=
  Sum.elim (fun _ => equalAreaPhi (Fin.tail z))
    (fun j => z 0 • equalAreaPhiDerivative (Fin.tail z) (equalAreaBasisVector j))

def equalAreaConeMatrix (z : Fin 9 → ℝ) :
    Matrix EqualAreaConeBasisIndex EqualAreaConeBasisIndex ℝ :=
  fun i j => equalAreaConeColumn z j (equalAreaConeBasisEquiv i)

theorem equalAreaConeDerivative_radial (z : Fin 9 → ℝ) :
    equalAreaConeDerivative z (Pi.single 0 1) = equalAreaPhi (Fin.tail z) := by
  have ht : Fin.tail (Pi.single (0:Fin 9) (1:ℝ) : Fin 9 → ℝ) = 0 := by
    ext i
    simp [Fin.tail]
  simp [equalAreaConeDerivative,equalAreaTailProjection9_apply,ht]

theorem equalAreaConeDerivative_tangent (z : Fin 9 → ℝ) (j : EqualAreaBasisIndex) :
    equalAreaConeDerivative z (Pi.single (equalAreaBasisEquiv8 j).succ 1) =
      z 0 • equalAreaPhiDerivative (Fin.tail z) (equalAreaBasisVector j) := by
  have ht : Fin.tail (Pi.single (equalAreaBasisEquiv8 j).succ (1:ℝ) : Fin 9 → ℝ) =
      equalAreaBasisVector j := by
    rw [equalAreaBasisVector_eq_single]
    ext i
    simp [Fin.tail,Pi.single_apply]
  simp [equalAreaConeDerivative,equalAreaTailProjection9_apply,ht]

theorem equalAreaConeMatrix_eq_toMatrix (z : Fin 9 → ℝ) :
    equalAreaConeMatrix z =
      (LinearMap.toMatrix' (equalAreaConeCoordinateDerivative z).toLinearMap).submatrix
        equalAreaConeBasisEquiv equalAreaConeBasisEquiv := by
  ext i j
  simp only [Matrix.submatrix_apply,LinearMap.toMatrix'_apply,
    equalAreaConeCoordinateDerivative,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,PiLp.coe_continuousLinearEquiv,
    ContinuousLinearMap.coe_coe,equalAreaConeMatrix]
  cases j with
  | inl j =>
    change _ = equalAreaConeDerivative z (Pi.single 0 1) _
    rw [equalAreaConeDerivative_radial]
    rfl
  | inr j =>
    change _ = equalAreaConeDerivative z (Pi.single (equalAreaBasisEquiv8 j).succ 1) _
    rw [equalAreaConeDerivative_tangent]
    rfl

theorem equalAreaGramMatrix_eq_inner (p : Fin 8 → ℝ) (i j : EqualAreaBasisIndex) :
    equalAreaGramMatrix p i j =
      inner ℝ (equalAreaPhiDerivative p (equalAreaBasisVector i))
        (equalAreaPhiDerivative p (equalAreaBasisVector j)) := by
  simp [equalAreaGramMatrix,equalAreaDerivativeMatrix,Matrix.mul_apply,
    Matrix.transpose_apply,PiLp.inner_apply,mul_comm]

theorem equalAreaConeMatrix_gram (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    (equalAreaConeMatrix z).transpose*equalAreaConeMatrix z =
      Matrix.fromBlocks (fun _ : Fin 1 => fun _ : Fin 1 => (1:ℝ)) 0 0
        ((z 0)^2 • equalAreaGramMatrix (Fin.tail z)) := by
  have hm : ∀ i j, ((equalAreaConeMatrix z).transpose*equalAreaConeMatrix z) i j =
      inner ℝ (equalAreaConeColumn z i) (equalAreaConeColumn z j) := by
    intro i j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,equalAreaConeMatrix]
    rw [equalAreaConeBasisEquiv.sum_comp
      (fun k : Fin 9 => equalAreaConeColumn z i k*equalAreaConeColumn z j k)]
    simp [PiLp.inner_apply,mul_comm]
  ext i j
  rw [hm]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [equalAreaConeColumn,Sum.elim_inl,Matrix.fromBlocks_apply₁₁,
        real_inner_self_eq_norm_sq]
      rw [equalAreaPhi_norm_sq,equalAreaHeight_sq _ hz]
      ring
    | inr j =>
      simp only [equalAreaConeColumn,Sum.elim_inl,Sum.elim_inr,
        Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,real_inner_smul_right]
      rw [equalAreaPhi_derivative_orthogonal _ _ hz,mul_zero]
  | inr i =>
    cases j with
    | inl j =>
      simp only [equalAreaConeColumn,Sum.elim_inl,Sum.elim_inr,
        Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,real_inner_smul_left]
      rw [real_inner_comm,equalAreaPhi_derivative_orthogonal _ _ hz,mul_zero]
    | inr j =>
      simp only [equalAreaConeColumn,Sum.elim_inr,Matrix.fromBlocks_apply₂₂,
        Matrix.smul_apply,smul_eq_mul,real_inner_smul_left,real_inner_smul_right,
        equalAreaGramMatrix_eq_inner]
      ring

theorem equalAreaConeMatrix_det_sq (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    (equalAreaConeMatrix z).det^2 = (z 0)^16 := by
  have h := congrArg Matrix.det (equalAreaConeMatrix_gram z hz)
  have hd : Matrix.det (fun _ : Fin 1 => fun _ : Fin 1 => (1:ℝ)) = 1 := by
    rw [Matrix.det_unique]
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_fromBlocks_zero₁₂,
    hd,Matrix.det_smul,equalAreaGramMatrix_det_one _ hz] at h
  norm_num [EqualAreaBasisIndex] at h
  nlinarith only [h]

theorem equalAreaConeMatrix_abs_det (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    |(equalAreaConeMatrix z).det| = (z 0)^8 := by
  apply (sq_eq_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,equalAreaConeMatrix_det_sq z hz]
  ring

theorem equalAreaConeCoordinateDerivative_abs_det (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    |(equalAreaConeCoordinateDerivative z).det| = (z 0)^8 := by
  change |LinearMap.det (equalAreaConeCoordinateDerivative z).toLinearMap| = _
  rw [←LinearMap.det_toMatrix']
  have h := equalAreaConeMatrix_abs_det z hz
  rw [equalAreaConeMatrix_eq_toMatrix,Matrix.det_submatrix_equiv_self] at h
  exact h

theorem equalAreaConeCoordinates_fderiv_abs_det (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    |(fderiv ℝ equalAreaConeCoordinates z).det| = (z 0)^8 := by
  rw [equalAreaConeCoordinates_fderiv z hz]
  exact equalAreaConeCoordinateDerivative_abs_det z hz

end SphericalRiesz
