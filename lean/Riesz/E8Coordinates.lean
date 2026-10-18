/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license; see third_party/SpherePacking/LICENSE.
Authors of the source: Bhavik Mehta, Gareth Ma

The matrix, triangular determinant proof and basis construction below
are adapted from Sphere-Packing-Lean at commit
1e98fb493088948ca7bbf47d7faed49cc5b39fc4,
SpherePacking/Dim8/E8/Basic.lean. Names and the field are specialized to
this project and ℝ. The continuous coordinate map is added here.
-/
import Riesz.AnnularCutoff
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The concrete nonorthogonal E8 coordinate map

These are the eight rows of the source's E8 basis matrix. Its determinant
is one and its real coordinate map is injective. The equality of the
integer row span with the parity definition of E8 is not ported here.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz

def e8Matrix : Matrix (Fin 8) (Fin 8) ℝ := !![
    2,   0,   0,   0,   0,   0,   0,   0;
   -1,   1,   0,   0,   0,   0,   0,   0;
    0,  -1,   1,   0,   0,   0,   0,   0;
    0,   0,  -1,   1,   0,   0,   0,   0;
    0,   0,   0,  -1,   1,   0,   0,   0;
    0,   0,   0,   0,  -1,   1,   0,   0;
    0,   0,   0,   0,   0,  -1,   1,   0;
  2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹]

theorem e8Matrix_lowerTriangular : e8Matrix.BlockTriangular OrderDual.toDual := by
  simp [Matrix.BlockTriangular, e8Matrix, Fin.forall_fin_succ]

theorem e8Matrix_det : e8Matrix.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular e8Matrix e8Matrix_lowerTriangular]
  norm_num [e8Matrix, Fin.prod_univ_eight]

theorem e8Matrix_is_basis : LinearIndependent ℝ e8Matrix.row ∧
    Submodule.span ℝ (Set.range e8Matrix.row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det_apply]
  change IsUnit e8Matrix.det
  rw [e8Matrix_det]
  simp

def e8Basis : Module.Basis (Fin 8) ℝ (Fin 8 → ℝ) :=
  Module.Basis.mk e8Matrix_is_basis.1 e8Matrix_is_basis.2.ge

theorem e8Basis_apply (i : Fin 8) : e8Basis i = e8Matrix.row i := by
  rw [e8Basis, Module.Basis.coe_mk]

def e8Map : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  e8Basis.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem e8Map_injective : Function.Injective e8Map :=
  e8Basis.equivFun.symm.injective

theorem e8Map_eq_sum (v : Fin 8 → ℝ) : e8Map v = ∑ i, v i • e8Matrix.row i := by
  change e8Basis.equivFun.symm v = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [e8Basis_apply]

#print axioms e8Matrix_det
#print axioms e8Map_injective
#print axioms e8Map_eq_sum

end SphericalRiesz
