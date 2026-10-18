import Riesz.E8Lattice
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Self-duality of the actual E8 lattice by an integer certificate

The inverse Gram matrix is supplied as a known finite answer. Lean verifies
its multiplication and every dual-basis pairing against the actual Euclidean
basis. No search for the inverse and no general discriminant theory is needed.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
noncomputable section
namespace SphericalRiesz

abbrev e8InnerForm : LinearMap.BilinForm ℝ E8Ambient := innerₗ E8Ambient

def e8Gram : Matrix (Fin 8) (Fin 8) ℤ := !![
  4, -2, 0, 0, 0, 0, 0, 1;
  -2, 2, -1, 0, 0, 0, 0, 0;
  0, -1, 2, -1, 0, 0, 0, 0;
  0, 0, -1, 2, -1, 0, 0, 0;
  0, 0, 0, -1, 2, -1, 0, 0;
  0, 0, 0, 0, -1, 2, -1, 0;
  0, 0, 0, 0, 0, -1, 2, 0;
  1, 0, 0, 0, 0, 0, 0, 2]

def e8InverseGram : Matrix (Fin 8) (Fin 8) ℤ := !![
  14, 24, 20, 16, 12, 8, 4, -7;
  24, 42, 35, 28, 21, 14, 7, -12;
  20, 35, 30, 24, 18, 12, 6, -10;
  16, 28, 24, 20, 15, 10, 5, -8;
  12, 21, 18, 15, 12, 8, 4, -6;
  8, 14, 12, 10, 8, 6, 3, -4;
  4, 7, 6, 5, 4, 3, 2, -2;
  -7, -12, -10, -8, -6, -4, -2, 4]

def e8DualPoint (i : Fin 8) : E8Ambient :=
  e8EuclideanPoint (e8InverseGram i)

theorem e8EuclideanBasis_gram (i j : Fin 8) :
    innerₗ E8Ambient (e8EuclideanBasis i) (e8EuclideanBasis j) = (e8Gram i j : ℝ) := by
  simp only [innerₗ_apply_apply, e8EuclideanBasis, Module.Basis.map_apply, e8Basis_apply]
  change (∑ k : Fin 8, e8Matrix j k * e8Matrix i k) = _
  fin_cases i <;> fin_cases j <;> norm_num [e8Matrix, e8Gram, Fin.sum_univ_eight]

theorem e8Gram_mul_inverse : e8Gram * e8InverseGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, e8Gram, e8InverseGram, Fin.sum_univ_eight]

theorem e8DualPoint_pairing (i j : Fin 8) :
    innerₗ E8Ambient (e8DualPoint i) (e8EuclideanBasis j) =
      if j = i then 1 else 0 := by
  simp only [innerₗ_apply_apply, e8EuclideanBasis, Module.Basis.map_apply, e8Basis_apply]
  change (∑ k : Fin 8, e8Matrix j k * e8IntegerPoint (e8InverseGram i) k) = _
  fin_cases i <;> fin_cases j <;>
    norm_num [e8IntegerPoint, e8Map_eq_vector, e8InverseGram, e8Matrix, Fin.sum_univ_eight]

theorem e8Inner_nondegenerate : e8InnerForm.Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

theorem e8EuclideanBasis_dual :
    e8InnerForm.dualBasis e8Inner_nondegenerate e8EuclideanBasis = e8DualPoint :=
  (e8InnerForm.dualBasis_eq_iff e8Inner_nondegenerate e8EuclideanBasis
    e8DualPoint).mpr e8DualPoint_pairing

theorem e8Lattice_integral : e8Lattice ≤ e8InnerForm.dualSubmodule e8Lattice := by
  rw [e8Lattice, Submodule.span_le]
  rintro _ ⟨i, rfl⟩ y hy
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  simp only [map_sum]
  apply sum_mem
  intro j _
  rw [← IsScalarTower.algebraMap_smul ℝ (f j), map_smul, smul_eq_mul,
    e8EuclideanBasis_gram]
  exact Submodule.mem_one.mpr ⟨f j * e8Gram i j, by simp⟩

theorem e8Lattice_selfDual : e8InnerForm.dualSubmodule e8Lattice = e8Lattice := by
  apply le_antisymm
  · rw [e8Lattice, LinearMap.BilinForm.dualSubmodule_span_of_basis _
      e8Inner_nondegenerate, e8EuclideanBasis_dual, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change e8DualPoint i ∈ e8Lattice
    rw [e8Lattice_mem_iff]
    exact ⟨e8InverseGram i, rfl⟩
  · exact e8Lattice_integral

#print axioms e8EuclideanBasis_gram
#print axioms e8Gram_mul_inverse
#print axioms e8DualPoint_pairing
#print axioms e8Inner_nondegenerate
#print axioms e8EuclideanBasis_dual
#print axioms e8Lattice_integral
#print axioms e8Lattice_selfDual

end SphericalRiesz
