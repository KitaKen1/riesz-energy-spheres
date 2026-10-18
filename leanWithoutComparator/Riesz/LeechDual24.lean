import Riesz.LeechLattice24
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The Leech lattice is self-dual (stage P24-1)

The scaled basis vectors have integer inner products `G_ij = (r_i · r_j)/8` (the integer row dot
products are divisible by `8`), so the lattice is integral. The Gram matrix `G` is unimodular;
its integer inverse (computed exactly offline and recorded as data) is checked by kernel
evaluation of `G · G⁻¹ = 1`. The dual basis vectors are then the integer points with coordinates
the rows of `G⁻¹`, so the dual lattice is the lattice itself. -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

abbrev leechInnerForm : LinearMap.BilinForm ℝ LeechAmbient := innerₗ LeechAmbient

/-- The integer Gram matrix of the scaled Leech basis. -/
def leechGram : Matrix (Fin 24) (Fin 24) ℤ := fun i j => leechDot i j / 8

/-- Its integer inverse (data). -/
def leechInverseGram : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![72, -20, -26, -20, -20, -12, -6, 3, -14, -9, -12, 12, -5, 6, 9, -9, -5, 3, 9, -6, 19, -9, -12, 11],
    ![-20, 8, 8, 6, 4, 4, 2, -3, 2, 3, 3, -5, 0, -2, -1, 4, 0, 0, -1, 2, -5, 3, 3, -4],
    ![-26, 8, 12, 8, 5, 4, 2, -2, 3, 4, 5, -7, 0, -1, -3, 5, 0, -1, -2, 4, -7, 4, 5, -6],
    ![-20, 6, 8, 8, 4, 4, 2, -3, 2, 2, 4, -5, 0, 0, -2, 3, 0, 1, -3, 3, -5, 2, 4, -4],
    ![-20, 4, 5, 4, 10, 3, 2, 1, 7, 1, 2, 1, 4, -3, -4, 0, 4, -2, -4, -1, -6, 2, 3, 0],
    ![-12, 4, 4, 4, 3, 4, 2, -3, 1, 1, 2, -2, 0, -1, -1, 2, 0, 1, -2, 1, -2, 1, 2, -2],
    ![-6, 2, 2, 2, 2, 2, 4, -4, 0, -1, 1, 0, 0, 1, -2, 1, 0, 2, -1, -1, 0, -1, 1, 0],
    ![3, -3, -2, -3, 1, -3, -4, 8, 3, 1, -1, 2, 2, -2, 0, -2, 2, -4, 0, 0, -2, 2, 0, 0],
    ![-14, 2, 3, 2, 7, 1, 0, 3, 8, 2, 2, 0, 4, -3, -3, -1, 4, -3, -3, -1, -4, 1, 1, 2],
    ![-9, 3, 4, 2, 1, 1, -1, 1, 2, 4, 2, -4, 0, -2, 0, 2, 0, -2, 0, 2, -2, 2, 1, -2],
    ![-12, 3, 5, 4, 2, 2, 1, -1, 2, 2, 4, -4, 0, 0, -2, 2, 0, 0, -2, 2, -2, 1, 2, -2],
    ![12, -5, -7, -5, 1, -2, 0, 2, 0, -4, -4, 8, 2, 0, 0, -4, 2, 0, 0, -4, 2, -2, -2, 4],
    ![-5, 0, 0, 0, 4, 0, 0, 2, 4, 0, 0, 2, 4, -2, -2, -2, 2, -1, -1, -1, -2, 0, 0, 2],
    ![6, -2, -1, 0, -3, -1, 1, -2, -3, -2, 0, 0, -2, 4, 0, 0, -1, 2, 0, 0, 2, -2, 0, 0],
    ![9, -1, -3, -2, -4, -1, -2, 0, -3, 0, -2, 0, -2, 0, 4, 0, -1, 0, 2, 0, 2, 0, -2, 0],
    ![-9, 4, 5, 3, 0, 2, 1, -2, -1, 2, 2, -4, -2, 0, 0, 4, -1, 0, 0, 2, -2, 2, 2, -4],
    ![-5, 0, 0, 0, 4, 0, 0, 2, 4, 0, 0, 2, 2, -1, -1, -1, 4, -2, -2, -2, -2, 0, 0, 2],
    ![3, 0, -1, 1, -2, 1, 2, -4, -3, -2, 0, 0, -1, 2, 0, 0, -2, 4, 0, 0, 2, -2, 0, 0],
    ![9, -1, -2, -3, -4, -2, -1, 0, -3, 0, -2, 0, -1, 0, 2, 0, -2, 0, 4, 0, 2, 0, -2, 0],
    ![-6, 2, 4, 3, -1, 1, -1, 0, -1, 2, 2, -4, -1, 0, 0, 2, -2, 0, 0, 4, -2, 2, 2, -4],
    ![19, -5, -7, -5, -6, -2, 0, -2, -4, -2, -2, 2, -2, 2, 2, -2, -2, 2, 2, -2, 8, -4, -4, 4],
    ![-9, 3, 4, 2, 2, 1, -1, 2, 1, 2, 1, -2, 0, -2, 0, 2, 0, -2, 0, 2, -4, 4, 2, -4],
    ![-12, 3, 5, 4, 3, 2, 1, 0, 1, 1, 2, -2, 0, 0, -2, 2, 0, 0, -2, 2, -4, 2, 4, -4],
    ![11, -4, -6, -4, 0, -2, 0, 0, 2, -2, -2, 4, 2, 0, 0, -4, 2, 0, 0, -4, 4, -4, -4, 8]
  ]

theorem leechGram_mul_inverse : leechGram * leechInverseGram = 1 := by
  decide +kernel

theorem leechInverse_mul_gram : leechInverseGram * leechGram = 1 :=
  mul_eq_one_comm.mp leechGram_mul_inverse

theorem leechIntegerPoint_eq_sum (z : Fin 24 → ℤ) :
    leechIntegerPoint z = ∑ j, (z j : ℝ) • leechEuclideanBasis j := by
  rw [leechIntegerPoint, leechMap_eq_sum]
  simp only [leechEuclideanBasis_apply, ← WithLp.toLp_sum, ← WithLp.toLp_smul]

theorem leechEuclideanBasis_inner (i j : Fin 24) :
    innerₗ LeechAmbient (leechEuclideanBasis i) (leechEuclideanBasis j) = (leechGram i j : ℝ) := by
  rw [innerₗ_apply_apply, leechEuclideanBasis_apply, leechEuclideanBasis_apply,
    EuclideanSpace.inner_toLp_toLp]
  rw [leechGram, Int.cast_div (leechDot_mod8 i j) (by norm_num)]
  simp only [leechDot, leechRowInt, dotProduct, Int.cast_sum, Int.cast_mul, leechMatrix,
    Matrix.row, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_trivial]
  have h8 : (Real.sqrt 8)⁻¹*(Real.sqrt 8)⁻¹ = (1:ℝ)/8 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  calc (Real.sqrt 8)⁻¹*(leechMatrixInt j k:ℝ)*((Real.sqrt 8)⁻¹*(leechMatrixInt i k:ℝ))
      = ((Real.sqrt 8)⁻¹*(Real.sqrt 8)⁻¹)*((leechMatrixInt i k:ℝ)*(leechMatrixInt j k:ℝ)) := by ring
    _ = (leechMatrixInt i k:ℝ)*(leechMatrixInt j k:ℝ)/8 := by rw [h8]; ring

def leechDualPoint (i : Fin 24) : LeechAmbient :=
  leechIntegerPoint (leechInverseGram i)

theorem leechDualPoint_pairing (i j : Fin 24) :
    innerₗ LeechAmbient (leechDualPoint i) (leechEuclideanBasis j) =
      if j = i then 1 else 0 := by
  rw [leechDualPoint, leechIntegerPoint_eq_sum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, leechEuclideanBasis_inner, smul_eq_mul]
  have h := congrFun (congrFun leechInverse_mul_gram i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  have h' : (∑ k, (leechInverseGram i k:ℝ)*(leechGram k j:ℝ)) =
      ((∑ k, leechInverseGram i k*leechGram k j : ℤ):ℝ) := by push_cast; rfl
  rw [h', h]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem leechInner_nondegenerate : leechInnerForm.Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

theorem leechEuclideanBasis_dual :
    leechInnerForm.dualBasis leechInner_nondegenerate leechEuclideanBasis = leechDualPoint :=
  (leechInnerForm.dualBasis_eq_iff leechInner_nondegenerate leechEuclideanBasis
    leechDualPoint).mpr leechDualPoint_pairing

theorem leechLattice_integral : leechLattice ≤ leechInnerForm.dualSubmodule leechLattice := by
  rw [leechLattice, Submodule.span_le]
  rintro _ ⟨i, rfl⟩ y hy
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  simp only [map_sum]
  apply sum_mem
  intro j _
  rw [← IsScalarTower.algebraMap_smul ℝ (f j), map_smul, smul_eq_mul,
    leechEuclideanBasis_inner]
  exact Submodule.mem_one.mpr ⟨f j * leechGram i j, by simp⟩

theorem leechLattice_selfDual : leechInnerForm.dualSubmodule leechLattice = leechLattice := by
  apply le_antisymm
  · rw [leechLattice, LinearMap.BilinForm.dualSubmodule_span_of_basis _
      leechInner_nondegenerate, leechEuclideanBasis_dual, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change leechDualPoint i ∈ leechLattice
    rw [leechLattice_mem_iff]
    exact ⟨leechInverseGram i, rfl⟩
  · exact leechLattice_integral

#print axioms leechGram_mul_inverse
#print axioms leechInverse_mul_gram
#print axioms leechIntegerPoint_eq_sum
#print axioms leechEuclideanBasis_inner
#print axioms leechDualPoint_pairing
#print axioms leechInner_nondegenerate
#print axioms leechEuclideanBasis_dual
#print axioms leechLattice_integral
#print axioms leechLattice_selfDual

end SphericalRiesz
