/-
Copyright (c) 2025 Bhavik Mehta, Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in licenses/Sphere-Packing-Apache-2.0.txt.
Authors: Bhavik Mehta, Gareth Ma; adapted for this project by Codex

The lower triangular basis and determinant/basis proof pattern are adapted from
Sphere-Packing-Lean, commit cbe754e5b699945fd391e6398e6293e9fafa16ec,
SpherePacking/Basic/E8.lean. Integer reconstruction uses this project's doubled-coordinate
congruences directly, rather than importing the upstream packing infrastructure.
-/
import E8Leech.E8Geometry
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# A triangular E8 basis and covolume-one lattice

The triangular matrix has determinant one. Explicit integer coefficients reconstruct every
point of the doubled-coordinate E8 model, avoiding an eight-dimensional classification.
-/

noncomputable section

namespace E8Leech

open Set Matrix Module MeasureTheory
open scoped ENNReal

def e8TriangularNumerators : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 0, 0, 0, 0, 0, 0, 0;
     -2, 2, 0, 0, 0, 0, 0, 0;
     0, -2, 2, 0, 0, 0, 0, 0;
     0, 0, -2, 2, 0, 0, 0, 0;
     0, 0, 0, -2, 2, 0, 0, 0;
     0, 0, 0, 0, -2, 2, 0, 0;
     0, 0, 0, 0, 0, -2, 2, 0;
     1, 1, 1, 1, 1, 1, 1, 1]

def e8TriangularMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => (e8TriangularNumerators i j : ℝ) / 2

theorem e8TriangularMatrix_lower :
    e8TriangularMatrix.BlockTriangular OrderDual.toDual := by
  norm_num [Matrix.BlockTriangular, e8TriangularMatrix, e8TriangularNumerators,
    Fin.forall_fin_succ]

theorem e8TriangularMatrix_det : e8TriangularMatrix.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ e8TriangularMatrix_lower]
  norm_num [e8TriangularMatrix, e8TriangularNumerators, Fin.prod_univ_succ]

theorem e8TriangularMatrix_is_basis :
    LinearIndependent ℝ e8TriangularMatrix.row ∧
      Submodule.span ℝ (Set.range e8TriangularMatrix.row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det_apply]
  change IsUnit e8TriangularMatrix.det
  rw [e8TriangularMatrix_det]
  exact isUnit_one

def e8CoordinateBasis : Basis (Fin 8) ℝ (Fin 8 → ℝ) :=
  Basis.mk e8TriangularMatrix_is_basis.1 e8TriangularMatrix_is_basis.2.ge

theorem e8CoordinateBasis_apply (i : Fin 8) : e8CoordinateBasis i = e8TriangularMatrix.row i := by
  rw [e8CoordinateBasis, Basis.coe_mk]

def e8EuclideanBasis : Basis (Fin 8) ℝ (Ambient 8) :=
  e8CoordinateBasis.map (WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm

theorem e8EuclideanBasis_apply (i : Fin 8) :
    e8EuclideanBasis i = halfCoordinates (e8TriangularNumerators i) := by
  ext j
  simp [e8EuclideanBasis, e8CoordinateBasis_apply, halfCoordinates, e8TriangularMatrix]

def e8Lattice : Submodule ℤ (Ambient 8) := Submodule.span ℤ (Set.range e8EuclideanBasis)

instance : DiscreteTopology e8Lattice := inferInstanceAs
  (DiscreteTopology (Submodule.span ℤ (Set.range e8EuclideanBasis)))

instance : IsZLattice ℝ e8Lattice := inferInstanceAs
  (IsZLattice ℝ (Submodule.span ℤ (Set.range e8EuclideanBasis)))

private theorem triangular_rows_mem : ∀ i, e8TriangularNumerators i ∈ e8Numerators := by
  intro i
  refine ⟨fun j => Int.dvd_of_emod_eq_zero ?_, Int.dvd_of_emod_eq_zero ?_⟩
  · fin_cases i <;> fin_cases j <;> decide
  · fin_cases i <;> decide

def e8NumeratorSubmodule : Submodule ℤ (Fin 8 → ℤ) where
  carrier := e8Numerators
  zero_mem' := by simp [e8Numerators]
  add_mem' := by
    intro z w hz hw
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [Pi.add_apply, add_sub_add_comm] using dvd_add (hz.1 i) (hw.1 i)
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using dvd_add hz.2 hw.2
  smul_mem' := by
    intro k z hz
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [Pi.smul_apply, smul_eq_mul, ← mul_sub] using dvd_mul_of_dvd_right (hz.1 i) k
    · simpa only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] using dvd_mul_of_dvd_right hz.2 k

def halfCoordinatesLinear : (Fin 8 → ℤ) →ₗ[ℤ] Ambient 8 where
  toFun := halfCoordinates
  map_add' z w := by ext i; simp [halfCoordinates, add_div]
  map_smul' k z := by ext i; simp [halfCoordinates]; ring

theorem e8Lattice_subset_e8Set : (e8Lattice : Set (Ambient 8)) ⊆ e8Set := by
  have hmap : (e8NumeratorSubmodule.map halfCoordinatesLinear : Set (Ambient 8)) = e8Set := rfl
  rw [← hmap]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change e8EuclideanBasis i ∈ e8NumeratorSubmodule.map halfCoordinatesLinear
  rw [Submodule.mem_map]
  exact ⟨e8TriangularNumerators i, triangular_rows_mem i, e8EuclideanBasis_apply i |>.symm⟩

def e8IntegerCoefficients (z : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![(∑ i, z i) / 4 - 2 * z 7,
    (z 1 + z 2 + z 3 + z 4 + z 5 + z 6 - 6 * z 7) / 2,
    (z 2 + z 3 + z 4 + z 5 + z 6 - 5 * z 7) / 2,
    (z 3 + z 4 + z 5 + z 6 - 4 * z 7) / 2,
    (z 4 + z 5 + z 6 - 3 * z 7) / 2,
    (z 5 + z 6 - 2 * z 7) / 2,
    (z 6 - z 7) / 2,
    z 7]

theorem e8IntegerCoefficients_reconstruct {z : Fin 8 → ℤ} (hz : z ∈ e8Numerators) :
    ∑ i, e8IntegerCoefficients z i • e8TriangularNumerators i = z := by
  have h0 := hz.1 0
  have h1 := hz.1 1
  have h2 := hz.1 2
  have h3 := hz.1 3
  have h4 := hz.1 4
  have h5 := hz.1 5
  have h6 := hz.1 6
  have h7 := hz.1 7
  have hsum := hz.2
  simp only [Fin.sum_univ_eight] at hsum
  ext j
  fin_cases j <;>
    simp [e8IntegerCoefficients, e8TriangularNumerators, Fin.sum_univ_eight] <;> omega

theorem e8Set_subset_e8Lattice : e8Set ⊆ (e8Lattice : Set (Ambient 8)) := by
  rintro x ⟨z, hz, rfl⟩
  have heq : halfCoordinates z = ∑ i, e8IntegerCoefficients z i • e8EuclideanBasis i := by
    calc
      _ = halfCoordinatesLinear (∑ i, e8IntegerCoefficients z i • e8TriangularNumerators i) :=
        congrArg halfCoordinatesLinear (e8IntegerCoefficients_reconstruct hz).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        congr 1
        exact (e8EuclideanBasis_apply i).symm
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem coe_e8Lattice : (e8Lattice : Set (Ambient 8)) = e8Set :=
  Set.Subset.antisymm e8Lattice_subset_e8Set e8Set_subset_e8Lattice

theorem volume_e8CoordinateFundamentalDomain :
    volume (ZSpan.fundamentalDomain e8CoordinateBasis) = 1 := by
  rw [ZSpan.volume_fundamentalDomain]
  have hm : Matrix.of e8CoordinateBasis = e8TriangularMatrix := by
    ext i j
    simp [e8CoordinateBasis_apply, Matrix.row]
  rw [hm, e8TriangularMatrix_det]
  norm_num

theorem volume_e8FundamentalDomain : volume (ZSpan.fundamentalDomain e8EuclideanBasis) = 1 := by
  have heq : (@WithLp.ofLp 2 (Fin 8 → ℝ)) ⁻¹'
      ZSpan.fundamentalDomain e8CoordinateBasis = ZSpan.fundamentalDomain e8EuclideanBasis := by
    ext x
    simp [ZSpan.fundamentalDomain, e8EuclideanBasis, Basis.map_repr]
  rw [← heq,
    (PiLp.volume_preserving_ofLp (ι := Fin 8)).measure_preimage
      (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet,
    volume_e8CoordinateFundamentalDomain]

theorem e8Lattice_covolume : ZLattice.covolume e8Lattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain e8Lattice volume
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume)]
  simp [measureReal_def, volume_e8FundamentalDomain]

theorem e8Lattice_rank : Module.finrank ℤ e8Lattice = 8 := by
  rw [ZLattice.rank ℝ e8Lattice]
  simp [Ambient]

end E8Leech
