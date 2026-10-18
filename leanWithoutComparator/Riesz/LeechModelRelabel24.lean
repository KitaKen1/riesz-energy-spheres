import E8Leech.LeechBasis
import Riesz.LeechLattice24

/-! The two models of the Leech lattice differ by a relabelling of the coordinates.

This library uses the generator matrix `leechMatrixInt` (the Conway–Sloane matrix, as in
Sphere-Packing-Lean); the vendored development `E8Leech` defines its Leech set by congruences
modulo a binary Golay code in systematic form, with the basis `E8Leech.leechCandidateNumerators`.
The two Golay codes are different subsets of `𝔽₂²⁴`, so the two lattices are different subsets
of `ℝ²⁴`.  They are carried onto each other by the coordinate relabelling `leechRelabel`:

* `leechMatrixIntRelabelled_row`: every relabelled row of `leechMatrixInt` is an explicit integer
  combination of the rows of the `E8Leech` basis (coefficients `leechToCandidate`);
* `leechCandidateNumerators_row`: every row of the `E8Leech` basis is an explicit integer
  combination of the relabelled rows (coefficients `leechFromCandidate`).

Both are identities of integer vectors, checked by the kernel.  The relabelling is a linear
isometry of `ℝ²⁴` (`leechRelabelIsometry`), hence
`E8Leech.leechSet = leechRelabelIsometry '' leechLattice`
(`leechRelabelIsometry_image_leechLattice`).  The relabelling and the two coefficient matrices
were found by a computer search; nothing of that search is used as a proof input. -/

set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz

/-- The relabelling `p` of the 24 coordinates. -/
def leechRelabel : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 7, 22, 18, 15, 23, 14, 13, 11, 20, 9, 19, 17, 12, 6, 8, 21, 16, 4, 10, 5]

/-- The inverse of the relabelling. -/
def leechRelabelInv : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 21, 23, 17, 4, 18, 13, 22, 11, 16, 10, 9, 7, 20, 15, 6, 14, 12, 19, 5, 8]

theorem leechRelabel_leechRelabelInv : ∀ j : Fin 24, leechRelabel (leechRelabelInv j) = j := by
  decide

theorem leechRelabelInv_leechRelabel : ∀ j : Fin 24, leechRelabelInv (leechRelabel j) = j := by
  decide

/-- The relabelling as an equivalence of the index set; its inverse function is `leechRelabel`. -/
def leechRelabelEquiv : Fin 24 ≃ Fin 24 where
  toFun := leechRelabelInv
  invFun := leechRelabel
  left_inv := leechRelabel_leechRelabelInv
  right_inv := leechRelabelInv_leechRelabel

/-- The linear isometry of `ℝ²⁴` that relabels the coordinates: `(σ v) j = v (p j)`. -/
def leechRelabelIsometry : LeechAmbient ≃ₗᵢ[ℝ] LeechAmbient :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ leechRelabelEquiv

theorem leechRelabelIsometry_apply (v : LeechAmbient) (j : Fin 24) :
    leechRelabelIsometry v j = v (leechRelabel j) :=
  rfl

/-- The generator matrix of this library with relabelled columns. -/
def leechMatrixIntRelabelled : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => leechMatrixInt i (leechRelabel j)

/-- Coefficients of the relabelled rows of `leechMatrixInt` in the basis of `E8Leech`. -/
def leechToCandidate : Matrix (Fin 24) (Fin 24) ℤ :=
  !![  4,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -2,  -2,  -2,  -2,  -2,  -2,  -2,  -2,  -2,  -2, -11;
       8,   4,  -2,  -2,  -2,  -2,  -2,  -2,  -2,  -2,  -2,  -2,   9,   0,   0,   1,   0,   0,   0,   1,   1,   1,   0,   7;
       2,   0,   2,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -2,  -1,  -2,  -2,  -2,  -1,  -1,  -1,  -2,  -1,  -9;
       2,   0,   0,   2,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -2,  -2,  -2,  -1,  -1,  -1,  -2,  -1,  -2,  -9;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -1,  -5;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -5;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,   0,  -1,  -1,  -1,  -1,  -1,  -5;
       4,   2,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   3,  -1,  -1,  -1,  -1,   0,   0,   0,   0,   0,  -1,  -1;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,   0,  -1,  -1,  -1,  -1,  -5;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -5;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -5;
       4,   2,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   0,   3,   0,  -1,  -1,  -1,  -1,   0,   0,   0,   0,   0,  -1;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -5;
       4,   2,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -1,   4,   0,   0,   0,   0,   0,   0,   0,   0,   1,   0,   3;
       1,   0,   1,   0,   0,   0,   0,   0,   0,   1,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -1,  -1,  -1,   0,  -5;
       1,   0,   0,   1,   1,   0,   0,   1,   0,   0,   0,   1,  -2,  -1,  -2,  -2,  -1,  -1,  -1,  -2,  -1,  -1,  -2,  -9;
       2,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -1,  -1,  -5;
       1,   0,   1,   0,   1,   0,   0,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -1,   0,  -1,  -1,  -5;
       1,   0,   0,   1,   0,   0,   1,   0,   0,   0,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,   0,  -1,  -1,   0,  -1,  -5;
       4,   2,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   0,   4,   0,   0,   0,   0,   0,   0,   0,   1,   1,   0,   3;
       3,   2,   0,   0,  -1,  -1,  -1,  -1,  -1,  -1,  -1,  -1,   4,   0,   0,   0,   0,   0,   1,   1,   1,   1,   0,   4;
       0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0;
       0,   0,   0,   0,   0,   1,   1,   0,   0,   1,   0,   0,  -1,  -1,  -1,   0,   0,  -1,   0,  -1,  -1,  -1,   0,  -4;
       0,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0,   0]

/-- Coefficients of the rows of the basis of `E8Leech` in the relabelled rows of
`leechMatrixInt`. -/
def leechFromCandidate : Matrix (Fin 24) (Fin 24) ℤ :=
  !![-4,  1,  1,  1,  1,  1,  0,  0,  1,  1,  1, -1,  1, -1,  0,  0,  0,  0,  0,  1, -1,  1,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1;
      0,  0,  0,  0,  0,  1,  1, -1, -1,  0,  0,  0,  0,  0,  0,  0, -1,  1,  0,  0,  1,  0,  0,  0;
      0,  0,  0,  1, -1,  1,  0, -1, -1,  0,  1, -1,  0,  0,  0,  0, -1,  1,  0,  1,  1,  0,  0,  0;
      0,  0,  0,  0,  0,  0, -1,  1,  0,  1,  1, -1,  0, -1,  0,  0, -1,  0,  0,  1,  0,  1,  0,  0;
     -3,  0,  1,  1,  1,  1,  0,  0,  1,  1,  1, -1,  0,  0, -1,  0,  0,  0, -1,  1,  0,  0,  1,  0;
      0,  0,  0, -1,  0,  0,  0,  1,  0,  1,  0,  0,  0, -1,  0,  0,  0, -1,  1,  0,  0,  1,  0,  0;
     -3,  1,  1,  0,  1,  1,  0,  0,  1,  1,  1, -1,  0, -1,  0,  1,  0, -1,  0,  0,  0,  1,  0,  0;
      3, -1, -2, -1,  0,  0,  1, -1,  0, -1,  0,  1,  0,  0,  0, -1,  0,  1,  0, -1,  2, -1, -1,  2;
      0,  0,  0,  0,  0,  0, -1,  1,  0,  1,  0, -1,  0, -1,  1,  0,  0, -1,  0,  1,  0,  1,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0;
      0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0, -1,  0,  0, -1,  0,  0,  1,  0,  1,  0,  0;
      4, -1, -1, -1, -1, -1,  0,  0, -1,  0,  0,  0, -1,  0,  0,  0, -1,  0,  0,  0,  2,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  1,  1, -1, -1, -1,  0,  0,  1,  1, -2,  0,  0,  0,  0, -1,  0,  0,  2,  0,  0,  0,  0;
      0,  1,  0,  1,  0,  0,  1, -2, -1, -1,  0,  0,  0,  0,  0,  0, -1,  2,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
     -3,  1,  1,  0,  2, -1, -1,  2,  2,  1,  0,  0,  1, -2,  0,  0,  1, -2,  0,  0, -2,  2,  0,  0;
      0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  1, -1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0;
     -1,  0,  0,  0,  0,  2,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0]

theorem leechMatrixIntRelabelled_row (i : Fin 24) : leechMatrixIntRelabelled i =
    ∑ k, leechToCandidate i k • E8Leech.leechCandidateNumerators k := by
  fin_cases i <;> decide +kernel

theorem leechCandidateNumerators_row (i : Fin 24) : E8Leech.leechCandidateNumerators i =
    ∑ k, leechFromCandidate i k • leechMatrixIntRelabelled k := by
  fin_cases i <;> decide +kernel

/-- The relabelled basis vector of this library, as a coordinate vector of `E8Leech`. -/
theorem leechRelabelIsometry_basis (i : Fin 24) :
    leechRelabelIsometry (leechEuclideanBasis i) =
      E8Leech.leechCoordinatesLinear (leechMatrixIntRelabelled i) := by
  ext j
  rw [leechRelabelIsometry_apply, leechEuclideanBasis_apply]
  change leechMatrix i (leechRelabel j) =
    ((leechMatrixInt i (leechRelabel j) : ℤ) : ℝ)/Real.sqrt 8
  rw [leechMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, div_eq_inv_mul]

/-- The relabelling carries the Leech lattice of this library onto the Leech lattice of the
vendored development. -/
theorem leechRelabelIsometry_map_leechLattice :
    Submodule.map (leechRelabelIsometry.toLinearEquiv.toLinearMap.restrictScalars ℤ)
      leechLattice = E8Leech.leechLattice := by
  rw [leechLattice, Submodule.map_span, E8Leech.leechLattice_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change leechRelabelIsometry (leechEuclideanBasis i) ∈ _
    rw [leechRelabelIsometry_basis, leechMatrixIntRelabelled_row, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, E8Leech.leechEuclideanBasis_apply k⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [E8Leech.leechEuclideanBasis_apply]
    change E8Leech.leechCoordinatesLinear (E8Leech.leechCandidateNumerators i) ∈ _
    rw [leechCandidateNumerators_row, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨leechEuclideanBasis k, ⟨k, rfl⟩, leechRelabelIsometry_basis k⟩)

/-- The Leech set of the vendored development is the image of the Leech lattice of this library
under the coordinate relabelling. -/
theorem leechRelabelIsometry_image_leechLattice :
    E8Leech.leechSet = leechRelabelIsometry '' (leechLattice : Set LeechAmbient) := by
  rw [← E8Leech.coe_leechLattice, ← leechRelabelIsometry_map_leechLattice, Submodule.map_coe]
  rfl

end SphericalRiesz
