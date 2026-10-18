import Riesz.E8Covolume
import Riesz.E8Volume
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Riesz.PoissonLattice
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Riesz.E8ThetaTransform
import Riesz.E8GaussianContact8
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness

/-! The triangular lattice of covolume one and its Gaussian certificate contract (stage S2-1 of the
S² chain).

The module has seven parts, the dimension-2 counterparts of the Leech lattice modules.

* `HexLattice2`: with `b = √3/2`, the lattice of the points `(√b)⁻¹ • (j + k/2, k b)`; covolume
  one, norm form `(2/√3)(j² + j k + k²)`, minimal squared norm `2/√3`.  The lattice is neither
  even nor integral.
* `HexDual2`: the dual lattice is the quarter turn of the lattice; sums of radial functions over
  the dual lattice and over the lattice agree.
* `HexTheta2`: the theta series and its inversion `θ(-1/τ) = (τ/i) θ(τ)` by Poisson summation.
* `HexGaussianContact2`: the contract `HexGaussianContactCertificate2 β f` (a Schwartz minorant
  of the Gaussian `exp(-π β |x|²)` with nonnegative Fourier transform, equality at the nonzero
  lattice points and Fourier zeros at the nonzero dual points), its value identity
  `f̂(0) - f(0) = Θ(β) - 1`, the form for a real Schwartz function and the reciprocal certificate
  `β ↔ 1/β`.
* `HexRegularized2`: `Θ(1/t) = t Θ(t)`, the regularized theta `Θ(t) - 1 - 1/t`, its decay and
  Mellin convergence on `0 < Re s < 1`.
* `HexEpstein2`: the functional-equation pair of weight one, the completed function and the
  Epstein zeta function in the variable `u = s/2`, with its series for `Re u > 1`.
* `PatchSupportHex2`: the inverse of the coordinate map.

No certificate is constructed here: the existence of `HexGaussianContactCertificate2 β f` for
every `β > 0` is the input of the S² chain (a theorem of the OpenAI triangular-lattice
development, not yet connected to this project). -/

section

/-
Copyright (c) 2025 the Sphere-Packing-Lean authors. All rights reserved.
Released under Apache 2.0 license; see third_party/SpherePacking/LICENSE.

Only the construction of a basis of `Fin n → ℝ` from a matrix with a unit determinant
(`hexMatrix_is_basis`, `hexBasis`, `hexBasis_apply`) is still adapted, through `E8Coordinates`
and `LeechLattice24`, from Sphere-Packing-Lean at commit
1e98fb493088948ca7bbf47d7faed49cc5b39fc4, SpherePacking/Dim8/E8/Basic.lean. The `2 × 2`
generator matrix, its determinant, the coordinate formulas, the norm form and the minimal norm of
the triangular lattice are new in this project; the Euclidean lattice API and the covolume
argument mirror `LeechLattice24`.
-/

/-! # The triangular lattice of covolume one (stage S2-1)

With `b = √3/2`, the rows `(√b)⁻¹ • (1, 0)` and `(√b)⁻¹ • (1/2, b)` span the triangular
(hexagonal) lattice of covolume one in `ℝ²`: the scaled `2 × 2` matrix has determinant one. The
lattice point with integer coordinates `(j, k)` is `(√b)⁻¹ • (j + k/2, k b)`, its squared norm is
`(2/√3) (j² + j k + k²)`, and every nonzero lattice vector has squared norm at least `2/√3 > 1`.
The lattice is neither even nor self-dual; its dual is treated in `HexDual2`. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SphericalRiesz

/-! ## The constant `b = √3/2` -/

/-- `b = √3/2`, the height of an equilateral triangle of side one. -/
def hexB : ℝ := Real.sqrt 3 / 2

theorem hexB_pos : 0 < hexB := by
  rw [hexB]
  exact div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)

theorem hexB_sq : hexB^2 = 3/4 := by
  rw [hexB, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

theorem hexB_inv : hexB⁻¹ = 2/Real.sqrt 3 := by
  rw [hexB, inv_div]

/-- The square of the scaling factor `(√b)⁻¹` is `b⁻¹`. -/
theorem hexScale_mul_self : (Real.sqrt hexB)⁻¹*(Real.sqrt hexB)⁻¹ = hexB⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hexB_pos.le]

theorem hexScale_mul_self_mul : (Real.sqrt hexB)⁻¹*(Real.sqrt hexB)⁻¹*hexB = 1 := by
  rw [hexScale_mul_self, inv_mul_cancel₀ hexB_pos.ne']

/-- The minimal squared norm `2/√3` of the lattice is larger than one. -/
theorem one_lt_two_div_sqrt_three : (1:ℝ) < 2/Real.sqrt 3 := by
  have h3 : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  exact (one_lt_div (Real.sqrt_pos.mpr (by norm_num))).mpr h3

/-! ## The generator matrix -/

/-- The generator matrix before scaling: rows `(1, 0)` and `(1/2, b)`. -/
def hexMatrixBase : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1/2, hexB]

theorem hexMatrixBase_apply_zero_zero : hexMatrixBase 0 0 = 1 := rfl

theorem hexMatrixBase_apply_zero_one : hexMatrixBase 0 1 = 0 := rfl

theorem hexMatrixBase_apply_one_zero : hexMatrixBase 1 0 = 1/2 := rfl

theorem hexMatrixBase_apply_one_one : hexMatrixBase 1 1 = hexB := rfl

theorem hexMatrixBase_det : hexMatrixBase.det = hexB := by
  rw [hexMatrixBase, Matrix.det_fin_two_of]
  ring

/-- The scaled real generator matrix: rows `(√b)⁻¹ • (1, 0)` and `(√b)⁻¹ • (1/2, b)`. -/
def hexMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt hexB)⁻¹ • hexMatrixBase

theorem hexMatrix_det : hexMatrix.det = 1 := by
  rw [hexMatrix, Matrix.det_smul, Fintype.card_fin, hexMatrixBase_det, inv_pow,
    Real.sq_sqrt hexB_pos.le]
  exact inv_mul_cancel₀ hexB_pos.ne'

theorem hexMatrix_is_basis : LinearIndependent ℝ hexMatrix.row ∧
    Submodule.span ℝ (Set.range hexMatrix.row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det_apply]
  change IsUnit hexMatrix.det
  rw [hexMatrix_det]
  simp

def hexBasis : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  Module.Basis.mk hexMatrix_is_basis.1 hexMatrix_is_basis.2.ge

theorem hexBasis_apply (i : Fin 2) : hexBasis i = hexMatrix.row i := by
  rw [hexBasis, Module.Basis.coe_mk]

/-- The triangular coordinate map: integer coordinates go to lattice points. -/
def hexMap : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  hexBasis.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem hexMap_injective : Function.Injective hexMap :=
  hexBasis.equivFun.symm.injective

theorem hexMap_eq_sum (v : Fin 2 → ℝ) : hexMap v = ∑ i, v i • hexMatrix.row i := by
  change hexBasis.equivFun.symm v = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [hexBasis_apply]

/-! ## The Euclidean triangular lattice -/

abbrev HexAmbient := EuclideanSpace ℝ (Fin 2)

def hexEuclideanBasis : Module.Basis (Fin 2) ℝ HexAmbient :=
  hexBasis.map (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm

def hexLattice : Submodule ℤ HexAmbient :=
  Submodule.span ℤ (Set.range hexEuclideanBasis)

instance : DiscreteTopology hexLattice := by
  unfold hexLattice
  infer_instance

instance : IsZLattice ℝ hexLattice := by
  unfold hexLattice
  infer_instance

theorem hexEuclideanBasis_apply (i : Fin 2) :
    (hexEuclideanBasis i : HexAmbient) = WithLp.toLp 2 (hexMatrix.row i) := by
  rw [hexEuclideanBasis, Module.Basis.map_apply, hexBasis_apply]
  rfl

/-- Integer combinations of the scaled rows. -/
def hexIntegerPoint (z : Fin 2 → ℤ) : HexAmbient :=
  WithLp.toLp 2 (hexMap (fun i => (z i : ℝ)))

theorem hexLattice_mem_iff (x : HexAmbient) :
    x ∈ hexLattice ↔ ∃ z : Fin 2 → ℤ, hexIntegerPoint z = x := by
  rw [hexLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    rw [hexIntegerPoint, hexMap_eq_sum]
    simp only [hexEuclideanBasis_apply, ← WithLp.toLp_sum, Int.cast_smul_eq_zsmul ℝ]
    congr 1
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hexIntegerPoint, hexMap_eq_sum]
    simp only [hexEuclideanBasis_apply]
    rw [← WithLp.toLp_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Int.cast_smul_eq_zsmul ℝ]
    rfl

theorem hexLattice_rank : Module.finrank ℤ hexLattice = 2 := by
  rw [ZLattice.rank ℝ]
  exact finrank_euclideanSpace_fin

theorem hexLattice_finite_norm_lt (R : ℝ) :
    {x : hexLattice | ‖(x : HexAmbient)‖ < R}.Finite := by
  have hf := ZSpan.setFinite_inter hexEuclideanBasis
    (s := Metric.ball (0 : HexAmbient) R) Metric.isBounded_ball
  have hpre := hf.preimage_embedding (Function.Embedding.subtype (fun x => x ∈ hexLattice))
  convert hpre using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.Embedding.subtype_apply,
    Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨h, x.property⟩
  · intro h
    exact h.1

/-! ## Coordinates of the lattice points -/

/-- Two points of the plane with the same two coordinates are equal. -/
theorem hexAmbient_ext {x y : HexAmbient} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y :=
  PiLp.ext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)

/-- The Euclidean inner product of the plane in coordinates. -/
theorem hexInner_eq (x y : HexAmbient) : inner ℝ x y = x 0*y 0+x 1*y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply]

/-- The squared Euclidean norm of the plane in coordinates. -/
theorem hexNorm_sq_eq (x : HexAmbient) : ‖x‖^2 = x 0^2+x 1^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem hexIntegerPoint_apply (z : Fin 2 → ℤ) (k : Fin 2) :
    (hexIntegerPoint z) k = (Real.sqrt hexB)⁻¹*
      ((z 0 : ℝ)*hexMatrixBase 0 k+(z 1 : ℝ)*hexMatrixBase 1 k) := by
  simp only [hexIntegerPoint, PiLp.toLp_apply, hexMap_eq_sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hexMatrix, Matrix.row, Matrix.smul_apply]
  rw [Fin.sum_univ_two]
  ring

theorem hexIntegerPoint_apply_zero (z : Fin 2 → ℤ) :
    (hexIntegerPoint z) 0 = (Real.sqrt hexB)⁻¹*((z 0 : ℝ)+(z 1 : ℝ)/2) := by
  rw [hexIntegerPoint_apply, hexMatrixBase_apply_zero_zero, hexMatrixBase_apply_one_zero]
  ring

theorem hexIntegerPoint_apply_one (z : Fin 2 → ℤ) :
    (hexIntegerPoint z) 1 = (Real.sqrt hexB)⁻¹*((z 1 : ℝ)*hexB) := by
  rw [hexIntegerPoint_apply, hexMatrixBase_apply_zero_one, hexMatrixBase_apply_one_one]
  ring

/-- The lattice point `(√b)⁻¹ • (j + k/2, k b)` with integer coordinates `(j, k)`, in the
spelling of the triangular lattice of density one used for the Gaussian certificates. -/
def hexTriangularPoint (j k : ℤ) : HexAmbient :=
  (Real.sqrt hexB)⁻¹ • (!₂[(j : ℝ)+(k : ℝ)/2, (k : ℝ)*hexB] : HexAmbient)

theorem hexTriangularPoint_apply_zero (j k : ℤ) :
    (hexTriangularPoint j k) 0 = (Real.sqrt hexB)⁻¹*((j : ℝ)+(k : ℝ)/2) := rfl

theorem hexTriangularPoint_apply_one (j k : ℤ) :
    (hexTriangularPoint j k) 1 = (Real.sqrt hexB)⁻¹*((k : ℝ)*hexB) := rfl

theorem hexIntegerPoint_eq_triangularPoint (z : Fin 2 → ℤ) :
    hexIntegerPoint z = hexTriangularPoint (z 0) (z 1) :=
  hexAmbient_ext
    ((hexIntegerPoint_apply_zero z).trans (hexTriangularPoint_apply_zero (z 0) (z 1)).symm)
    ((hexIntegerPoint_apply_one z).trans (hexTriangularPoint_apply_one (z 0) (z 1)).symm)

theorem hexTriangularPoint_eq_integerPoint (j k : ℤ) :
    hexTriangularPoint j k = hexIntegerPoint ![j, k] :=
  (hexIntegerPoint_eq_triangularPoint ![j, k]).symm

theorem hexTriangularPoint_mem (j k : ℤ) : hexTriangularPoint j k ∈ hexLattice :=
  (hexLattice_mem_iff _).mpr ⟨![j, k], (hexTriangularPoint_eq_integerPoint j k).symm⟩

/-- The lattice is the set of the points `(√b)⁻¹ • (j + k/2, k b)`. -/
theorem hexLattice_mem_iff_triangular (x : HexAmbient) :
    x ∈ hexLattice ↔ ∃ j k : ℤ, hexTriangularPoint j k = x := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (hexLattice_mem_iff x).mp hx
    exact ⟨z 0, z 1, (hexIntegerPoint_eq_triangularPoint z).symm.trans hz⟩
  · rintro ⟨j, k, rfl⟩
    exact hexTriangularPoint_mem j k

theorem hexLattice_coe_eq_range :
    (hexLattice : Set HexAmbient) = Set.range (fun p : ℤ × ℤ => hexTriangularPoint p.1 p.2) := by
  ext x
  rw [SetLike.mem_coe, hexLattice_mem_iff_triangular, Set.mem_range]
  constructor
  · rintro ⟨j, k, h⟩
    exact ⟨(j, k), h⟩
  · rintro ⟨p, h⟩
    exact ⟨p.1, p.2, h⟩

theorem hexTriangularPoint_zero : hexTriangularPoint 0 0 = 0 := by
  apply hexAmbient_ext
  · rw [hexTriangularPoint_apply_zero]
    simp
  · rw [hexTriangularPoint_apply_one]
    simp

/-! ## The norm form and the minimal norm -/

/-- `‖(√b)⁻¹ • (j + k/2, k b)‖² = (2/√3) (j² + j k + k²)`. -/
theorem hexTriangularPoint_norm_sq (j k : ℤ) :
    ‖hexTriangularPoint j k‖^2 = 2/Real.sqrt 3*((j^2+j*k+k^2 : ℤ) : ℝ) := by
  rw [hexNorm_sq_eq, hexTriangularPoint_apply_zero, hexTriangularPoint_apply_one, ← hexB_inv]
  push_cast
  linear_combination (((j : ℝ)+(k : ℝ)/2)^2+(k : ℝ)^2*hexB^2)*hexScale_mul_self+
    (hexB⁻¹*(k : ℝ)^2)*hexB_sq

theorem hexIntegerPoint_norm_sq (z : Fin 2 → ℤ) :
    ‖hexIntegerPoint z‖^2 = 2/Real.sqrt 3*(((z 0)^2+z 0*z 1+(z 1)^2 : ℤ) : ℝ) := by
  rw [hexIntegerPoint_eq_triangularPoint, hexTriangularPoint_norm_sq]

/-- The binary quadratic form `j² + j k + k²` is at least one away from the origin. -/
theorem hexForm_ge_one {j k : ℤ} (h : ¬(j = 0 ∧ k = 0)) : 1 ≤ j^2+j*k+k^2 := by
  by_cases hk : k = 0
  · have hj : j ≠ 0 := fun hj => h ⟨hj, hk⟩
    have h1 : 0 < j*j := mul_self_pos.mpr hj
    rw [hk]
    nlinarith
  · have h1 : 0 < k*k := mul_self_pos.mpr hk
    nlinarith [sq_nonneg (2*j+k)]

/-- Every lattice vector has squared norm in `(2/√3) ℕ`. -/
theorem hexLattice_norm_sq_eq (x : hexLattice) :
    ∃ n : ℕ, ‖(x : HexAmbient)‖^2 = 2/Real.sqrt 3*(n : ℝ) := by
  obtain ⟨j, k, hjk⟩ := (hexLattice_mem_iff_triangular x).mp x.property
  rw [← hjk, hexTriangularPoint_norm_sq]
  have h0 : 0 ≤ j^2+j*k+k^2 := by nlinarith [sq_nonneg (2*j+k), sq_nonneg k]
  refine ⟨Int.toNat (j^2+j*k+k^2), ?_⟩
  have hcast : ((Int.toNat (j^2+j*k+k^2) : ℕ) : ℝ) = ((j^2+j*k+k^2 : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [hcast]

/-- Nonzero vectors of the triangular lattice of covolume one have squared norm at least
`2/√3` (this replaces evenness of the Leech lattice). -/
theorem hexLattice_norm_sq_ge (x : hexLattice) (hx : (x : HexAmbient) ≠ 0) :
    2/Real.sqrt 3 ≤ ‖(x : HexAmbient)‖^2 := by
  obtain ⟨j, k, hjk⟩ := (hexLattice_mem_iff_triangular x).mp x.property
  rw [← hjk] at hx ⊢
  rw [hexTriangularPoint_norm_sq]
  have hq : ¬(j = 0 ∧ k = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hx hexTriangularPoint_zero
  have h1 : (1:ℝ) ≤ ((j^2+j*k+k^2 : ℤ) : ℝ) := by
    exact_mod_cast hexForm_ge_one hq
  have hpos : (0:ℝ) ≤ 2/Real.sqrt 3 := by positivity
  calc 2/Real.sqrt 3 = 2/Real.sqrt 3*1 := (mul_one _).symm
    _ ≤ 2/Real.sqrt 3*((j^2+j*k+k^2 : ℤ) : ℝ) := mul_le_mul_of_nonneg_left h1 hpos

/-- Nonzero vectors of the triangular lattice of covolume one have squared norm larger than
one. -/
theorem hexLattice_norm_sq_gt_one (x : hexLattice) (hx : (x : HexAmbient) ≠ 0) :
    1 < ‖(x : HexAmbient)‖^2 :=
  one_lt_two_div_sqrt_three.trans_le (hexLattice_norm_sq_ge x hx)

/-! ## Volume preservation and covolume one -/

theorem hexMap_eq_matrixTranspose (v : Fin 2 → ℝ) :
    hexMap v = Matrix.toLin' hexMatrix.transpose v := by
  rw [hexMap_eq_sum, Matrix.toLin'_apply]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row,
    Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hexMap_det : LinearMap.det hexMap.toLinearMap = 1 := by
  have h : hexMap.toLinearMap = Matrix.toLin' hexMatrix.transpose :=
    LinearMap.ext hexMap_eq_matrixTranspose
  rw [h, LinearMap.det_toLin', Matrix.det_transpose, hexMatrix_det]

theorem hexMap_map_volume :
    MeasureTheory.Measure.map hexMap (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → ℝ)) =
      MeasureTheory.volume := by
  have hdet : LinearMap.det hexMap.toLinearMap ≠ 0 := by rw [hexMap_det]; norm_num
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  simpa only [ContinuousLinearMap.coe_coe, hexMap_det, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul] using h

theorem hexMap_measurePreserving :
    MeasureTheory.MeasurePreserving hexMap (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → ℝ))
      MeasureTheory.volume :=
  ⟨hexMap.measurable, hexMap_map_volume⟩

theorem hexMap_measurableEmbedding :
    MeasurableEmbedding (hexMap : (Fin 2 → ℝ) → (Fin 2 → ℝ)) :=
  hexBasis.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

theorem hexEuclideanFundamentalDomain_volume :
    (MeasureTheory.volume : MeasureTheory.Measure HexAmbient).real
      (ZSpan.fundamentalDomain hexEuclideanBasis) = 1 := by
  have hp : (WithLp.ofLp : HexAmbient → (Fin 2 → ℝ)) ⁻¹'
      ZSpan.fundamentalDomain hexBasis = ZSpan.fundamentalDomain hexEuclideanBasis := by
    ext x
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hexEuclideanBasis,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    rfl
  have hm : (Matrix.of hexBasis : Matrix (Fin 2) (Fin 2) ℝ) = hexMatrix := by
    ext i j
    simp only [Matrix.of_apply, hexBasis_apply]
    rfl
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → ℝ)).real
      (ZSpan.fundamentalDomain hexBasis) = 1 := by
    rw [ZSpan.volume_real_fundamentalDomain, hm, hexMatrix_det, abs_one]
  have h := (PiLp.volume_preserving_ofLp (ι := Fin 2)).measureReal_preimage
    (ZSpan.fundamentalDomain_measurableSet (b := hexBasis)).nullMeasurableSet
  simpa only [hp, hv] using h

/-- The triangular lattice `hexLattice` has covolume one. -/
theorem hexLattice_covolume : ZLattice.covolume hexLattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain hexLattice MeasureTheory.volume
    (ZSpan.isAddFundamentalDomain hexEuclideanBasis MeasureTheory.volume)]
  exact hexEuclideanFundamentalDomain_volume

end SphericalRiesz
end
end

section

/-! # The dual of the triangular lattice is its quarter turn (stage S2-1)

The triangular lattice of covolume one is not self-dual. With the quarter turn
`J (x, y) = (-y, x)`, a linear isometry of the plane with `J ∘ J = -1`, the pairing of two lattice
points is `⟪p(j', k'), J p(j, k)⟫ = j k' - k j'`, an integer: the basis `p(1, 0)`, `p(0, 1)` is
paired with its own quarter turn by the unimodular matrix `[[0, -1], [1, 0]]`. Hence the dual
lattice (the `dualSubmodule` of the inner form, which is `SchwartzMap.dualLattice`) is exactly
`J` applied to the lattice, and `J` restricts to a norm preserving bijection from the lattice onto
its dual. Sums of functions of the norm over the dual lattice are sums over the lattice. This
replaces self-duality of the Leech lattice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SphericalRiesz

abbrev hexInnerForm : LinearMap.BilinForm ℝ HexAmbient := innerₗ HexAmbient

/-- `SchwartzMap.dualLattice` is the dual submodule of the Euclidean inner form. -/
theorem hexDualLattice_eq :
    SchwartzMap.dualLattice hexLattice = hexInnerForm.dualSubmodule hexLattice := rfl

theorem hexIntegerPoint_eq_sum (z : Fin 2 → ℤ) :
    hexIntegerPoint z = ∑ j, (z j : ℝ) • hexEuclideanBasis j := by
  rw [hexIntegerPoint, hexMap_eq_sum]
  simp only [hexEuclideanBasis_apply, ← WithLp.toLp_sum, ← WithLp.toLp_smul]

theorem hexInner_nondegenerate : hexInnerForm.Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

/-! ## The quarter turn -/

theorem hexVec_apply_zero (a c : ℝ) : (!₂[a, c] : HexAmbient) 0 = a := rfl

theorem hexVec_apply_one (a c : ℝ) : (!₂[a, c] : HexAmbient) 1 = c := rfl

/-- The quarter turn `(x, y) ↦ (-y, x)` as a linear equivalence of the plane. -/
def hexQuarterTurnLinear : HexAmbient ≃ₗ[ℝ] HexAmbient where
  toFun x := !₂[-x 1, x 0]
  invFun x := !₂[x 1, -x 0]
  map_add' x y := by
    apply hexAmbient_ext
    · show -(x 1 + y 1) = -x 1 + -y 1
      ring
    · rfl
  map_smul' c x := by
    apply hexAmbient_ext
    · show -(c * x 1) = c * -x 1
      ring
    · rfl
  left_inv x := by
    apply hexAmbient_ext
    · rfl
    · show -(-x 1) = x 1
      exact neg_neg _
  right_inv x := by
    apply hexAmbient_ext
    · show -(-x 0) = x 0
      exact neg_neg _
    · rfl

theorem hexQuarterTurnLinear_apply_zero (x : HexAmbient) :
    (hexQuarterTurnLinear x) 0 = -x 1 := rfl

theorem hexQuarterTurnLinear_apply_one (x : HexAmbient) :
    (hexQuarterTurnLinear x) 1 = x 0 := rfl

theorem hexQuarterTurnLinear_symm_apply_zero (x : HexAmbient) :
    (hexQuarterTurnLinear.symm x) 0 = x 1 := rfl

theorem hexQuarterTurnLinear_symm_apply_one (x : HexAmbient) :
    (hexQuarterTurnLinear.symm x) 1 = -x 0 := rfl

theorem hexQuarterTurnLinear_inner (x y : HexAmbient) :
    inner ℝ (hexQuarterTurnLinear x) (hexQuarterTurnLinear y) = inner ℝ x y := by
  rw [hexInner_eq, hexInner_eq, hexQuarterTurnLinear_apply_zero x,
    hexQuarterTurnLinear_apply_one x, hexQuarterTurnLinear_apply_zero y,
    hexQuarterTurnLinear_apply_one y]
  ring

/-- The quarter turn `J (x, y) = (-y, x)`, a linear isometry of the plane. -/
def hexQuarterTurn : HexAmbient ≃ₗᵢ[ℝ] HexAmbient :=
  hexQuarterTurnLinear.isometryOfInner hexQuarterTurnLinear_inner

theorem hexQuarterTurn_apply_zero (x : HexAmbient) : (hexQuarterTurn x) 0 = -x 1 :=
  hexQuarterTurnLinear_apply_zero x

theorem hexQuarterTurn_apply_one (x : HexAmbient) : (hexQuarterTurn x) 1 = x 0 :=
  hexQuarterTurnLinear_apply_one x

theorem hexQuarterTurn_symm_apply_zero (x : HexAmbient) : (hexQuarterTurn.symm x) 0 = x 1 :=
  hexQuarterTurnLinear_symm_apply_zero x

theorem hexQuarterTurn_symm_apply_one (x : HexAmbient) : (hexQuarterTurn.symm x) 1 = -x 0 :=
  hexQuarterTurnLinear_symm_apply_one x

theorem hexQuarterTurn_apply (x : HexAmbient) : hexQuarterTurn x = !₂[-x 1, x 0] :=
  hexAmbient_ext ((hexQuarterTurn_apply_zero x).trans (hexVec_apply_zero (-x 1) (x 0)).symm)
    ((hexQuarterTurn_apply_one x).trans (hexVec_apply_one (-x 1) (x 0)).symm)

/-- `J ∘ J = -1`. -/
theorem hexQuarterTurn_quarterTurn (x : HexAmbient) :
    hexQuarterTurn (hexQuarterTurn x) = -x := by
  apply hexAmbient_ext
  · rw [hexQuarterTurn_apply_zero, hexQuarterTurn_apply_one, PiLp.neg_apply]
  · rw [hexQuarterTurn_apply_one, hexQuarterTurn_apply_zero, PiLp.neg_apply]

theorem hexQuarterTurn_ne_zero {v : HexAmbient} (hv : v ≠ 0) : hexQuarterTurn v ≠ 0 :=
  fun h0 => hv (hexQuarterTurn.map_eq_zero_iff.mp h0)

/-- The pairing against a quarter turn is the determinant form. -/
theorem hexInner_quarterTurn (a v : HexAmbient) :
    inner ℝ a (hexQuarterTurn v) = v 0*a 1-v 1*a 0 := by
  rw [hexInner_eq, hexQuarterTurn_apply_zero, hexQuarterTurn_apply_one]
  ring

/-! ## The pairing of the lattice with its quarter turn -/

theorem hexTriangularPoint_inner (j k : ℤ) (w : HexAmbient) :
    inner ℝ (hexTriangularPoint j k) w =
      (Real.sqrt hexB)⁻¹*(((j : ℝ)+(k : ℝ)/2)*w 0+(k : ℝ)*hexB*w 1) := by
  rw [hexInner_eq, hexTriangularPoint_apply_zero, hexTriangularPoint_apply_one]
  ring

/-- `⟪p(j', k'), J p(j, k)⟫ = j k' - k j'`: the lattice is integrally paired with its quarter
turn, with Gram matrix `[[0, -1], [1, 0]]` on the basis. -/
theorem hexTriangularPoint_inner_quarterTurn (j' k' j k : ℤ) :
    inner ℝ (hexTriangularPoint j' k') (hexQuarterTurn (hexTriangularPoint j k)) =
      ((j*k'-k*j' : ℤ) : ℝ) := by
  rw [hexInner_quarterTurn, hexTriangularPoint_apply_zero j k, hexTriangularPoint_apply_one j k,
    hexTriangularPoint_apply_zero j' k', hexTriangularPoint_apply_one j' k']
  push_cast
  linear_combination ((j : ℝ)*(k' : ℝ)-(k : ℝ)*(j' : ℝ))*hexScale_mul_self_mul

/-! ## The dual lattice -/

/-- Membership in the dual lattice: integer pairing with every lattice vector. -/
theorem hexDual_mem_iff_inner (w : HexAmbient) :
    w ∈ SchwartzMap.dualLattice hexLattice ↔
      ∀ a ∈ hexLattice, ∃ n : ℤ, inner ℝ a w = (n : ℝ) := by
  constructor
  · intro hw a ha
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hw a ha)
    exact ⟨n, (real_inner_comm w a).trans (hn.symm.trans (eq_intCast (algebraMap ℤ ℝ) n))⟩
  · intro h a ha
    obtain ⟨n, hn⟩ := h a ha
    exact Submodule.mem_one.mpr
      ⟨n, (eq_intCast (algebraMap ℤ ℝ) n).trans (hn.symm.trans (real_inner_comm w a))⟩

/-- The dual lattice is the quarter turn of the lattice. -/
theorem hexDual_mem_iff (w : HexAmbient) :
    w ∈ SchwartzMap.dualLattice hexLattice ↔ ∃ v ∈ hexLattice, hexQuarterTurn v = w := by
  rw [hexDual_mem_iff_inner]
  constructor
  · intro hw
    obtain ⟨n0, e0⟩ := hw (hexTriangularPoint 1 0) (hexTriangularPoint_mem 1 0)
    obtain ⟨n1, e1⟩ := hw (hexTriangularPoint 0 1) (hexTriangularPoint_mem 0 1)
    rw [hexTriangularPoint_inner] at e0 e1
    push_cast at e0 e1
    refine ⟨hexTriangularPoint n1 (-n0), hexTriangularPoint_mem n1 (-n0), ?_⟩
    apply hexAmbient_ext
    · rw [hexQuarterTurn_apply_zero, hexTriangularPoint_apply_one]
      push_cast
      linear_combination (-((Real.sqrt hexB)⁻¹*hexB))*e0+(w 0)*hexScale_mul_self_mul
    · rw [hexQuarterTurn_apply_one, hexTriangularPoint_apply_zero]
      push_cast
      linear_combination (-(Real.sqrt hexB)⁻¹)*e1+((Real.sqrt hexB)⁻¹/2)*e0+
        (w 1)*hexScale_mul_self_mul
  · rintro ⟨v, hv, rfl⟩ a ha
    obtain ⟨j, k, rfl⟩ := (hexLattice_mem_iff_triangular v).mp hv
    obtain ⟨j', k', rfl⟩ := (hexLattice_mem_iff_triangular a).mp ha
    exact ⟨j*k'-k*j', hexTriangularPoint_inner_quarterTurn j' k' j k⟩

theorem hexQuarterTurn_mem_dual {v : HexAmbient} (hv : v ∈ hexLattice) :
    hexQuarterTurn v ∈ SchwartzMap.dualLattice hexLattice :=
  (hexDual_mem_iff _).mpr ⟨v, hv, rfl⟩

theorem hexQuarterTurn_symm_mem {w : HexAmbient}
    (hw : w ∈ SchwartzMap.dualLattice hexLattice) : hexQuarterTurn.symm w ∈ hexLattice := by
  obtain ⟨v, hv, rfl⟩ := (hexDual_mem_iff w).mp hw
  rw [hexQuarterTurn.symm_apply_apply]
  exact hv

/-- The dual lattice is the image of the lattice under the quarter turn (this replaces
`leechLattice_selfDual`). -/
theorem hexLattice_dual :
    hexInnerForm.dualSubmodule hexLattice =
      Submodule.map (hexQuarterTurn.toLinearEquiv.toLinearMap.restrictScalars ℤ) hexLattice := by
  ext w
  rw [← hexDualLattice_eq, hexDual_mem_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    exact ⟨v, hv, rfl⟩

theorem hexLattice_dual_coe :
    (SchwartzMap.dualLattice hexLattice : Set HexAmbient) =
      hexQuarterTurn '' (hexLattice : Set HexAmbient) := by
  ext w
  rw [SetLike.mem_coe, hexDual_mem_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- The quarter turn as a bijection from the lattice onto its dual. -/
def hexDualEquiv : hexLattice ≃ SchwartzMap.dualLattice hexLattice where
  toFun x := ⟨hexQuarterTurn (x : HexAmbient), hexQuarterTurn_mem_dual x.property⟩
  invFun w := ⟨hexQuarterTurn.symm (w : HexAmbient), hexQuarterTurn_symm_mem w.property⟩
  left_inv x := Subtype.ext (hexQuarterTurn.symm_apply_apply (x : HexAmbient))
  right_inv w := Subtype.ext (hexQuarterTurn.apply_symm_apply (w : HexAmbient))

theorem hexDualEquiv_coe (x : hexLattice) :
    ((hexDualEquiv x : SchwartzMap.dualLattice hexLattice) : HexAmbient) =
      hexQuarterTurn (x : HexAmbient) := rfl

/-- The bijection of the lattice onto its dual preserves norms. -/
theorem hexDualEquiv_norm (x : hexLattice) :
    ‖((hexDualEquiv x : SchwartzMap.dualLattice hexLattice) : HexAmbient)‖ =
      ‖(x : HexAmbient)‖ := by
  rw [hexDualEquiv_coe, hexQuarterTurn.norm_map]

/-- A sum of a function of the norm over the dual lattice is the same sum over the lattice. -/
theorem hexDual_tsum_norm {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (F : ℝ → α) :
    (∑' m : SchwartzMap.dualLattice hexLattice, F ‖(m : HexAmbient)‖) =
      ∑' x : hexLattice, F ‖(x : HexAmbient)‖ := by
  rw [← hexDualEquiv.tsum_eq]
  exact tsum_congr fun x => by rw [hexDualEquiv_norm]

/-- The nonzero vectors of the dual lattice have squared norm at least `2/√3` as well. -/
theorem hexDual_norm_sq_ge {w : HexAmbient} (hw : w ∈ SchwartzMap.dualLattice hexLattice)
    (hw0 : w ≠ 0) : 2/Real.sqrt 3 ≤ ‖w‖^2 := by
  obtain ⟨v, hv, rfl⟩ := (hexDual_mem_iff w).mp hw
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hw0 (map_zero hexQuarterTurn)
  rw [hexQuarterTurn.norm_map]
  exact hexLattice_norm_sq_ge ⟨v, hv⟩ hv0

end SphericalRiesz
end
end

section

/-! # The theta function of the triangular lattice and its `S`-transformation (stage S2-1)

`Θ(τ) = Σ_{x ∈ Λ} exp(π i |x|² τ)` over the triangular lattice `Λ` of covolume one converges for
`Im τ > 0` (the lattice sum of `|x|^(-4)` converges). By Poisson summation on the lattice of
covolume one, the Gaussian Fourier transform in dimension `2` (weight `d/2 = 1`, so the factor is
`τ/i` and not a power of `τ`) and the quarter turn, which maps the lattice onto its dual and
preserves norms, `Θ(-1/τ) = (τ/i) Θ(τ)`. The lattice is not even, so there is no relation
`Θ(τ + 1) = Θ(τ)`. The radial Schwartz profile of the `E8` development is reused: it is a function
of one real variable and does not depend on the dimension. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology FourierTransform RealInnerProductSpace SchwartzMap
namespace SphericalRiesz

theorem hexLattice_summable_norm_rpow :
    Summable (fun x : hexLattice => ‖x‖ ^ (-4 : ℝ)) :=
  ZLattice.summable_norm_rpow hexLattice (-4) (by rw [hexLattice_rank]; norm_num)

def hexLatticeThetaTerm (τ : ℂ) (x : hexLattice) : ℂ :=
  Complex.exp ((Real.pi : ℂ)*Complex.I*(‖(x : HexAmbient)‖^2 : ℝ)*τ)

theorem hexLatticeThetaTerm_norm (τ : ℂ) (x : hexLattice) :
    ‖hexLatticeThetaTerm τ x‖ = Real.exp (-Real.pi*‖(x : HexAmbient)‖^2*τ.im) := by
  unfold hexLatticeThetaTerm
  rw [Complex.norm_exp]
  congr 1
  have he : (Real.pi : ℂ)*Complex.I*(‖(x : HexAmbient)‖^2 : ℝ)*τ =
      ((Real.pi*‖(x : HexAmbient)‖^2 : ℝ) : ℂ)*(τ*Complex.I) := by
    push_cast
    ring
  rw [he, Complex.re_ofReal_mul, Complex.mul_I_re]
  ring

theorem hexLatticeThetaTerm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (hexLatticeThetaTerm τ) := by
  have hdecay : (fun t : ℝ => Real.exp (-Real.pi*τ.im*t^2)) =o[atTop]
      (fun t : ℝ => t^(-4 : ℝ)) := by
    have ha : -Real.pi*τ.im < 0 := by nlinarith [Real.pi_pos]
    simpa only [zero_mul, add_zero] using
      rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 (-4)
  obtain ⟨C, hC, hbound⟩ := hdecay.isBigO.exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound.bound
  have hfinite := hexLattice_finite_norm_lt R
  have hevent : ∀ᶠ x : hexLattice in cofinite,
      ‖hexLatticeThetaTerm τ x‖ ≤ C*‖x‖^(-4 : ℝ) := by
    apply eventually_cofinite.mpr
    apply hfinite.subset
    intro x hx
    by_contra hsmall
    have hlarge : R ≤ ‖(x : HexAmbient)‖ := le_of_not_gt hsmall
    have h := hR ‖(x : HexAmbient)‖ hlarge
    have hb : Real.exp (-Real.pi*τ.im*‖(x : HexAmbient)‖^2) ≤
        C*‖(x : HexAmbient)‖^(-4 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using h
    apply hx
    simpa only [hexLatticeThetaTerm_norm, Submodule.norm_coe,
      mul_assoc, mul_left_comm, mul_comm] using hb
  apply Summable.of_norm_bounded_eventually (hexLattice_summable_norm_rpow.mul_left C)
  filter_upwards [hevent] with x hx
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos hC,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx

/-- The theta function of the triangular lattice of covolume one. -/
def hexTheta (τ : ℂ) : ℂ := ∑' x : hexLattice, hexLatticeThetaTerm τ x

/-- The squared norms of the lattice lie in `(2/√3) ℕ`, so the theta function has period `√3`
(this replaces `Θ(τ + 1) = Θ(τ)` of an even lattice). -/
theorem hexTheta_add_sqrt_three (τ : ℂ) :
    hexTheta (τ+((Real.sqrt 3 : ℝ) : ℂ)) = hexTheta τ := by
  unfold hexTheta
  refine tsum_congr fun x => ?_
  obtain ⟨n, hn⟩ := hexLattice_norm_sq_eq x
  unfold hexLatticeThetaTerm
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨n, ?_⟩
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹*((Real.sqrt 3 : ℝ) : ℂ) = 1 :=
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne')
  rw [hn]
  push_cast
  linear_combination (2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*h3

def hexThetaKernel (τ : ℂ) (x : HexAmbient) : ℂ :=
  Complex.exp ((Real.pi : ℂ)*Complex.I*(‖x‖^2 : ℝ)*τ)

theorem hexThetaKernel_lattice (τ : ℂ) (x : hexLattice) :
    hexThetaKernel τ x = hexLatticeThetaTerm τ x := rfl

theorem hexThetaKernel_gaussian (τ : ℂ) : hexThetaKernel τ =
    fun x : HexAmbient => Complex.exp
      (-((Real.pi : ℂ)*(-Complex.I*τ))*(‖x‖ : ℂ)^2) := by
  funext x
  unfold hexThetaKernel
  congr 1
  push_cast
  ring

/-- The theta kernel is invariant under the quarter turn. -/
theorem hexThetaKernel_quarterTurn (τ : ℂ) (x : HexAmbient) :
    hexThetaKernel τ (hexQuarterTurn x) = hexThetaKernel τ x := by
  unfold hexThetaKernel
  rw [hexQuarterTurn.norm_map]

/-- The sum of the theta kernel over the dual lattice is its sum over the lattice. -/
theorem hexThetaKernel_dual_tsum (τ : ℂ) :
    (∑' m : SchwartzMap.dualLattice hexLattice, hexThetaKernel τ (m : HexAmbient)) =
      ∑' x : hexLattice, hexThetaKernel τ (x : HexAmbient) := by
  unfold hexThetaKernel
  exact hexDual_tsum_norm
    (fun r : ℝ => Complex.exp ((Real.pi : ℂ)*Complex.I*((r^2 : ℝ) : ℂ)*τ))

/-- The Fourier transform of the theta kernel in dimension two: weight one, factor `τ/i`. -/
theorem hexThetaKernel_fourier_S {τ : ℂ} (hτ : 0 < τ.im) (w : HexAmbient) :
    𝓕 (hexThetaKernel (-1/τ)) w = τ/Complex.I * hexThetaKernel τ w := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simp [h] at hτ
  have hS : 0 < (-1/τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  let b : ℂ := (Real.pi : ℂ)*(-Complex.I*(-1/τ))
  have hb : 0 < b.re := by
    simpa [b] using mul_pos Real.pi_pos hS
  have hπ : (Real.pi : ℂ)/b = τ/Complex.I := by
    dsimp [b]
    field_simp [hτ0, Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : ((Real.pi : ℂ)/b)^((Module.finrank ℝ HexAmbient : ℂ)/2) = τ/Complex.I := by
    rw [hπ, finrank_euclideanSpace_fin]
    have h1 : ((2:ℕ):ℂ)/2 = 1 := by norm_num
    rw [h1, Complex.cpow_one]
  have he : -(Real.pi : ℂ)^2*(‖w‖ : ℂ)^2/b =
      (Real.pi : ℂ)*Complex.I*(‖w‖^2 : ℝ)*τ := by
    dsimp [b]
    push_cast
    field_simp [hτ0, Real.pi_ne_zero, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  rw [hexThetaKernel_gaussian]
  change 𝓕 (fun x : HexAmbient => Complex.exp (-b*(‖x‖ : ℂ)^2)) w = _
  rw [fourier_gaussian_innerProductSpace hb w, hc, he]
  rfl

noncomputable def hexThetaSchwartzKernel (τ : ℂ) (hτ : 0 < τ.im) : 𝓢(HexAmbient, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_contDiff_decay_nonneg (F := HexAmbient)
    (e8ThetaProfile τ) (e8ThetaProfile_contDiff τ) (e8ThetaProfile_decay (τ := τ) hτ)

theorem hexThetaSchwartzKernel_apply (τ : ℂ) (hτ : 0 < τ.im) (x : HexAmbient) :
    hexThetaSchwartzKernel τ hτ x =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
  simp [hexThetaSchwartzKernel, e8ThetaProfile, mul_assoc, mul_comm]

theorem hexThetaSchwartzKernel_eq (τ : ℂ) (hτ : 0 < τ.im) :
    (fun x : HexAmbient => hexThetaSchwartzKernel τ hτ x) = hexThetaKernel τ := by
  funext x
  rw [hexThetaSchwartzKernel_apply]
  unfold hexThetaKernel
  congr 1
  ring

/-- The `S`-transformation of the theta function of the triangular lattice (weight `1`):
`Θ(-1/τ) = (τ/i) Θ(τ)`. -/
theorem hexTheta_transform_S {τ : ℂ} (hτ : 0 < τ.im) :
    hexTheta (-1/τ) = τ/Complex.I * hexTheta τ := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simp [h] at hτ
  have hS : 0 < (-1/τ).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ0)
  let f := hexThetaSchwartzKernel (-1/τ) hS
  have hp := SchwartzMap.poissonSummation_lattice (L := hexLattice) f 0
  have hf : (fun x : HexAmbient => f x) = hexThetaKernel (-1/τ) :=
    hexThetaSchwartzKernel_eq (-1/τ) hS
  have hp' : (∑' x : hexLattice, hexThetaKernel (-1/τ) x) =
      ∑' m : SchwartzMap.dualLattice hexLattice, 𝓕 (hexThetaKernel (-1/τ)) m := by
    simpa [hexLattice_covolume, hf] using hp
  unfold hexTheta
  change (∑' x : hexLattice, hexThetaKernel (-1/τ) x) =
    τ/Complex.I * ∑' x : hexLattice, hexThetaKernel τ x
  rw [hp']
  calc (∑' m : SchwartzMap.dualLattice hexLattice, 𝓕 (hexThetaKernel (-1/τ)) (m : HexAmbient))
      = ∑' m : SchwartzMap.dualLattice hexLattice,
          τ/Complex.I * hexThetaKernel τ (m : HexAmbient) :=
        tsum_congr fun m => hexThetaKernel_fourier_S hτ (m : HexAmbient)
    _ = τ/Complex.I * ∑' m : SchwartzMap.dualLattice hexLattice,
          hexThetaKernel τ (m : HexAmbient) := tsum_mul_left
    _ = τ/Complex.I * ∑' x : hexLattice, hexThetaKernel τ (x : HexAmbient) := by
        rw [hexThetaKernel_dual_tsum]

/-- The same transformation with the factor written as `-i τ`. -/
theorem hexTheta_transform_S' {τ : ℂ} (hτ : 0 < τ.im) :
    hexTheta (-1/τ) = -Complex.I*τ * hexTheta τ := by
  rw [hexTheta_transform_S hτ]
  congr 1
  rw [div_eq_iff Complex.I_ne_zero]
  linear_combination τ*Complex.I_mul_I

end SphericalRiesz
end
end

section

/-! # Sharp Gaussian certificates for the triangular lattice (stage S2-0)

`HexGaussianContactCertificate2 β f` is the shape of the sharp Gaussian minorants of the
triangular lattice of covolume one in the plane: a real Schwartz function below
`exp(-π β ‖x‖²)`, with real nonnegative Fourier transform, touching the Gaussian at every nonzero
lattice vector and with Fourier transform vanishing at every nonzero vector of the DUAL lattice
(the lattice is not self-dual; its dual is its quarter turn). Proved here, with no deep input:
* Poisson summation over the covolume-one lattice turns one certificate into the value identity
  `Re 𝓕f(0) - Re f(0) = Θ(β) - 1`, `Θ(β) = Σ_{v ∈ Λ} exp(-π β |v|²)`; the Fourier side is a sum
  over the dual lattice, which is where the zeros are;
* the reciprocal map `f ↦ g_β - β⁻¹ (𝓕f ∘ J)` (`𝓕 g_β = β⁻¹ g_{β⁻¹}` in dimension `2`, `J` the
  quarter turn, `J ∘ J = -1`) turns a certificate at `β⁻¹` into one at `β`, so certificates on
  one side of `β = 1` give all `β > 0`.
The existence of certificates is an external input (stage S2-6). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace SphericalRiesz

/-- The real Gaussian theta sum `Σ_{v ∈ Λ} exp(-π β |v|²)` of the triangular lattice. -/
def hexGaussianThetaReal2 (β : ℝ) : ℝ :=
  ∑' x : hexLattice, Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2))

/-- The real Gaussian sum over the lattice has sum `Θ(β)`. -/
theorem hexLatticeGaussian_hasSum {β : ℝ} (hβ : 0 < β) :
    HasSum (fun x : hexLattice => ((Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ))
      (hexGaussianThetaReal2 β : ℂ) := by
  have hτ : 0 < ((β:ℂ)*Complex.I).im := by simpa using hβ
  have hs := hexLatticeThetaTerm_summable hτ
  have hterm : ∀ x : hexLattice, hexLatticeThetaTerm ((β:ℂ)*Complex.I) x =
      ((Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ) := by
    intro x
    unfold hexLatticeThetaTerm
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : hexLatticeThetaTerm ((β:ℂ)*Complex.I) = fun x : hexLattice =>
      ((Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ) := funext hterm
  have hs' : Summable (fun x : hexLattice =>
      ((Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ)) := by
    rw [← hfun]; exact hs
  have hr : Summable (fun x : hexLattice => Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2))) :=
    Complex.summable_ofReal.mp hs'
  rw [Complex.hasSum_ofReal]
  exact hr.hasSum

theorem hexGaussianThetaReal2_ge_one {β : ℝ} (hβ : 0 < β) : 1 ≤ hexGaussianThetaReal2 β := by
  have hs := (Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hβ)).summable
  have h0 : Real.exp (-(Real.pi*β*‖((0 : hexLattice) : HexAmbient)‖^2)) = 1 := by simp
  calc (1:ℝ) = Real.exp (-(Real.pi*β*‖((0 : hexLattice) : HexAmbient)‖^2)) := h0.symm
    _ ≤ hexGaussianThetaReal2 β :=
      hs.le_tsum (0 : hexLattice) (fun x _ => (Real.exp_pos _).le)

/-- The sharp Gaussian certificate for the triangular lattice at parameter `β`: contact on the
lattice, zeros of the Fourier transform on the dual lattice. -/
structure HexGaussianContactCertificate2 (β : ℝ) (f : 𝓢(HexAmbient, ℂ)) : Prop where
  real : ∀ x, (f x).im = 0
  fourier_real : ∀ ξ, ((𝓕 f) ξ).im = 0
  fourier_nonneg : ∀ ξ, 0 ≤ ((𝓕 f) ξ).re
  minorant : ∀ x, (f x).re ≤ Real.exp (-(Real.pi*β*‖x‖^2))
  contact : ∀ v ∈ hexLattice, v ≠ 0 → (f v).re = Real.exp (-(Real.pi*β*‖v‖^2))
  fourier_zero : ∀ w ∈ SchwartzMap.dualLattice hexLattice, w ≠ 0 → (𝓕 f) w = 0

theorem HexGaussianContactCertificate2.apply_eq {β : ℝ} {f : 𝓢(HexAmbient, ℂ)}
    (h : HexGaussianContactCertificate2 β f) {v : HexAmbient} (hv : v ∈ hexLattice)
    (hv0 : v ≠ 0) : f v = (Real.exp (-(Real.pi*β*‖v‖^2)) : ℂ) := by
  apply Complex.ext
  · rw [h.contact v hv hv0, Complex.ofReal_re]
  · rw [h.real v, Complex.ofReal_im]

/-- The zeros of the Fourier transform, stated on the quarter turn of the lattice. -/
theorem HexGaussianContactCertificate2.fourier_zero_quarterTurn {β : ℝ}
    {f : 𝓢(HexAmbient, ℂ)} (h : HexGaussianContactCertificate2 β f) {v : HexAmbient}
    (hv : v ∈ hexLattice) (hv0 : v ≠ 0) : (𝓕 f) (hexQuarterTurn v) = 0 :=
  h.fourier_zero (hexQuarterTurn v) (hexQuarterTurn_mem_dual hv) (hexQuarterTurn_ne_zero hv0)

/-- Poisson summation: the contact and Fourier-zero conditions force the sharp value. -/
theorem HexGaussianContactCertificate2.value {β : ℝ} (hβ : 0 < β) {f : 𝓢(HexAmbient, ℂ)}
    (h : HexGaussianContactCertificate2 β f) :
    ((𝓕 f) 0).re-(f 0).re = hexGaussianThetaReal2 β-1 := by
  classical
  have hp := SchwartzMap.poissonSummation_lattice (L := hexLattice) f 0
  have hp' : (∑' x : hexLattice, f x) =
      ∑' m : SchwartzMap.dualLattice hexLattice, 𝓕 (fun x : HexAmbient => f x) m := by
    simpa [hexLattice_covolume] using hp
  have hrhs : (∑' m : SchwartzMap.dualLattice hexLattice,
      𝓕 (fun x : HexAmbient => f x) m) = (𝓕 f) 0 := by
    rw [tsum_eq_single (0 : SchwartzMap.dualLattice hexLattice)]
    · rfl
    · intro m hm
      have hm0 : (m : HexAmbient) ≠ 0 := by
        intro h0
        exact hm (Subtype.ext h0)
      exact h.fourier_zero m m.property hm0
  let ψ : hexLattice → ℂ := fun x => ((Real.exp (-(Real.pi*β*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ)
  have hψ : HasSum ψ (hexGaussianThetaReal2 β : ℂ) := hexLatticeGaussian_hasSum hβ
  have hupd := hψ.update (0 : hexLattice) (f 0)
  have hfun : Function.update ψ (0 : hexLattice) (f 0) = fun x : hexLattice => f x := by
    funext x
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [Function.update_of_ne hx]
      have hx0 : (x : HexAmbient) ≠ 0 := by
        intro h0
        exact hx (Subtype.ext h0)
      exact (h.apply_eq x.property hx0).symm
  rw [hfun] at hupd
  have hψ0 : ψ 0 = 1 := by simp [ψ]
  rw [hupd.tsum_eq, hrhs, hψ0] at hp'
  have hre := congrArg Complex.re hp'
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
  linarith

/-- A real Schwartz map on the plane as a complex Schwartz map. -/
def hexSchwartzOfReal (g : 𝓢(HexAmbient, ℝ)) : 𝓢(HexAmbient, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM g

theorem hexSchwartzOfReal_apply (g : 𝓢(HexAmbient, ℝ)) (x : HexAmbient) :
    hexSchwartzOfReal g x = ((g x : ℝ) : ℂ) := rfl

/-- The Fourier transform of the complexified map is the Fourier transform of the complex valued
function `x ↦ (g x : ℂ)`. -/
theorem hexSchwartzOfReal_fourier (g : 𝓢(HexAmbient, ℝ)) (ξ : HexAmbient) :
    (𝓕 (hexSchwartzOfReal g)) ξ = 𝓕 (fun x : HexAmbient => ((g x : ℝ) : ℂ)) ξ := by
  have hfun : (fun x : HexAmbient => hexSchwartzOfReal g x) =
      fun x : HexAmbient => ((g x : ℝ) : ℂ) := funext fun x => hexSchwartzOfReal_apply g x
  change 𝓕 (fun x : HexAmbient => hexSchwartzOfReal g x) ξ = _
  rw [hfun]

/-- The shape of the external sharp Gaussian minorants: a REAL Schwartz function below the
Gaussian, whose complex Fourier transform is real and nonnegative, with contact at the nonzero
lattice vectors and Fourier zeros at the nonzero vectors that pair integrally with the lattice,
gives a certificate. -/
theorem HexGaussianContactCertificate2.of_real {β : ℝ} (g : 𝓢(HexAmbient, ℝ))
    (hminor : ∀ x, g x ≤ Real.exp (-(Real.pi*β*‖x‖^2)))
    (hfourier : ∀ w : HexAmbient, (𝓕 (fun x : HexAmbient => ((g x : ℝ) : ℂ)) w).im = 0 ∧
      0 ≤ (𝓕 (fun x : HexAmbient => ((g x : ℝ) : ℂ)) w).re)
    (hcontact : ∀ a ∈ hexLattice, a ≠ 0 → g a = Real.exp (-(Real.pi*β*‖a‖^2)))
    (hzero : ∀ w : HexAmbient, (∀ a ∈ hexLattice, ∃ n : ℤ, inner ℝ a w = (n : ℝ)) → w ≠ 0 →
      𝓕 (fun x : HexAmbient => ((g x : ℝ) : ℂ)) w = 0) :
    HexGaussianContactCertificate2 β (hexSchwartzOfReal g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hexSchwartzOfReal_apply, Complex.ofReal_im]
  · intro ξ
    rw [hexSchwartzOfReal_fourier]
    exact (hfourier ξ).1
  · intro ξ
    rw [hexSchwartzOfReal_fourier]
    exact (hfourier ξ).2
  · intro x
    rw [hexSchwartzOfReal_apply, Complex.ofReal_re]
    exact hminor x
  · intro v hv hv0
    rw [hexSchwartzOfReal_apply, Complex.ofReal_re]
    exact hcontact v hv hv0
  · intro w hw hw0
    rw [hexSchwartzOfReal_fourier]
    exact hzero w ((hexDual_mem_iff_inner w).mp hw) hw0

/-- The Gaussian `exp(-π β ‖x‖²)` on `ℝ²` as an actual Schwartz map. -/
def hexGaussianSchwartz2 (β : ℝ) (hβ : 0 < β) : 𝓢(HexAmbient, ℂ) :=
  hexThetaSchwartzKernel ((β : ℂ)*Complex.I) (by simpa using hβ)

theorem hexGaussianSchwartz2_apply {β : ℝ} (hβ : 0 < β) (x : HexAmbient) :
    hexGaussianSchwartz2 β hβ x = (Real.exp (-(Real.pi*β*‖x‖^2)) : ℂ) := by
  rw [hexGaussianSchwartz2, hexThetaSchwartzKernel_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `𝓕 g_β = β⁻¹ g_{β⁻¹}` in dimension two. -/
theorem hexGaussianSchwartz2_fourier {β : ℝ} (hβ : 0 < β) (ξ : HexAmbient) :
    (𝓕 (hexGaussianSchwartz2 β hβ)) ξ =
      ((β⁻¹ : ℝ) : ℂ) * (Real.exp (-(Real.pi*β⁻¹*‖ξ‖^2)) : ℂ) := by
  have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  set τ : ℂ := Complex.I*((β⁻¹ : ℝ) : ℂ) with hτdef
  have hτ : 0 < τ.im := by simpa [hτdef] using inv_pos.mpr hβ
  have hS : -1/τ = (β : ℂ)*Complex.I := by
    rw [hτdef]
    push_cast
    field_simp
    rw [Complex.I_sq]
  have hf : (fun x : HexAmbient => hexGaussianSchwartz2 β hβ x) = hexThetaKernel (-1/τ) := by
    rw [hS]
    exact hexThetaSchwartzKernel_eq _ _
  change 𝓕 (fun x : HexAmbient => hexGaussianSchwartz2 β hβ x) ξ = _
  rw [hf, hexThetaKernel_fourier_S hτ ξ]
  unfold hexThetaKernel
  rw [Complex.ofReal_exp]
  have hpow : τ/Complex.I = ((β⁻¹ : ℝ) : ℂ) := by
    rw [hτdef, mul_div_cancel_left₀ _ Complex.I_ne_zero]
  rw [hpow]
  congr 2
  rw [hτdef]
  push_cast
  have hI : Complex.I*Complex.I = -1 := by rw [← sq, Complex.I_sq]
  linear_combination ((Real.pi : ℂ)*((‖ξ‖ : ℂ))^2*(β : ℂ)⁻¹)*hI

/-- `𝓕 (𝓕 f) ξ = f (-ξ)` for Schwartz maps on `ℝ²`. -/
theorem hexSchwartz_fourier_fourier (f : 𝓢(HexAmbient, ℂ)) (ξ : HexAmbient) :
    (𝓕 (𝓕 f)) ξ = f (-ξ) := by
  have h0 : 𝓕⁻ (𝓕 f : 𝓢(HexAmbient, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h : (𝓕⁻ (𝓕 f : 𝓢(HexAmbient, ℂ))) (-ξ) = f (-ξ) := by rw [h0]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg]
  rfl

/-- Composition of a Schwartz map with the quarter turn. -/
def hexSchwartzQuarterTurn (g : 𝓢(HexAmbient, ℂ)) : 𝓢(HexAmbient, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ hexQuarterTurn.toContinuousLinearEquiv g

theorem hexSchwartzQuarterTurn_apply (g : 𝓢(HexAmbient, ℂ)) (x : HexAmbient) :
    hexSchwartzQuarterTurn g x = g (hexQuarterTurn x) := rfl

/-- The Fourier transform commutes with the quarter turn. -/
theorem hexSchwartzQuarterTurn_fourier (g : 𝓢(HexAmbient, ℂ)) (ξ : HexAmbient) :
    (𝓕 (hexSchwartzQuarterTurn g)) ξ = (𝓕 g) (hexQuarterTurn ξ) := by
  change 𝓕 ((fun x : HexAmbient => g x) ∘ hexQuarterTurn) ξ =
    𝓕 (fun x : HexAmbient => g x) (hexQuarterTurn ξ)
  exact Real.fourier_comp_linearIsometry hexQuarterTurn (fun x : HexAmbient => g x) ξ

/-- The reciprocal certificate `g_β - β⁻¹ (𝓕 f ∘ J)`. -/
def hexReciprocalCertificate2 (β : ℝ) (hβ : 0 < β) (f : 𝓢(HexAmbient, ℂ)) :
    𝓢(HexAmbient, ℂ) :=
  hexGaussianSchwartz2 β hβ - ((β⁻¹ : ℝ) : ℂ) • hexSchwartzQuarterTurn (𝓕 f)

theorem hexReciprocalCertificate2_apply {β : ℝ} (hβ : 0 < β) (f : 𝓢(HexAmbient, ℂ))
    (x : HexAmbient) :
    hexReciprocalCertificate2 β hβ f x =
      (Real.exp (-(Real.pi*β*‖x‖^2)) : ℂ) - ((β⁻¹ : ℝ) : ℂ) * (𝓕 f) (hexQuarterTurn x) := by
  rw [hexReciprocalCertificate2, sub_apply, smul_apply,
    hexGaussianSchwartz2_apply, smul_eq_mul, hexSchwartzQuarterTurn_apply]

theorem hexReciprocalCertificate2_fourier {β : ℝ} (hβ : 0 < β) (f : 𝓢(HexAmbient, ℂ))
    (ξ : HexAmbient) :
    (𝓕 (hexReciprocalCertificate2 β hβ f)) ξ =
      ((β⁻¹ : ℝ) : ℂ) * ((Real.exp (-(Real.pi*β⁻¹*‖ξ‖^2)) : ℂ) - f (-(hexQuarterTurn ξ))) := by
  have hlin : 𝓕 (hexReciprocalCertificate2 β hβ f) =
      𝓕 (hexGaussianSchwartz2 β hβ) - ((β⁻¹ : ℝ) : ℂ) • 𝓕 (hexSchwartzQuarterTurn (𝓕 f)) := by
    change SchwartzMap.fourierTransformCLM ℂ
        (hexGaussianSchwartz2 β hβ - ((β⁻¹ : ℝ) : ℂ) • hexSchwartzQuarterTurn (𝓕 f)) =
      SchwartzMap.fourierTransformCLM ℂ (hexGaussianSchwartz2 β hβ) -
        ((β⁻¹ : ℝ) : ℂ) • SchwartzMap.fourierTransformCLM ℂ (hexSchwartzQuarterTurn (𝓕 f))
    rw [map_sub, map_smul]
  rw [hlin, sub_apply, smul_apply, hexGaussianSchwartz2_fourier,
    hexSchwartzQuarterTurn_fourier, hexSchwartz_fourier_fourier, smul_eq_mul]
  ring

/-- A certificate at `β⁻¹` gives one at `β`. -/
theorem HexGaussianContactCertificate2.reciprocal {β : ℝ} (hβ : 0 < β)
    {f : 𝓢(HexAmbient, ℂ)} (h : HexGaussianContactCertificate2 β⁻¹ f) :
    HexGaussianContactCertificate2 β (hexReciprocalCertificate2 β hβ f) := by
  have hc : 0 < β⁻¹ := inv_pos.mpr hβ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hexReciprocalCertificate2_apply, (e8_real_sub_mul_parts _ _ _).2,
      h.fourier_real (hexQuarterTurn x), mul_zero, neg_zero]
  · intro ξ
    rw [hexReciprocalCertificate2_fourier, (e8_real_mul_sub_parts _ _ _).2,
      h.real (-(hexQuarterTurn ξ)), mul_zero, neg_zero]
  · intro ξ
    rw [hexReciprocalCertificate2_fourier, (e8_real_mul_sub_parts _ _ _).1]
    have hm := h.minorant (-(hexQuarterTurn ξ))
    rw [norm_neg, hexQuarterTurn.norm_map] at hm
    exact mul_nonneg hc.le (by linarith)
  · intro x
    rw [hexReciprocalCertificate2_apply, (e8_real_sub_mul_parts _ _ _).1]
    have := mul_nonneg hc.le (h.fourier_nonneg (hexQuarterTurn x))
    linarith
  · intro v hv hv0
    rw [hexReciprocalCertificate2_apply, h.fourier_zero_quarterTurn hv hv0, mul_zero, sub_zero,
      Complex.ofReal_re]
  · intro w hw hw0
    obtain ⟨v, hv, rfl⟩ := (hexDual_mem_iff w).mp hw
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hw0 (map_zero hexQuarterTurn)
    have hJJ : -(hexQuarterTurn (hexQuarterTurn v)) = v := by
      rw [hexQuarterTurn_quarterTurn, neg_neg]
    rw [hexReciprocalCertificate2_fourier, hJJ, h.apply_eq hv hv0, hexQuarterTurn.norm_map,
      sub_self, mul_zero]

/-- Certificates on `β ≥ 1` give certificates for every `β > 0`. -/
theorem hexGaussianContact_all_of_ge_one
    (h : ∀ β : ℝ, 1 ≤ β → ∃ f, HexGaussianContactCertificate2 β f) :
    ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f := by
  intro β hβ
  rcases le_or_gt 1 β with h1 | h1
  · exact h β h1
  · obtain ⟨f, hf⟩ := h β⁻¹ ((one_le_inv₀ hβ).mpr h1.le)
    exact ⟨_, hf.reciprocal hβ⟩

/-- Certificates on `0 < β ≤ 1` give certificates for every `β > 0`. -/
theorem hexGaussianContact_all_of_le_one
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ f, HexGaussianContactCertificate2 β f) :
    ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f := by
  intro β hβ
  rcases le_or_gt β 1 with h1 | h1
  · exact h β hβ h1
  · obtain ⟨f, hf⟩ := h β⁻¹ (inv_pos.mpr hβ) (inv_le_one_of_one_le₀ h1.le)
    exact ⟨_, hf.reciprocal hβ⟩

/-- The real theta function of the triangular lattice is continuous on `(0, ∞)` (locally uniform
convergence). -/
theorem hexGaussianThetaReal2_continuousOn :
    ContinuousOn hexGaussianThetaReal2 (Set.Ioi 0) := by
  intro α hα
  have hα0 : (0:ℝ) < α := hα
  have hα2 : 0 < α/2 := half_pos hα0
  have hsum : Summable (fun x : hexLattice =>
      Real.exp (-(Real.pi*(α/2)*‖(x : HexAmbient)‖^2))) :=
    (Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hα2)).summable
  have hc : ContinuousOn hexGaussianThetaReal2 (Set.Ioi (α/2)) := by
    unfold hexGaussianThetaReal2
    refine continuousOn_tsum (fun x => by fun_prop) hsum ?_
    intro x β hβ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ ‖(x : HexAmbient)‖^2 := sq_nonneg _
    have hβ' : α/2 < β := hβ
    have hprod := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hβ'.le)) h0
    nlinarith [hprod]
  exact (hc.continuousAt (isOpen_Ioi.mem_nhds (by linarith : α/2 < α))).continuousWithinAt

end SphericalRiesz
end
end

section

/-! # The regularized theta function of the triangular lattice (stage S2-1)

On the imaginary axis `Θ(it)` is the real Gaussian lattice sum. Poisson inversion gives
`Θ(i/t) = t Θ(it)` (weight `d/2 = 1`), and the minimal squared norm `2/√3` of the lattice gives
the elementary tail bound `Θ(it) - 1 ≤ e^(-(2π/√3)(t-1)) (Θ(i) - 1)` for `t ≥ 1`, with no
modular-form input. Hence `Θ(it) - 1 - t⁻¹` is bounded near `0`, is `O(t⁻¹)` at infinity, and its
Mellin transform converges on `0 < Re s < 1`. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace SphericalRiesz

def hexThetaImag (t : ℝ) : ℂ := hexTheta ((t : ℂ) * Complex.I)

def hexThetaTail (t : ℝ) : ℂ := hexThetaImag t - 1

def hexThetaRegularized (t : ℝ) : ℂ := hexThetaTail t - ((t : ℂ))⁻¹

theorem hexThetaImag_eq_real {t : ℝ} (ht : 0 < t) :
    hexThetaImag t = (hexGaussianThetaReal2 t : ℂ) := by
  have hterm : ∀ x : hexLattice, hexLatticeThetaTerm ((t:ℂ)*Complex.I) x =
      ((Real.exp (-(Real.pi*t*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ) := by
    intro x
    unfold hexLatticeThetaTerm
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : hexLatticeThetaTerm ((t:ℂ)*Complex.I) = fun x : hexLattice =>
      ((Real.exp (-(Real.pi*t*‖(x : HexAmbient)‖^2)) : ℝ) : ℂ) := funext hterm
  unfold hexThetaImag hexTheta
  rw [hfun]
  exact (hexLatticeGaussian_hasSum ht).tsum_eq

/-- The regularized theta function in terms of the real Gaussian lattice sum. -/
theorem hexThetaRegularized_eq_real {t : ℝ} (ht : 0 < t) :
    hexThetaRegularized t = ((hexGaussianThetaReal2 t-t⁻¹-1 : ℝ) : ℂ) := by
  unfold hexThetaRegularized hexThetaTail
  rw [hexThetaImag_eq_real ht]
  push_cast
  ring

theorem hexThetaImag_continuousOn : ContinuousOn hexThetaImag (Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => (hexGaussianThetaReal2 t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn hexGaussianThetaReal2_continuousOn
  exact h.congr (fun t ht => hexThetaImag_eq_real ht)

theorem hexThetaTail_continuousOn : ContinuousOn hexThetaTail (Ioi 0) :=
  hexThetaImag_continuousOn.sub continuousOn_const

theorem hexThetaRegularized_continuousOn : ContinuousOn hexThetaRegularized (Ioi 0) := by
  apply hexThetaTail_continuousOn.sub
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)

/-- `Θ(i/t) = t Θ(it)`: the functional equation of weight one on the imaginary axis. -/
theorem hexThetaImag_transform {t : ℝ} (ht : 0 < t) :
    hexThetaImag t⁻¹ = (t : ℂ) * hexThetaImag t := by
  have h := hexTheta_transform_S (τ := (t : ℂ)*Complex.I) (by simpa using ht)
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hS : -1/((t:ℂ)*Complex.I) = ((t⁻¹ : ℝ) : ℂ)*Complex.I := by
    push_cast
    field_simp
    rw [Complex.I_sq]
  unfold hexThetaImag
  rw [← hS, h, mul_div_cancel_right₀ _ Complex.I_ne_zero]

theorem hexThetaRegularized_inversion {t : ℝ} (ht : 0 < t) :
    hexThetaRegularized t = ((t : ℂ))⁻¹ * hexThetaTail t⁻¹ - 1 := by
  have h := hexThetaImag_transform ht
  have h0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : ((t : ℂ))⁻¹ * (t : ℂ) = 1 := inv_mul_cancel₀ h0
  unfold hexThetaRegularized hexThetaTail
  rw [h]
  linear_combination (-(hexThetaImag t)) * h1

/-- The real tail `Θ(t) - 1` decays like `e^(-(2π/√3) t)`: every nonzero lattice vector has
squared norm at least `2/√3`. -/
theorem hexGaussianThetaReal2_tail_le {t : ℝ} (ht : 1 ≤ t) :
    hexGaussianThetaReal2 t - 1 ≤
      Real.exp (-(2*Real.pi/Real.sqrt 3)*(t-1)) * (hexGaussianThetaReal2 1 - 1) := by
  classical
  have ht0 : 0 < t := by linarith
  let f : ℝ → hexLattice → ℝ := fun u x => Real.exp (-(Real.pi*u*‖(x : HexAmbient)‖^2))
  have hf : ∀ u, 0 < u → HasSum (f u) (hexGaussianThetaReal2 u) := fun u hu =>
    Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hu)
  have hf0 : ∀ u, f u 0 = 1 := fun u => by simp [f]
  have h1 := (hf t ht0).update (0 : hexLattice) 0
  have h2 := ((hf 1 one_pos).update (0 : hexLattice) 0).mul_left
    (Real.exp (-(2*Real.pi/Real.sqrt 3)*(t-1)))
  rw [hf0] at h1 h2
  have hle : ∀ x, Function.update (f t) (0 : hexLattice) 0 x ≤
      Real.exp (-(2*Real.pi/Real.sqrt 3)*(t-1)) * Function.update (f 1) (0 : hexLattice) 0 x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
      have hx0 : (x : HexAmbient) ≠ 0 := fun h => hx (Subtype.ext h)
      have hn := hexLattice_norm_sq_ge x hx0
      simp only [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h3 : 0 ≤ t-1 := by linarith
      have h4 : Real.pi*(t-1)*(2/Real.sqrt 3) ≤ Real.pi*(t-1)*‖(x : HexAmbient)‖^2 :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg Real.pi_pos.le h3)
      have h5 : -(2*Real.pi/Real.sqrt 3)*(t-1) = -(Real.pi*(t-1)*(2/Real.sqrt 3)) := by ring
      have h6 : -(Real.pi*t*‖(x : HexAmbient)‖^2) =
          -(Real.pi*(t-1)*‖(x : HexAmbient)‖^2)+-(Real.pi*1*‖(x : HexAmbient)‖^2) := by ring
      rw [h5, h6]
      linarith
  have := hasSum_le hle h1 h2
  linarith

theorem hexGaussianThetaReal2_ge_one' {t : ℝ} (ht : 0 < t) : 1 ≤ hexGaussianThetaReal2 t :=
  hexGaussianThetaReal2_ge_one ht

theorem hexThetaTail_exp_decay :
    hexThetaTail =O[atTop] (fun t : ℝ => Real.exp (-(2*Real.pi/Real.sqrt 3)*t)) := by
  refine isBigO_iff.mpr
    ⟨Real.exp (2*Real.pi/Real.sqrt 3) * (hexGaussianThetaReal2 1 - 1), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have htail : hexThetaTail t = ((hexGaussianThetaReal2 t - 1 : ℝ) : ℂ) := by
    unfold hexThetaTail
    rw [hexThetaImag_eq_real ht0]
    push_cast
    ring
  rw [htail, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [hexGaussianThetaReal2_ge_one ht0]), abs_of_pos (Real.exp_pos _)]
  have h := hexGaussianThetaReal2_tail_le ht
  have he : Real.exp (-(2*Real.pi/Real.sqrt 3)*(t-1)) =
      Real.exp (2*Real.pi/Real.sqrt 3) * Real.exp (-(2*Real.pi/Real.sqrt 3)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  linarith

theorem hexThetaTail_littleO_rpow (a : ℝ) :
    hexThetaTail =o[atTop] (fun t : ℝ => t^a) :=
  hexThetaTail_exp_decay.trans_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop (by positivity) a)

theorem hexThetaTail_scaled_tendsto :
    Tendsto (fun t : ℝ => (t : ℂ) * hexThetaTail t) atTop (𝓝 0) := by
  have h := (hexThetaTail_littleO_rpow (-1)).tendsto_inv_smul_nhds_zero (𝕜 := ℝ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.rpow_neg ht.le, inv_inv, Real.rpow_one, Complex.real_smul]

theorem hexThetaRegularized_tendsto_zero :
    Tendsto hexThetaRegularized (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have h := hexThetaTail_scaled_tendsto.comp tendsto_inv_nhdsGT_zero
  have h' := h.sub_const (1 : ℂ)
  simp only [zero_sub] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hexThetaRegularized_inversion ht]
  simp [Complex.ofReal_inv]

theorem hexThetaRegularized_bigO_zero :
    hexThetaRegularized =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t^(-(0 : ℝ))) := by
  simpa using hexThetaRegularized_tendsto_zero.isBigO_one ℝ

theorem hexThetaRegularized_bigO_infty :
    hexThetaRegularized =O[atTop] (fun t : ℝ => t^(-(1 : ℝ))) := by
  have hp : (fun t : ℝ => ((t : ℂ))⁻¹) =O[atTop]
      (fun t : ℝ => t^(-(1 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with t ht
    have he : ‖((t : ℂ))⁻¹‖ = 1 * ‖t^(-(1 : ℝ))‖ := by
      rw [norm_inv, Complex.norm_real, one_mul, Real.rpow_neg ht.le, Real.rpow_one, norm_inv]
    exact he.le
  exact (hexThetaTail_littleO_rpow (-1)).isBigO.sub hp

theorem hexThetaRegularized_mellinConvergent {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : MellinConvergent hexThetaRegularized s :=
  mellinConvergent_of_isBigO_rpow
    (hexThetaRegularized_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    hexThetaRegularized_bigO_infty h1 hexThetaRegularized_bigO_zero h0

theorem hexThetaRegularized_mellin_differentiableAt {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    DifferentiableAt ℂ (mellin hexThetaRegularized) s := by
  exact (mellin_hasDerivAt_of_isBigO_rpow
    (hexThetaRegularized_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    hexThetaRegularized_bigO_infty h1 hexThetaRegularized_bigO_zero h0).2.differentiableAt

end SphericalRiesz
end
end

section

/-! The continued Epstein zeta function of the triangular lattice of covolume one.

The abstract Mellin functional equation applied to the theta function of the triangular lattice
(weight `1`) gives the completed function `Λ(u)`, differentiable away from `u = 0, 1`.  For
`Re u > 1` it is `π^(-u) Γ(u) Σ_{x ∈ Λ, x ≠ 0} (|x|²)^(-u)`; the lattice sum converges there by the
general summability of `‖x‖^r` over a lattice of rank 2.  In the strip `0 < u < 1` it is the
Mellin integral of the regularized theta function `Θ(t) - 1 - t⁻¹`.  Hence

`ζ_Λ(2u) := π^u Λ(u)/Γ(u)`

is the Epstein zeta function of the triangular lattice where the series converges and is
differentiable for `Re u > 0`, `u ≠ 1`.  A uniqueness statement shows that every continuation of
the series which is analytic in the open upper quadrant and continuous at the real point gives the
same value.  No closed formula (`6 ζ(u) L(u, χ₋₃)` up to the scaling) is used or proved.  The
identification with the coefficient of the S² Riesz asymptotics belongs to the sphere chain and
is not part of this file. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace SphericalRiesz

/-- The abstract functional-equation pair of the theta function of the triangular lattice on the
imaginary axis: weight `1`. -/
def hexThetaFEPair : WeakFEPair ℂ where
  f := hexThetaImag
  g := hexThetaImag
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := hexThetaImag_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hg_int := hexThetaImag_continuousOn.locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq t ht := by
    simpa [one_div, Real.rpow_one, smul_eq_mul] using hexThetaImag_transform ht
  hf_top r := (hexThetaTail_littleO_rpow r).isBigO
  hg_top r := (hexThetaTail_littleO_rpow r).isBigO

/-- The completed Epstein function of the triangular lattice. -/
def hexThetaCompleted : ℂ → ℂ := hexThetaFEPair.Λ

theorem hexThetaCompleted_differentiableAt {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ hexThetaCompleted s :=
  hexThetaFEPair.differentiableAt_Λ (Or.inl h0) (Or.inl h1)

theorem hexThetaCompleted_eq_mellin {s : ℂ} (hs : 1 < s.re) :
    hexThetaCompleted s = mellin hexThetaTail s :=
  (hexThetaFEPair.hasMellin hs).2.symm

/-- The theta tail as a Gaussian sum over the nonzero lattice vectors. -/
theorem hexThetaTail_gaussian_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun x : hexLattice => if ‖(x : HexAmbient)‖^2 = 0 then (0 : ℂ)
      else ((Real.exp (-Real.pi*‖(x : HexAmbient)‖^2*t) : ℝ) : ℂ)) (hexThetaTail t) := by
  classical
  have h := hasSum_ite_sub_hasSum (hexLatticeGaussian_hasSum ht) (0 : hexLattice)
  have hz0 (x : hexLattice) : ‖(x : HexAmbient)‖^2 = 0 ↔ x = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero]
    exact ⟨fun hx => Subtype.ext hx, fun hx => by rw [hx]; rfl⟩
  have hval : ((hexGaussianThetaReal2 t : ℝ) : ℂ)-
      ((Real.exp (-(Real.pi*t*‖((0 : hexLattice) : HexAmbient)‖^2)) : ℝ) : ℂ) =
      hexThetaTail t := by
    unfold hexThetaTail
    rw [hexThetaImag_eq_real ht]
    simp
  rw [hval] at h
  apply h.congr_fun
  intro x
  simp only [hz0]
  split_ifs
  · rfl
  · congr 2
    ring

/-- Summability of the Epstein series of the triangular lattice beyond the critical exponent. -/
theorem hexEpstein_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun x : hexLattice => ‖(1 : ℂ)‖/(‖(x : HexAmbient)‖^2)^s.re) := by
  have hr : -(2*s.re) < -(Module.finrank ℤ hexLattice : ℝ) := by
    rw [hexLattice_rank]
    push_cast
    linarith
  have h := ZLattice.summable_norm_rpow hexLattice (-(2*s.re)) hr
  apply h.congr
  intro x
  have hx : (‖(x : HexAmbient)‖^2)^s.re = ‖(x : HexAmbient)‖^(2*s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [norm_one, one_div, hx, ← Real.rpow_neg (norm_nonneg _)]
  try rfl

/-- Terms of the Epstein series of the triangular lattice, `(|x|²)^(-u)`; the term of `x = 0`
vanishes for `u ≠ 0`. -/
def hexEpsteinTerm (u : ℂ) (x : hexLattice) : ℂ :=
  ((‖(x : HexAmbient)‖^2 : ℝ) : ℂ)^(-u)

/-- The completed function is `π^(-u) Γ(u)` times the Epstein series for `Re u > 1`. -/
theorem hexThetaCompleted_hasSum_epstein {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun x : hexLattice => (Real.pi : ℂ)^(-s)*Complex.Gamma s*hexEpsteinTerm s x)
      (hexThetaCompleted s) := by
  have hs0 : 0 < s.re := by linarith
  have hm := hasSum_mellin_pi_mul₀ (a := fun _ : hexLattice => (1 : ℂ))
    (F := hexThetaTail) (s := s) (p := fun x => ‖(x : HexAmbient)‖^2)
    (fun x => sq_nonneg _) hs0
    (fun t ht => by simpa only [one_mul] using hexThetaTail_gaussian_hasSum ht)
    (hexEpstein_norm_summable hs)
  rw [hexThetaCompleted_eq_mellin hs]
  apply hm.congr_fun
  intro x
  have hneg : ((‖(x : HexAmbient)‖^2 : ℝ) : ℂ)^(-s) =
      (((‖(x : HexAmbient)‖^2 : ℝ) : ℂ)^s)⁻¹ := Complex.cpow_neg _ _
  unfold hexEpsteinTerm
  rw [hneg, mul_one, div_eq_mul_inv]

/-- The Epstein zeta function of the triangular lattice in the variable `u = s/2`, continued:
`π^u Λ(u)/Γ(u)`. -/
def hexEpsteinZeta (u : ℂ) : ℂ := (Real.pi : ℂ)^u*hexThetaCompleted u/Complex.Gamma u

/-- Where the series converges, the continued function is the Epstein series. -/
theorem hexEpsteinZeta_hasSum {u : ℂ} (hu : 1 < u.re) :
    HasSum (hexEpsteinTerm u) (hexEpsteinZeta u) := by
  have hu0 : 0 < u.re := by linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπu : (Real.pi : ℂ)^u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hΓ : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu0
  have hneg : (Real.pi : ℂ)^(-u) = ((Real.pi : ℂ)^u)⁻¹ := Complex.cpow_neg _ _
  have h := (hexThetaCompleted_hasSum_epstein hu).mul_left ((Real.pi : ℂ)^u/Complex.Gamma u)
  have hval : (Real.pi : ℂ)^u/Complex.Gamma u*hexThetaCompleted u = hexEpsteinZeta u := by
    unfold hexEpsteinZeta
    ring
  rw [hval] at h
  apply h.congr_fun
  intro x
  rw [hneg, show (Real.pi : ℂ)^u/Complex.Gamma u*
      (((Real.pi : ℂ)^u)⁻¹*Complex.Gamma u*hexEpsteinTerm u x) =
      ((Real.pi : ℂ)^u*((Real.pi : ℂ)^u)⁻¹)*(Complex.Gamma u/Complex.Gamma u)*
        hexEpsteinTerm u x by ring,
    mul_inv_cancel₀ hπu, div_self hΓ, one_mul, one_mul]

theorem hexEpsteinZeta_differentiableAt {u : ℂ} (hu : 0 < u.re) (h1 : u ≠ 1) :
    DifferentiableAt ℂ hexEpsteinZeta u := by
  have h0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hΓ := Complex.differentiableAt_Gamma u (fun m h => by
    have hneg : (-(m : ℂ)).re ≤ 0 := by simp
    rw [← h] at hneg
    exact (not_le_of_gt hu) hneg)
  have hΓ0 : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu
  have hpow : DifferentiableAt ℂ (fun v : ℂ => (Real.pi : ℂ)^v) u :=
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact (hpow.mul (hexThetaCompleted_differentiableAt h0 h1)).div hΓ hΓ0

theorem hexThetaFEPair_modified_weighted_ae_rpow (u : ℝ) :
    (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • hexThetaFEPair.f_modif t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t +
        (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t +
        (Ioi 1).indicator (fun t : ℝ => ((t^(u-2) : ℝ) : ℂ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  have hc : (t:ℂ)^((u:ℂ)-1) = ((t^(u-1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht0.le]
    push_cast
    ring_nf
  have hc2 : ((t^(u-2) : ℝ) : ℂ) = ((t^(u-1) : ℝ) : ℂ) * ((t:ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [show u-2 = (u-1)-(1:ℝ) by ring, Real.rpow_sub ht0, Real.rpow_one, div_eq_mul_inv]
  have h1 : ((t^(-(1:ℝ)) : ℝ) : ℂ) = ((t:ℂ))⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_one, Complex.ofReal_inv]
  simp only [WeakFEPair.f_modif, hexThetaFEPair, Pi.add_apply, hc, smul_eq_mul]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hA : t ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    have hB : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, hsmall⟩
    simp only [indicator_of_notMem hA, indicator_of_mem hB, h1]
    unfold hexThetaRegularized hexThetaTail
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, hc2]
    unfold hexThetaRegularized hexThetaTail
    ring

/-- In the strip, the completed value is the Mellin integral of the regularized theta. -/
theorem hexThetaCompleted_eq_integral_strip {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    hexThetaCompleted (u:ℂ) =
      ∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t := by
  have hreg : IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t) (Ioi 0) :=
    hexThetaRegularized_mellinConvergent (s := (u:ℂ)) (by simpa using hu0) (by simpa using hu1)
  have hsmall : IntegrableOn (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)).ofReal
  have hlarge : IntegrableOn (fun t : ℝ => ((t^(u-2) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have hs := (hsmall.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi 0)
  have hl := (hlarge.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have Ismall : (∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t) =
      1/(u:ℂ) := by
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < u-1))]
    have hu : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hu0.ne', sub_zero]
    push_cast
    field_simp
  have Ilarge : (∫ t : ℝ in Ioi 0, (Ioi 1).indicator (fun t : ℝ => ((t^(u-2) : ℝ) : ℂ)) t) =
      1/(1-(u:ℂ)) := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)),
      integral_complex_ofReal, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    have hval : -1/(u-1) = 1/(1-u) := by
      have hd1 : u-1 ≠ 0 := by linarith
      have hd2 : 1-u ≠ 0 := by linarith
      rw [div_eq_div_iff hd1 hd2]
      ring
    simp only [Real.one_rpow, show u-2+1 = u-1 by ring]
    rw [hval]
    push_cast
    ring
  have hm : mellin hexThetaFEPair.f_modif (u:ℂ) =
      (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t) + 1/(u:ℂ) +
        1/(1-(u:ℂ)) := by
    unfold mellin
    rw [integral_congr_ae (hexThetaFEPair_modified_weighted_ae_rpow u)]
    have e1 : (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t +
          (Ioi 1).indicator (fun t : ℝ => ((t^(u-2) : ℝ) : ℂ)) t)) =
        (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t)) +
        ∫ t : ℝ in Ioi 0, (Ioi 1).indicator (fun t : ℝ => ((t^(u-2) : ℝ) : ℂ)) t :=
      integral_add (hreg.add hs) hl
    have e2 : (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t +
          (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t)) =
        (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t) +
        ∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) t :=
      integral_add hreg hs
    rw [e1, e2, Ismall, Ilarge]
  change mellin hexThetaFEPair.f_modif (u:ℂ) - (1/(u:ℂ))*1 - (1/(1-(u:ℂ)))*1 = _
  rw [hm]
  ring

/-- Uniqueness at the real points of the strip: a function which is analytic in the open upper
quadrant, equals the Epstein series where the series converges and is continuous at a real point
`0 < u`, `u ≠ 1`, has the value `hexEpsteinZeta u` there. -/
theorem hexEpsteinZeta_unique_real {Z : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z {v : ℂ | 0 < v.re ∧ 0 < v.im})
    (hser : ∀ v : ℂ, 1 < v.re → 0 < v.im → HasSum (hexEpsteinTerm v) (Z v))
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≠ 1) (hcont : ContinuousAt Z (u:ℂ)) :
    Z (u:ℂ) = hexEpsteinZeta (u:ℂ) := by
  let U : Set ℂ := {v | 0 < v.re ∧ 0 < v.im}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (r := 0)).inter (convex_halfSpace_im_gt (r := 0))).isPreconnected
  have hreal {v : ℂ} (hv : v ∈ U) : v ≠ 1 := by
    intro h
    have hi : 0 < v.im := hv.2
    rw [h] at hi
    norm_num at hi
  have hf : AnalyticOnNhd ℂ Z U := hZ.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ hexEpsteinZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro v hv
    exact (hexEpsteinZeta_differentiableAt hv.1 (hreal hv)).differentiableWithinAt
  have hopen : IsOpen {v : ℂ | 1 < v.re ∧ 0 < v.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hbase : ((2 : ℂ)+Complex.I) ∈ {v : ℂ | 1 < v.re ∧ 0 < v.im} := by
    show 1 < ((2 : ℂ)+Complex.I).re ∧ 0 < ((2 : ℂ)+Complex.I).im
    constructor <;> norm_num
  have hfg : Z =ᶠ[𝓝 ((2 : ℂ)+Complex.I)] hexEpsteinZeta := by
    filter_upwards [hopen.mem_nhds hbase] with v hv
    exact (hser v hv.1 hv.2).unique (hexEpsteinZeta_hasSum hv.1)
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc
    (show 0 < ((2 : ℂ)+Complex.I).re ∧ 0 < ((2 : ℂ)+Complex.I).im by
      constructor <;> norm_num) hfg
  have ht : Tendsto (fun ε : ℝ => (u : ℂ)+(ε : ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hε |>.mul_const Complex.I)
  have hu1' : (u:ℂ) ≠ 1 := by
    intro h
    have : u = 1 := by exact_mod_cast h
    exact hu1 this
  apply tendsto_nhds_unique_of_eventuallyEq (hcont.tendsto.comp ht)
    ((hexEpsteinZeta_differentiableAt (u := (u:ℂ)) (by simpa using hu0)
      hu1').continuousAt.tendsto.comp ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply heq
  have hε0 : 0 < ε := hε
  show 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).re ∧ 0 < ((u:ℂ)+(ε:ℂ)*Complex.I).im
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
  exact ⟨hu0, hε0⟩

/-- The real part of the completed value in the strip is the weighted integral of the real
regularized theta function `Θ(α) - α⁻¹ - 1`. -/
theorem hexThetaCompleted_re_eq_integral {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (hexThetaCompleted (u:ℂ)).re =
      ∫ α : ℝ in Ioi 0, α^(u-1)*(hexGaussianThetaReal2 α-α⁻¹-1) := by
  rw [hexThetaCompleted_eq_integral_strip hu0 hu1]
  have hint : IntegrableOn
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t) (Ioi 0) :=
    hexThetaRegularized_mellinConvergent (s := (u:ℂ)) (by simpa using hu0) (by simpa using hu1)
  have h := integral_re hint
  change (∫ t : ℝ in Ioi 0, (((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t).re) =
    (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • hexThetaRegularized t).re at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α hα
  have hα0 : 0 < α := hα
  have hc : (α:ℂ)^((u:ℂ)-1) = ((α^(u-1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hα0.le]
    push_cast
    ring_nf
  show (((α:ℂ)^((u:ℂ)-1)) • hexThetaRegularized α).re = α^(u-1)*(hexGaussianThetaReal2 α-α⁻¹-1)
  rw [hc, hexThetaRegularized_eq_real hα0, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

end SphericalRiesz
end
end

section

/-! The continuous linear inverse of the coordinate map of the triangular lattice, in the form
used by the patch constructions (the dimension-2 counterpart of `leechInverseMap`). -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

/-- The inverse of the coordinate map `hexMap` of the triangular lattice. -/
def hexInverseMap : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  hexBasis.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

theorem hexInverseMap_hexMap (v : Fin 2 → ℝ) : hexInverseMap (hexMap v) = v :=
  hexBasis.equivFun.apply_symm_apply v

theorem hexMap_hexInverseMap (v : Fin 2 → ℝ) : hexMap (hexInverseMap v) = v :=
  hexBasis.equivFun.symm_apply_apply v

end SphericalRiesz
end
end
