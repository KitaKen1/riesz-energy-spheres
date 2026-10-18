import Riesz.E8Theta
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# The actual integer basis image as a discrete Euclidean lattice

The real basis is transported to the L2 space before taking its integer span.
An explicit linear equivalence identifies every integer label with exactly
one lattice point. This keeps the lattice used in the theta sum unchanged.
-/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

abbrev E8Ambient := EuclideanSpace ℝ (Fin 8)

def e8EuclideanBasis : Module.Basis (Fin 8) ℝ E8Ambient :=
  e8Basis.map (WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm

def e8Lattice : Submodule ℤ E8Ambient :=
  Submodule.span ℤ (Set.range e8EuclideanBasis)

instance : DiscreteTopology e8Lattice := by
  unfold e8Lattice
  infer_instance

instance : IsZLattice ℝ e8Lattice := by
  unfold e8Lattice
  infer_instance

def e8IntegerBasis : Module.Basis (Fin 8) ℤ e8Lattice :=
  e8EuclideanBasis.restrictScalars ℤ

def e8LatticeEquiv : (Fin 8 → ℤ) ≃ₗ[ℤ] e8Lattice :=
  e8IntegerBasis.equivFun.symm

theorem e8LatticeEquiv_coe (z : Fin 8 → ℤ) :
    (e8LatticeEquiv z : E8Ambient) = e8EuclideanPoint z := by
  have hB (i : Fin 8) : (e8IntegerBasis i : E8Ambient) =
      (WithLp.linearEquiv 2 ℝ (Fin 8 → ℝ)).symm (e8Basis i) := by
    change ((e8EuclideanBasis.restrictScalars ℤ) i : E8Ambient) = _
    rw [Module.Basis.restrictScalars_apply, e8EuclideanBasis, Module.Basis.map_apply]
  rw [e8LatticeEquiv, Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hB,
    ← map_zsmul, ← map_sum]
  change WithLp.toLp 2 (∑ i, z i • e8Basis i) = WithLp.toLp 2 (e8IntegerPoint z)
  congr 1
  rw [e8IntegerPoint, e8Map_eq_sum]
  simp only [e8Basis_apply, Int.cast_smul_eq_zsmul ℝ]

theorem e8Lattice_mem_iff (x : E8Ambient) :
    x ∈ e8Lattice ↔ ∃ z : Fin 8 → ℤ, e8EuclideanPoint z = x := by
  constructor
  · intro hx
    refine ⟨e8LatticeEquiv.symm ⟨x, hx⟩, ?_⟩
    rw [← e8LatticeEquiv_coe, e8LatticeEquiv.apply_symm_apply]
  · rintro ⟨z, rfl⟩
    rw [← e8LatticeEquiv_coe]
    exact (e8LatticeEquiv z).property

theorem e8Lattice_rank : Module.finrank ℤ e8Lattice = 8 := by
  rw [ZLattice.rank ℝ]
  exact finrank_euclideanSpace_fin

theorem e8Lattice_even (x : e8Lattice) :
    ∃ k : ℕ, ‖(x : E8Ambient)‖^2 = 2*(k:ℝ) := by
  obtain ⟨z, hz⟩ := (e8Lattice_mem_iff x).mp x.property
  rw [← hz]
  exact e8ParityPoint_norm_sq_even (e8IntegerPoint z) (e8IntegerPoint_mem_parity z)

theorem e8Lattice_finite_norm_lt (R : ℝ) :
    {x : e8Lattice | ‖(x : E8Ambient)‖ < R}.Finite := by
  have hf := ZSpan.setFinite_inter e8EuclideanBasis
    (s := Metric.ball (0 : E8Ambient) R) Metric.isBounded_ball
  have hpre := hf.preimage_embedding (Function.Embedding.subtype (fun x => x ∈ e8Lattice))
  convert hpre using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.Embedding.subtype_apply,
    Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, SetLike.mem_coe]
  exact (and_iff_left x.property).symm

theorem e8Lattice_summable_norm_rpow :
    Summable (fun x : e8Lattice => ‖x‖ ^ (-10 : ℝ)) :=
  ZLattice.summable_norm_rpow e8Lattice (-10) (by rw [e8Lattice_rank]; norm_num)

#print axioms e8LatticeEquiv_coe
#print axioms e8Lattice_mem_iff
#print axioms e8Lattice_rank
#print axioms e8Lattice_even
#print axioms e8Lattice_finite_norm_lt
#print axioms e8Lattice_summable_norm_rpow

end SphericalRiesz
