import Riesz.EqualAreaInverseD
import Riesz.LeechLattice24
import Riesz.CubeLebesgue

/-! Small dimension-generic helpers for the patch layer (stage P24-2).

`ambientConsD` identifies `ℝ × ℝ^(n+1)` with the ambient space `ℝ^(n+2)` (measure preserving,
`|cons p|² = p₁² + |p₂|²`); the sup norm is bounded by the Euclidean norm; and the Leech
coordinate map has the continuous linear inverse `leechInverseMap`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz

variable {n : ℕ}

def ambientConsD (n : ℕ) : (ℝ × (Fin (n+1) → ℝ)) ≃ᵐ AmbientD (n+1) :=
  (Boundary.cubeConsEquiv (n+1)).trans (MeasurableEquiv.toLp 2 (Fin (n+1+1) → ℝ))

theorem ambientConsD_apply (p : ℝ × (Fin (n+1) → ℝ)) :
    ambientConsD n p = WithLp.toLp 2 (Fin.cons p.1 p.2) := by
  simp [ambientConsD, Boundary.cubeConsEquiv_apply]

theorem ambientConsD_measurePreserving :
    MeasurePreserving (ambientConsD n) volume volume :=
  (PiLp.volume_preserving_toLp (Fin (n+1+1))).comp (Boundary.cubeConsEquiv_measurePreserving (n+1))

theorem ambientConsD_norm_sq (p : ℝ × (Fin (n+1) → ℝ)) :
    ‖ambientConsD n p‖ ^ 2 = p.1 ^ 2 + ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [ambientConsD_apply, Fin.sum_univ_succ]

theorem ambientConsD_dist_sq (p q : ℝ × (Fin (n+1) → ℝ)) :
    dist (ambientConsD n p) (ambientConsD n q)^2 =
      (p.1-q.1)^2+dist (WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin (n+1))) (WithLp.toLp 2 q.2)^2 := by
  have he : ambientConsD n p-ambientConsD n q = ambientConsD n (p.1-q.1, p.2-q.2) := by
    rw [ambientConsD_apply, ambientConsD_apply, ambientConsD_apply, ← WithLp.toLp_sub]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [dist_eq_norm, he, ambientConsD_norm_sq, dist_eq_norm, ← WithLp.toLp_sub]

theorem pi_norm_le_euclideanD {m : ℕ} (v : Fin m → ℝ) :
    ‖v‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 v) i

def leechInverseMap : (Fin 24 → ℝ) →L[ℝ] (Fin 24 → ℝ) :=
  leechBasis.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

theorem leechInverseMap_leechMap (v : Fin 24 → ℝ) : leechInverseMap (leechMap v) = v :=
  leechBasis.equivFun.apply_symm_apply v

theorem leechMap_leechInverseMap (v : Fin 24 → ℝ) : leechMap (leechInverseMap v) = v :=
  leechBasis.equivFun.symm_apply_apply v

#print axioms ambientConsD_apply
#print axioms ambientConsD_measurePreserving
#print axioms ambientConsD_norm_sq
#print axioms ambientConsD_dist_sq
#print axioms pi_norm_le_euclideanD
#print axioms leechInverseMap_leechMap
#print axioms leechMap_leechInverseMap

end SphericalRiesz
