import Riesz.E8Parity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Concrete E8 evenness and the translation law for its theta expression

The integer quadratic form is an explicit certificate for the actual basis
already used by the quadrature nodes. Its discovery is not part of the proof.
The theta expression is the lattice sum, not an Eisenstein series definition.
This module proves the translation law. E8ThetaSummable and E8ThetaAnalytic
prove convergence, holomorphy and the cusp limit 1; E8Dual proves self-duality.
The inversion law and the resulting modular-form connection remain open.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz

def e8EuclideanPoint (z : Fin 8 → ℤ) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 (e8IntegerPoint z)

def e8HalfNorm (z : Fin 8 → ℤ) : ℤ :=
  2*z 0^2 + z 1^2 + z 2^2 + z 3^2 + z 4^2 + z 5^2 + z 6^2 + z 7^2
    - 2*z 0*z 1 - z 1*z 2 - z 2*z 3 - z 3*z 4 - z 4*z 5 - z 5*z 6
    + z 0*z 7

theorem e8EuclideanPoint_norm_sq (z : Fin 8 → ℤ) :
    ‖e8EuclideanPoint z‖^2 = 2*(e8HalfNorm z : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (e8IntegerPoint z i)^2) = _
  simp only [e8IntegerPoint, e8Map_eq_vector, Fin.sum_univ_eight]
  simp [e8HalfNorm]
  ring

theorem e8HalfNorm_nonneg (z : Fin 8 → ℤ) : 0 ≤ e8HalfNorm z := by
  have h := sq_nonneg ‖e8EuclideanPoint z‖
  rw [e8EuclideanPoint_norm_sq] at h
  have : (0 : ℝ) ≤ (e8HalfNorm z : ℝ) := by linarith
  exact_mod_cast this

theorem e8EuclideanPoint_injective : Function.Injective e8EuclideanPoint := by
  intro z w h
  have h' : e8IntegerPoint z = e8IntegerPoint w :=
    congrArg (WithLp.ofLp : EuclideanSpace ℝ (Fin 8) → (Fin 8 → ℝ)) h
  have hc := e8Map_injective h'
  ext i
  exact_mod_cast congrFun hc i

@[simp] theorem e8EuclideanPoint_zero : e8EuclideanPoint 0 = 0 := by
  simp only [e8EuclideanPoint, e8IntegerPoint, Pi.zero_apply, Int.cast_zero]
  change WithLp.toLp 2 (e8Map (0 : Fin 8 → ℝ)) = 0
  rw [map_zero]
  rfl

theorem e8EuclideanPoint_norm_sq_ge_two {z : Fin 8 → ℤ} (hz : z ≠ 0) :
    2 ≤ ‖e8EuclideanPoint z‖^2 := by
  have hp : 0 < ‖e8EuclideanPoint z‖ := norm_pos_iff.mpr fun h =>
    hz (e8EuclideanPoint_injective (h.trans e8EuclideanPoint_zero.symm))
  have hk : 0 < (e8HalfNorm z : ℝ) := by
    have hs := sq_pos_of_pos hp
    rw [e8EuclideanPoint_norm_sq] at hs
    linarith
  have hkZ : 1 ≤ e8HalfNorm z := by
    have : (0 : ℤ) < e8HalfNorm z := by exact_mod_cast hk
    omega
  rw [e8EuclideanPoint_norm_sq]
  have : (1 : ℝ) ≤ (e8HalfNorm z : ℝ) := by exact_mod_cast hkZ
  linarith

theorem e8ParityPoint_norm_sq_even (w : Fin 8 → ℝ) (hw : e8ParityPoint w) :
    ∃ k : ℕ, ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 8))‖^2 = 2*(k:ℝ) := by
  obtain ⟨z, rfl⟩ := e8ParityPoint_exists_integer w hw
  refine ⟨(e8HalfNorm z).toNat, ?_⟩
  have hk : ((e8HalfNorm z).toNat : ℤ) = e8HalfNorm z :=
    Int.toNat_of_nonneg (e8HalfNorm_nonneg z)
  have hkR : ((e8HalfNorm z).toNat : ℝ) = (e8HalfNorm z : ℝ) := by
    exact_mod_cast hk
  rw [hkR]
  exact e8EuclideanPoint_norm_sq z

theorem e8ParityPoint_norm_sq_ge_two (w : Fin 8 → ℝ)
    (hw : e8ParityPoint w) (hw0 : w ≠ 0) :
    2 ≤ ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 8))‖^2 := by
  obtain ⟨z, hz⟩ := e8ParityPoint_exists_integer w hw
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    apply hw0
    have h0 : e8IntegerPoint 0 = 0 := by
      simp only [e8IntegerPoint, Pi.zero_apply, Int.cast_zero]
      change e8Map (0 : Fin 8 → ℝ) = 0
      exact map_zero _
    exact hz.symm.trans h0
  simpa only [e8EuclideanPoint, ← hz] using e8EuclideanPoint_norm_sq_ge_two hz0

/-- A known minimal vector certificate, with no search procedure in the proof. -/
theorem e8EuclideanPoint_minimum_attained :
    ‖e8EuclideanPoint ![0, 1, 0, 0, 0, 0, 0, 0]‖^2 = 2 := by
  rw [e8EuclideanPoint_norm_sq]
  norm_num [e8HalfNorm]

def e8Theta (τ : ℂ) : ℂ :=
  ∑' z : Fin 8 → ℤ, Complex.exp ((Real.pi : ℂ)*Complex.I*
    (‖e8EuclideanPoint z‖^2 : ℝ)*τ)

theorem e8Theta_term_add_one (z : Fin 8 → ℤ) (τ : ℂ) :
    Complex.exp ((Real.pi : ℂ)*Complex.I*(‖e8EuclideanPoint z‖^2 : ℝ)*(τ+1)) =
      Complex.exp ((Real.pi : ℂ)*Complex.I*(‖e8EuclideanPoint z‖^2 : ℝ)*τ) := by
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨e8HalfNorm z, ?_⟩
  rw [e8EuclideanPoint_norm_sq]
  push_cast
  ring

theorem e8Theta_add_one (τ : ℂ) : e8Theta (τ+1) = e8Theta τ := by
  unfold e8Theta
  exact tsum_congr fun z => e8Theta_term_add_one z τ

#print axioms e8EuclideanPoint_norm_sq
#print axioms e8HalfNorm_nonneg
#print axioms e8EuclideanPoint_injective
#print axioms e8EuclideanPoint_zero
#print axioms e8EuclideanPoint_norm_sq_ge_two
#print axioms e8ParityPoint_norm_sq_even
#print axioms e8ParityPoint_norm_sq_ge_two
#print axioms e8EuclideanPoint_minimum_attained
#print axioms e8Theta_term_add_one
#print axioms e8Theta_add_one

end SphericalRiesz
