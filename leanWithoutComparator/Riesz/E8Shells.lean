import Riesz.E8ThetaModular

/-!
# Actual E8 shells from q-expansion uniqueness

Group the actual absolutely convergent theta series by half the squared
norm. Every fiber is finite. Uniqueness of a convergent q-expansion then
identifies its cardinality, without enumerating vectors or bounding all
coordinates in a search box. Compare the shell blueprint in the pinned
Sphere-Packing-Lean ThetaSeries module (rank 24); the proofs here use the
already checked actual E8 integer labels and rank-eight lattice.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
namespace SphericalRiesz

def e8ShellIndex (z : Fin 8 → ℤ) : ℕ := (e8HalfNorm z).toNat

theorem e8ShellIndex_norm_sq (z : Fin 8 → ℤ) :
    ‖e8EuclideanPoint z‖^2 = 2*(e8ShellIndex z : ℝ) := by
  rw [e8EuclideanPoint_norm_sq]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg (e8HalfNorm_nonneg z)).symm

theorem e8ShellIndex_zero_iff (z : Fin 8 → ℤ) : e8ShellIndex z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hn : ‖e8EuclideanPoint z‖^2 = 0 := by rw [e8ShellIndex_norm_sq, h]; norm_num
    have hz : e8EuclideanPoint z = 0 := by simpa using hn
    exact e8EuclideanPoint_injective (hz.trans e8EuclideanPoint_zero.symm)
  · rintro rfl
    simp [e8ShellIndex, e8HalfNorm]

theorem e8ShellIndex_finite (n : ℕ) : (e8ShellIndex ⁻¹' {n}).Finite := by
  have hb := (e8Lattice_finite_norm_lt (2*(n:ℝ)+1)).preimage_embedding
    e8LatticeEquiv.toEquiv.toEmbedding
  apply hb.subset
  intro z hz
  have hz' : e8ShellIndex z = n := hz
  have hsq : ‖e8EuclideanPoint z‖^2 = 2*(n:ℝ) := by rw [e8ShellIndex_norm_sq, hz']
  change ‖(e8LatticeEquiv z : E8Ambient)‖ < 2*(n:ℝ)+1
  rw [e8LatticeEquiv_coe]
  nlinarith [norm_nonneg (e8EuclideanPoint z), Nat.cast_nonneg (α := ℝ) n]

def e8ShellCount (n : ℕ) : ℕ := Nat.card (e8ShellIndex ⁻¹' {n})

theorem e8Theta_term_eq_qpow (τ : UpperHalfPlane) (z : Fin 8 → ℤ) :
    Complex.exp ((Real.pi : ℂ)*Complex.I*(‖e8EuclideanPoint z‖^2 : ℝ)*(τ : ℂ)) =
      Function.Periodic.qParam 1 τ ^ e8ShellIndex z := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [e8ShellIndex_norm_sq]
  push_cast
  ring

theorem e8Theta_shell_hasSum (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => (e8ShellCount n : ℂ) • Function.Periodic.qParam 1 τ ^ n)
      (e8ThetaUpper τ) := by
  have h := (e8Theta_hasSum τ.im_pos).tsum_fiberwise e8ShellIndex
  apply h.congr_fun
  intro n
  letI : Fintype (e8ShellIndex ⁻¹' {n}) := (e8ShellIndex_finite n).fintype
  have ht : (fun z : e8ShellIndex ⁻¹' {n} => Complex.exp
      ((Real.pi : ℂ)*Complex.I*(‖e8EuclideanPoint z‖^2 : ℝ)*(τ : ℂ))) =
      (fun _ : e8ShellIndex ⁻¹' {n} => Function.Periodic.qParam 1 τ ^ n) := by
    funext z
    rw [e8Theta_term_eq_qpow, show e8ShellIndex z = n from z.property]
  rw [ht, tsum_const]
  simp [e8ShellCount, nsmul_eq_mul]

theorem e8ShellCount_eq_qcoeff (n : ℕ) : (e8ShellCount n : ℂ) =
    (UpperHalfPlane.qExpansion 1 e8ThetaUpper).coeff n :=
  UpperHalfPlane.qExpansion_coeff_unique (h := 1)
    (c := fun m => (e8ShellCount m : ℂ)) e8ThetaModularForm (by norm_num)
    e8ThetaUpper_cusp_analytic e8Theta_shell_hasSum n

theorem e8ShellCount_zero : e8ShellCount 0 = 1 := by
  have h := e8ShellCount_eq_qcoeff 0
  rw [e8ThetaUpper_qExpansion_zero] at h
  exact_mod_cast h

theorem e8ShellCount_positive (n : ℕ) (hn : n ≠ 0) :
    e8ShellCount n = 240 * ArithmeticFunction.sigma 3 n := by
  have h := e8ShellCount_eq_qcoeff n
  rw [e8ThetaUpper_positive_coeff n hn] at h
  exact_mod_cast h

theorem e8ShellCount_one : e8ShellCount 1 = 240 := by
  simpa using e8ShellCount_positive 1 (by decide)

#print axioms e8ShellIndex_norm_sq
#print axioms e8ShellIndex_zero_iff
#print axioms e8ShellIndex_finite
#print axioms e8Theta_term_eq_qpow
#print axioms e8Theta_shell_hasSum
#print axioms e8ShellCount_eq_qcoeff
#print axioms e8ShellCount_zero
#print axioms e8ShellCount_positive
#print axioms e8ShellCount_one
end SphericalRiesz
