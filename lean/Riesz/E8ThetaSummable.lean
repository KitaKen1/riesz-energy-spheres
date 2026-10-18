import Riesz.E8Lattice
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Convergence of the actual E8 theta series

The comparison with a lattice p-series follows the proof architecture of
Sphere-Packing-Lean, commit 1e98fb493088948ca7bbf47d7faed49cc5b39fc4,
Dim24/Uniqueness/Rigidity/Classify/EvenUnimodular/ThetaAnalytic.lean
(Apache 2.0; third_party/SpherePacking/LICENSE).
Here the actual eight-dimensional basis and its integer-label equivalence
are used. No shell formula, modularity, or regularized value is assumed.
-/

set_option autoImplicit false
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace SphericalRiesz

def e8LatticeThetaTerm (τ : ℂ) (x : e8Lattice) : ℂ :=
  Complex.exp ((Real.pi : ℂ)*Complex.I*(‖(x : E8Ambient)‖^2 : ℝ)*τ)

theorem e8LatticeThetaTerm_norm (τ : ℂ) (x : e8Lattice) :
    ‖e8LatticeThetaTerm τ x‖ = Real.exp (-Real.pi*‖(x : E8Ambient)‖^2*τ.im) := by
  unfold e8LatticeThetaTerm
  rw [Complex.norm_exp]
  congr 1
  have he : (Real.pi : ℂ)*Complex.I*(‖(x : E8Ambient)‖^2 : ℝ)*τ =
      ((Real.pi*‖(x : E8Ambient)‖^2 : ℝ) : ℂ)*(τ*Complex.I) := by
    push_cast
    ring
  rw [he, Complex.re_ofReal_mul, Complex.mul_I_re]
  ring

theorem e8LatticeThetaTerm_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (e8LatticeThetaTerm τ) := by
  have hdecay : (fun t : ℝ => Real.exp (-Real.pi*τ.im*t^2)) =o[atTop]
      (fun t : ℝ => t^(-10 : ℝ)) := by
    have ha : -Real.pi*τ.im < 0 := by nlinarith [Real.pi_pos]
    simpa only [zero_mul, add_zero] using
      rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 (-10)
  obtain ⟨C, hC, hbound⟩ := hdecay.isBigO.exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp hbound.bound
  have hfinite := e8Lattice_finite_norm_lt R
  have hevent : ∀ᶠ x : e8Lattice in cofinite,
      ‖e8LatticeThetaTerm τ x‖ ≤ C*‖x‖^(-10 : ℝ) := by
    apply eventually_cofinite.mpr
    apply hfinite.subset
    intro x hx
    by_contra hsmall
    have hlarge : R ≤ ‖(x : E8Ambient)‖ := le_of_not_gt hsmall
    have h := hR ‖(x : E8Ambient)‖ hlarge
    have hb : Real.exp (-Real.pi*τ.im*‖(x : E8Ambient)‖^2) ≤
        C*‖(x : E8Ambient)‖^(-10 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using h
    apply hx
    simpa only [e8LatticeThetaTerm_norm, Submodule.norm_coe,
      mul_assoc, mul_left_comm, mul_comm] using hb
  apply Summable.of_norm_bounded_eventually (e8Lattice_summable_norm_rpow.mul_left C)
  filter_upwards [hevent] with x hx
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos hC,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx

theorem e8Theta_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun z : Fin 8 → ℤ => Complex.exp ((Real.pi : ℂ)*Complex.I*
      (‖e8EuclideanPoint z‖^2 : ℝ)*τ)) := by
  have h := (e8LatticeThetaTerm_summable hτ).comp_injective e8LatticeEquiv.injective
  simpa only [Function.comp_def, e8LatticeThetaTerm, e8LatticeEquiv_coe] using h

theorem e8Theta_hasSum {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun z : Fin 8 → ℤ => Complex.exp ((Real.pi : ℂ)*Complex.I*
      (‖e8EuclideanPoint z‖^2 : ℝ)*τ)) (e8Theta τ) :=
  (e8Theta_summable hτ).hasSum

theorem e8Theta_lattice_tsum (τ : ℂ) :
    e8Theta τ = ∑' x : e8Lattice, e8LatticeThetaTerm τ x := by
  rw [← e8LatticeEquiv.toEquiv.tsum_eq]
  apply tsum_congr
  intro z
  change Complex.exp ((Real.pi : ℂ)*Complex.I*(‖e8EuclideanPoint z‖^2 : ℝ)*τ) =
    e8LatticeThetaTerm τ (e8LatticeEquiv z)
  rw [e8LatticeThetaTerm, e8LatticeEquiv_coe]

#print axioms e8LatticeThetaTerm_norm
#print axioms e8LatticeThetaTerm_summable
#print axioms e8Theta_summable
#print axioms e8Theta_hasSum
#print axioms e8Theta_lattice_tsum

end SphericalRiesz
