import Riesz.E8HeatTailBound

/-!
# Unconditional limit of the actual compact centered E8 cell defect

The previously explicit heat-tail hypothesis is discharged. This proves
flat compact-cell and centered-row coefficients. Curved global spherical
rows, sharp Gaussian lower bounds and all-N recovery remain separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem e8CompactDefect_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      |e8CompactDefect R-(-5*Real.pi^2/6)| ≤ C/R^2 := by
  obtain ⟨C, hC, hb⟩ := e8HeatTailDefect_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro R hR
  exact e8CompactDefect_bound_of_heatTail (by linarith) C (fun ε hε => hb ε hε R hR)

theorem e8CompactDefect_limit :
    Tendsto e8CompactDefect atTop (𝓝 (-5*Real.pi^2/6)) := by
  obtain ⟨C, _, hb⟩ := e8CompactDefect_uniform_bound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun R => norm_nonneg _))
    (show ∀ᶠ R : ℝ in atTop, ‖e8CompactDefect R-(-5*Real.pi^2/6)‖ ≤ C/R^2 from by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
      simpa only [Real.norm_eq_abs] using hb R hR)
  exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))

theorem e8CompactDefect_normalized_limit :
    Tendsto (fun R : ℝ => e8CompactDefect R/Real.sqrt (sphereArea8.real univ))
      atTop (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact e8CompactDefect_limit.div_const _

theorem e8CompactDefect_actual_norm_formula (R : ℝ) :
    e8CompactDefect R =
      (∑' z : Fin 8 → ℤ, outerUnitBump 8 (R⁻¹ • (fun i => (z i : ℝ))) /
        ‖e8EuclideanPoint z‖^4) -
      ∫ y : Fin 8 → ℝ, outerUnitBump 8 (R⁻¹ • y) /
        ‖(WithLp.toLp 2 (e8Map y) : EuclideanSpace ℝ (Fin 8))‖^4 := by
  unfold e8CompactDefect e8CompactLatticeSum
  simp_rw [e8CompactTerm_eq]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    unfold nearObliqueRieszFour
    rw [obliqueRieszFour_eq_dist]
    simp only [map_zero, WithLp.toLp_zero, dist_zero_left, sub_zero]
    rw [inv_pow, div_eq_mul_inv]
    ring)

theorem e8CenteredRow_diagonal_limit (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hcover : ∀ᶠ q : ℕ in atTop, 2*R q ≤ q) :
    Tendsto (fun q : ℕ => (centeredMesh q : ℝ)^4 *
      (cubeQuadrature 8 (centeredMesh q)
        (nearObliqueRieszFour 8 e8Map (R q/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ))) -
       ∫ y in UnitCube 8,
        nearObliqueRieszFour 8 e8Map (R q/(centeredMesh q : ℝ)) (fun _ => (1/2:ℝ)) y))
      atTop (𝓝 (-5*Real.pi^2/6)) := by
  apply (e8CompactDefect_limit.comp hR).congr'
  filter_upwards [hcover, hR.eventually (eventually_ge_atTop (1:ℝ))] with q hq hRq
  exact e8CompactDefect_eq_scaled_row (by linarith : 0 < R q) q hq

theorem e8CenteredRow_sqrt_limit :
    Tendsto (fun q : ℕ => (centeredMesh q : ℝ)^4 *
      (cubeQuadrature 8 (centeredMesh q)
        (nearObliqueRieszFour 8 e8Map (Real.sqrt (q:ℝ)/(centeredMesh q : ℝ))
          (fun _ => (1/2:ℝ))) -
       ∫ y in UnitCube 8,
        nearObliqueRieszFour 8 e8Map (Real.sqrt (q:ℝ)/(centeredMesh q : ℝ))
          (fun _ => (1/2:ℝ)) y))
      atTop (𝓝 (-5*Real.pi^2/6)) := by
  apply e8CenteredRow_diagonal_limit (fun q => Real.sqrt (q:ℝ))
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (4:ℕ)] with q hq
  have hqr : (4:ℝ) ≤ q := by exact_mod_cast hq
  have hs := Real.sq_sqrt (show 0 ≤ (q:ℝ) by positivity)
  have hn := Real.sqrt_nonneg (q:ℝ)
  have htwo : (2:ℝ) ≤ Real.sqrt (q:ℝ) := by nlinarith
  nlinarith

#print axioms e8CompactDefect_uniform_bound
#print axioms e8CompactDefect_limit
#print axioms e8CompactDefect_normalized_limit
#print axioms e8CompactDefect_actual_norm_formula
#print axioms e8CenteredRow_diagonal_limit
#print axioms e8CenteredRow_sqrt_limit
end SphericalRiesz
