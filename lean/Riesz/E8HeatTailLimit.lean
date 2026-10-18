import Riesz.E8HeatCellComparison
import Mathlib.Analysis.Normed.Group.Tannery

/-! The actual Gaussian tail disappears at large radius, for each ε>0.
Both the integer sum and the continuous background use the actual checked heat kernel.
This limit is not asserted for the undamped inverse-fourth kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem e8CoordinateHeatKernel_nonneg (ε : ℝ) (y : Fin 8 → ℝ) :
    0 ≤ e8CoordinateHeatKernel ε y := by
  rw [e8CoordinateHeatKernel_eq]
  unfold e8HeatBackgroundKernel
  positivity

theorem e8HeatTailKernel_zero_inside (ε : ℝ) {R : ℝ} (hR : 0 < R)
    (y : Fin 8 → ℝ) (hy : ‖y‖ ≤ R) : e8HeatTailKernel ε R y = 0 := by
  have hb : outerUnitBump 8 (R⁻¹ • y) = 1 := by
    apply (outerUnitBump 8).one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖R⁻¹ • y‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ← div_eq_inv_mul]
    exact (div_le_one hR).mpr hy
  simp only [e8HeatTailKernel, hb, sub_self, mul_zero]

theorem e8HeatTailKernel_integer (ε R : ℝ) (z : Fin 8 → ℤ) :
    e8HeatTailKernel ε R (fun i => (z i : ℝ)) = e8HeatCellTailTerm ε R z := by
  simp only [e8HeatTailKernel, e8HeatCellTailTerm, e8CoordinateHeatKernel_integer]

theorem e8HeatTailKernel_radius_limit (ε : ℝ) (y : Fin 8 → ℝ) :
    Tendsto (fun R : ℝ => e8HeatTailKernel ε R y) atTop (𝓝 0) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0)).congr'
  filter_upwards [eventually_ge_atTop (max 1 ‖y‖)] with R hR
  have hpos : 0 < R := by linarith [le_max_left (1:ℝ) ‖y‖]
  exact (e8HeatTailKernel_zero_inside ε hpos y ((le_max_right _ _).trans hR)).symm

theorem e8HeatCellTailTerm_norm_le (ε R : ℝ) (z : Fin 8 → ℤ) :
    ‖e8HeatCellTailTerm ε R z‖ ≤ e8HeatTerm ε z := by
  rw [Real.norm_of_nonneg (e8HeatCellTailTerm_nonneg ε R z)]
  unfold e8HeatCellTailTerm
  apply mul_le_of_le_one_right (e8HeatTerm_nonneg ε z)
  linarith [(outerUnitBump 8).nonneg (x := R⁻¹ • (fun i => (z i : ℝ)))]

theorem e8HeatCellTailTerm_tsum_radius_limit {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ∑' z : Fin 8 → ℤ, e8HeatCellTailTerm ε R z) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun R : ℝ => e8HeatCellTailTerm ε R)
    (g := fun _ : Fin 8 → ℤ => (0:ℝ)) (e8HeatTerm_summable hε)
    (fun z => by simpa only [e8HeatTailKernel_integer] using
      e8HeatTailKernel_radius_limit ε (fun i => (z i : ℝ)))
    (Eventually.of_forall (fun R z => e8HeatCellTailTerm_norm_le ε R z))
  simpa only [tsum_zero] using h

theorem e8HeatTailKernel_integral_radius_limit {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ∫ y : Fin 8 → ℝ, e8HeatTailKernel ε R y) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (μ := (volume : Measure (Fin 8 → ℝ)))
    (F := fun R y => e8HeatTailKernel ε R y) (f := fun _ => (0:ℝ))
    (e8CoordinateHeatKernel ε)
    (Eventually.of_forall (fun R => (e8HeatTailKernel_integrable hε R).aestronglyMeasurable))
    (Eventually.of_forall (fun R => Eventually.of_forall (fun y => by
      simpa only [Real.norm_of_nonneg (e8CoordinateHeatKernel_nonneg ε y)] using
        e8HeatTailKernel_norm_bound ε R y)))
    (e8CoordinateHeatKernel_integrable hε)
    (Eventually.of_forall (e8HeatTailKernel_radius_limit ε))
  simpa only [integral_zero] using h

theorem e8HeatTailDefect_radius_limit {ε : ℝ} (hε : 0 < ε) :
    Tendsto (e8HeatTailDefect ε) atTop (𝓝 0) := by
  change Tendsto (fun R : ℝ =>
    (∑' z : Fin 8 → ℤ, e8HeatCellTailTerm ε R z) -
      ∫ y : Fin 8 → ℝ, e8HeatTailKernel ε R y) atTop (𝓝 0)
  simpa only [sub_zero] using
    (e8HeatCellTailTerm_tsum_radius_limit hε).sub (e8HeatTailKernel_integral_radius_limit hε)

#print axioms e8CoordinateHeatKernel_nonneg
#print axioms e8HeatTailKernel_zero_inside
#print axioms e8HeatTailKernel_integer
#print axioms e8HeatTailKernel_radius_limit
#print axioms e8HeatCellTailTerm_norm_le
#print axioms e8HeatCellTailTerm_tsum_radius_limit
#print axioms e8HeatTailKernel_integral_radius_limit
#print axioms e8HeatTailDefect_radius_limit
end SphericalRiesz
