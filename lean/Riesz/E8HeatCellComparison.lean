import Riesz.E8NearHeatRemoval

/-!
# Exact heat-to-compact comparison for the actual E8 defect

The uniform C/R² tail bound is an explicit input of the final bound
lemma. It is proved for these actual objects in E8HeatTailBound; the
resulting unconditional compact-cell limit is closed in E8CellLimit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

def e8HeatTailKernel (ε R : ℝ) (y : Fin 8 → ℝ) : ℝ :=
  e8CoordinateHeatKernel ε y * (1-outerUnitBump 8 (R⁻¹ • y))

def e8HeatCellTailTerm (ε R : ℝ) (z : Fin 8 → ℤ) : ℝ :=
  e8HeatTerm ε z * (1-outerUnitBump 8 (R⁻¹ • (fun i => (z i : ℝ))))

def e8HeatTailDefect (ε R : ℝ) : ℝ :=
  (∑' z : Fin 8 → ℤ, e8HeatCellTailTerm ε R z) -
    ∫ y : Fin 8 → ℝ, e8HeatTailKernel ε R y

theorem e8HeatCellTailTerm_nonneg (ε R : ℝ) (z : Fin 8 → ℤ) :
    0 ≤ e8HeatCellTailTerm ε R z :=
  mul_nonneg (e8HeatTerm_nonneg ε z) (sub_nonneg.mpr (outerUnitBump 8).le_one)

theorem e8HeatCellTailTerm_summable {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Summable (e8HeatCellTailTerm ε R) := by
  apply Summable.of_nonneg_of_le (e8HeatCellTailTerm_nonneg ε R) _ (e8HeatTerm_summable hε)
  intro z
  apply mul_le_of_le_one_right (e8HeatTerm_nonneg ε z)
  linarith [(outerUnitBump 8).nonneg (x := R⁻¹ • (fun i => (z i : ℝ)))]

theorem e8HeatTailKernel_norm_bound (ε R : ℝ) (y : Fin 8 → ℝ) :
    ‖e8HeatTailKernel ε R y‖ ≤ ‖e8CoordinateHeatKernel ε y‖ := by
  unfold e8HeatTailKernel
  rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr (outerUnitBump 8).le_one)]
  apply mul_le_of_le_one_right (norm_nonneg _)
  linarith [(outerUnitBump 8).nonneg (x := R⁻¹ • y)]

theorem e8HeatTailKernel_integrable {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Integrable (e8HeatTailKernel ε R) := by
  have hc : Continuous (fun y : Fin 8 → ℝ => 1-outerUnitBump 8 (R⁻¹ • y)) :=
    continuous_const.sub (((outerUnitBump 8).contDiff (n := 1)).continuous.comp
      (show Continuous (fun y : Fin 8 → ℝ => R⁻¹ • y) by fun_prop))
  apply MeasureTheory.Integrable.mono (e8CoordinateHeatKernel_integrable hε)
    ((e8CoordinateHeatKernel_integrable hε).aestronglyMeasurable.mul hc.aestronglyMeasurable)
  exact Eventually.of_forall (e8HeatTailKernel_norm_bound ε R)

theorem e8HeatCell_kernel_identity (ε R : ℝ) (y : Fin 8 → ℝ) :
    nearObliqueRieszFour 8 e8Map R 0 y - e8CoordinateHeatKernel ε y =
      e8NearHeatRemovalKernel ε R y - e8HeatTailKernel ε R y := by
  unfold e8NearHeatRemovalKernel e8HeatTailKernel nearObliqueRieszFour e8CoordinateHeatKernel
  simp only [sub_zero]
  ring

theorem e8HeatCell_term_identity (ε R : ℝ) (z : Fin 8 → ℤ) :
    e8CompactTerm R z - e8HeatTerm ε z =
      e8NearHeatRemovalTerm ε R z - e8HeatCellTailTerm ε R z := by
  simpa only [e8CompactTerm, e8NearHeatRemovalTerm, e8NearHeatRemovalKernel,
    e8HeatTailKernel, e8HeatCellTailTerm, e8CoordinateHeatKernel_integer] using
      e8HeatCell_kernel_identity ε R (fun i => (z i : ℝ))

theorem e8HeatCell_tsum_identity {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    e8CompactLatticeSum R - e8HeatEnergy ε =
      (∑' z : Fin 8 → ℤ, e8NearHeatRemovalTerm ε R z) -
        ∑' z : Fin 8 → ℤ, e8HeatCellTailTerm ε R z := by
  unfold e8CompactLatticeSum e8HeatEnergy
  rw [← (e8CompactTerm_summable hR).tsum_sub (e8HeatTerm_summable hε),
    ← (e8NearHeatRemovalTerm_summable hR ε).tsum_sub (e8HeatCellTailTerm_summable hε R)]
  exact tsum_congr (e8HeatCell_term_identity ε R)

theorem e8HeatCell_integral_identity {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∫ y : Fin 8 → ℝ, nearObliqueRieszFour 8 e8Map R 0 y) -
      (∫ y : Fin 8 → ℝ, e8CoordinateHeatKernel ε y) =
    (∫ y : Fin 8 → ℝ, e8NearHeatRemovalKernel ε R y) -
      ∫ y : Fin 8 → ℝ, e8HeatTailKernel ε R y := by
  rw [← integral_sub (e8Near_integrable R hR 0) (e8CoordinateHeatKernel_integrable hε),
    ← integral_sub (e8NearHeatRemovalKernel_integrable hε.le hR) (e8HeatTailKernel_integrable hε R)]
  exact integral_congr_ae (Eventually.of_forall (e8HeatCell_kernel_identity ε R))

theorem e8HeatCell_defect_comparison {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    e8CompactDefect R - e8HeatDefect ε = e8NearHeatRemoval ε R - e8HeatTailDefect ε R := by
  have hs := e8HeatCell_tsum_identity hε hR
  have hi := e8HeatCell_integral_identity hε hR
  rw [e8CoordinateHeatKernel_integral hε] at hi
  unfold e8CompactDefect e8HeatDefect e8NearHeatRemoval e8HeatTailDefect
  rw [e8HeatBackgroundKernel_integral hε]
  linarith

theorem e8HeatTailDefect_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => e8HeatTailDefect ε R) (𝓝[>] (0 : ℝ))
      (𝓝 ((-5*Real.pi^2/6)-e8CompactDefect R)) := by
  have h := ((e8NearHeatRemoval_limit hR).sub_const (e8CompactDefect R)).add e8HeatDefect_limit
  rw [show (0-e8CompactDefect R)+(-5*Real.pi^2/6) =
    (-5*Real.pi^2/6)-e8CompactDefect R by ring] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have heq := e8HeatCell_defect_comparison hε hR
  linarith

/-- The actual tail bound, uniform in ε, is an explicit remaining input. -/
theorem e8CompactDefect_bound_of_heatTail {R : ℝ} (hR : 0 < R) (C : ℝ)
    (hb : ∀ ε : ℝ, 0 < ε → |e8HeatTailDefect ε R| ≤ C/R^2) :
    |e8CompactDefect R-(-5*Real.pi^2/6)| ≤ C/R^2 := by
  have h := le_of_tendsto (e8HeatTailDefect_limit hR).abs
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, |e8HeatTailDefect ε R| ≤ C/R^2 from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hb ε hε)
  simpa only [abs_sub_comm] using h

#print axioms e8HeatCellTailTerm_nonneg
#print axioms e8HeatCellTailTerm_summable
#print axioms e8HeatTailKernel_norm_bound
#print axioms e8HeatTailKernel_integrable
#print axioms e8HeatCell_kernel_identity
#print axioms e8HeatCell_term_identity
#print axioms e8HeatCell_tsum_identity
#print axioms e8HeatCell_integral_identity
#print axioms e8HeatCell_defect_comparison
#print axioms e8HeatTailDefect_limit
#print axioms e8CompactDefect_bound_of_heatTail

end SphericalRiesz
