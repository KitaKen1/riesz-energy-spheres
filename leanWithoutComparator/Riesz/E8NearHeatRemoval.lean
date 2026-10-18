import Riesz.E8CompactCell
import Riesz.E8CoordinateHeat
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fixed-radius removal of the Gaussian from the actual compact defect. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

def e8NearHeatRemovalKernel (ε R : ℝ) (y : Fin 8 → ℝ) : ℝ :=
  nearObliqueRieszFour 8 e8Map R 0 y * (1-e8CoordinateGaussian ε y)

def e8NearHeatRemovalTerm (ε R : ℝ) (z : Fin 8 → ℤ) : ℝ :=
  e8CompactTerm R z * (1-e8CoordinateGaussian ε (fun i => (z i : ℝ)))

def e8NearHeatRemoval (ε R : ℝ) : ℝ :=
  (∑' z : Fin 8 → ℤ, e8NearHeatRemovalTerm ε R z) -
    ∫ y : Fin 8 → ℝ, e8NearHeatRemovalKernel ε R y

theorem e8NearHeatRemovalKernel_aestronglyMeasurable {R : ℝ} (hR : 0 < R) (ε : ℝ) :
    AEStronglyMeasurable (e8NearHeatRemovalKernel ε R) :=
  (e8Near_integrable R hR 0).aestronglyMeasurable.mul
    ((continuous_const.sub (e8CoordinateGaussian_continuous ε)).aestronglyMeasurable)

theorem e8NearHeatRemovalKernel_norm_bound {ε : ℝ} (hε : 0 ≤ ε) (R : ℝ) (y : Fin 8 → ℝ) :
    ‖e8NearHeatRemovalKernel ε R y‖ ≤ nearObliqueRieszFour 8 e8Map R 0 y := by
  have hg := e8CoordinateGaussian_bounds hε y
  have hn := e8Near_nonneg R 0 y
  unfold e8NearHeatRemovalKernel
  rw [Real.norm_of_nonneg (mul_nonneg hn (by linarith))]
  apply mul_le_of_le_one_right hn
  linarith

theorem e8NearHeatRemovalKernel_integrable {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R) :
    Integrable (e8NearHeatRemovalKernel ε R) := by
  apply MeasureTheory.Integrable.mono (e8Near_integrable R hR 0)
    (e8NearHeatRemovalKernel_aestronglyMeasurable hR ε)
  apply Eventually.of_forall
  intro y
  rw [Real.norm_of_nonneg (e8Near_nonneg R 0 y)]
  exact e8NearHeatRemovalKernel_norm_bound hε R y

theorem e8NearHeatRemovalTerm_summable {R : ℝ} (hR : 0 < R) (ε : ℝ) :
    Summable (e8NearHeatRemovalTerm ε R) := by
  obtain ⟨q, hq⟩ := exists_nat_ge (2*R)
  apply summable_of_ne_finset_zero (s := centeredIntegerBox 8 q)
  intro z hz
  rw [e8NearHeatRemovalTerm, e8CompactTerm_zero_outside hR q hq z hz, zero_mul]

theorem e8NearHeatRemovalTerm_tsum_finite {R : ℝ} (hR : 0 < R) (ε : ℝ)
    (q : ℕ) (hq : 2*R ≤ q) :
    (∑' z : Fin 8 → ℤ, e8NearHeatRemovalTerm ε R z) =
      ∑ z ∈ centeredIntegerBox 8 q, e8NearHeatRemovalTerm ε R z := by
  apply tsum_eq_sum
  intro z hz
  rw [e8NearHeatRemovalTerm, e8CompactTerm_zero_outside hR q hq z hz, zero_mul]

theorem e8NearHeatRemovalTerm_tsum_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∑' z : Fin 8 → ℤ, e8NearHeatRemovalTerm ε R z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  obtain ⟨q, hq⟩ := exists_nat_ge (2*R)
  have hc : Continuous (fun ε : ℝ => ∑ z ∈ centeredIntegerBox 8 q,
      e8NearHeatRemovalTerm ε R z) := by
    unfold e8NearHeatRemovalTerm e8CoordinateGaussian
    fun_prop
  have ht : Tendsto (fun ε : ℝ => ∑ z ∈ centeredIntegerBox 8 q,
      e8NearHeatRemovalTerm ε R z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [e8NearHeatRemovalTerm, e8CoordinateGaussian] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  exact Eventually.of_forall (fun ε => (e8NearHeatRemovalTerm_tsum_finite hR ε q hq).symm)

theorem e8NearHeatRemovalKernel_integral_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫ y : Fin 8 → ℝ, e8NearHeatRemovalKernel ε R y)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := (volume : Measure (Fin 8 → ℝ)))
    (F := fun ε y => e8NearHeatRemovalKernel ε R y) (f := fun _ => (0 : ℝ))
    (nearObliqueRieszFour 8 e8Map R 0)
    (Eventually.of_forall (e8NearHeatRemovalKernel_aestronglyMeasurable hR)) ?_
    (e8Near_integrable R hR 0) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall (e8NearHeatRemovalKernel_norm_bound hε.le R)
  · apply Eventually.of_forall
    intro y
    have hc : Continuous (fun ε : ℝ => e8NearHeatRemovalKernel ε R y) := by
      unfold e8NearHeatRemovalKernel e8CoordinateGaussian
      fun_prop
    simpa [e8NearHeatRemovalKernel, e8CoordinateGaussian] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem e8NearHeatRemoval_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => e8NearHeatRemoval ε R) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [sub_zero, e8NearHeatRemoval] using
    (e8NearHeatRemovalTerm_tsum_limit hR).sub (e8NearHeatRemovalKernel_integral_limit hR)

#print axioms e8NearHeatRemovalKernel_aestronglyMeasurable
#print axioms e8NearHeatRemovalKernel_norm_bound
#print axioms e8NearHeatRemovalKernel_integrable
#print axioms e8NearHeatRemovalTerm_summable
#print axioms e8NearHeatRemovalTerm_tsum_finite
#print axioms e8NearHeatRemovalTerm_tsum_limit
#print axioms e8NearHeatRemovalKernel_integral_limit
#print axioms e8NearHeatRemoval_limit

end SphericalRiesz
