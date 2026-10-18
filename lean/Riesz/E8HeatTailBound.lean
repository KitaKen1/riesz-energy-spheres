import Riesz.E8WholeAnnulus
import Riesz.E8HeatTailLimit

/-!
# The actual E8 heat tail is uniformly O(R^-2)

Finite annuli telescope to the difference of two actual tails. The outer
tail tends to zero by dominated convergence. No infinite annular series
exchange, and no uniform-tail hypothesis, is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem e8HeatAnnulus_eq_kernel (ε : ℝ) {r : ℝ} (hr : 0 < r) (y : Fin 8 → ℝ) :
    e8HeatAnnulus ε r 0 y = e8CoordinateHeatKernel ε y * unitAnnularCutoff 8 (r⁻¹ • y) := by
  rw [e8HeatAnnulus, e8ScaledDampedAnnulus_eq_heat ε r hr]
  simp only [sub_zero, e8CoordinateHeatKernel]
  ring

theorem e8HeatAnnulus_eq_tail_sub (ε : ℝ) {r : ℝ} (hr : 0 < r) (y : Fin 8 → ℝ) :
    e8HeatAnnulus ε r 0 y = e8HeatTailKernel ε (r/2) y-e8HeatTailKernel ε r y := by
  rw [e8HeatAnnulus_eq_kernel ε hr, unitAnnularCutoff, innerUnitBump_eq_outer_scaled]
  have harg : (2:ℝ) • (r⁻¹ • y) = (r/2)⁻¹ • y := by
    rw [smul_smul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [harg, e8HeatTailKernel, e8HeatTailKernel]
  ring

theorem e8HeatAnnulus_integrable {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    Integrable (e8HeatAnnulus ε r 0) := by
  have heq : e8HeatAnnulus ε r 0 =
      fun y => e8HeatTailKernel ε (r/2) y-e8HeatTailKernel ε r y :=
    funext (e8HeatAnnulus_eq_tail_sub ε hr)
  rw [heq]
  exact (e8HeatTailKernel_integrable hε _).sub (e8HeatTailKernel_integrable hε _)

theorem e8AnnularDefect_eq_tail_sub {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    e8AnnularDefect (ε*r^2) r = e8HeatTailDefect ε (r/2)-e8HeatTailDefect ε r := by
  change ((∑' z : Fin 8 → ℤ, e8HeatAnnulus ε r 0 (fun i => (z i : ℝ))) -
    ∫ y : Fin 8 → ℝ, e8HeatAnnulus ε r 0 y) = _
  simp_rw [e8HeatAnnulus_eq_tail_sub ε hr, e8HeatTailKernel_integer]
  rw [(e8HeatCellTailTerm_summable hε (r/2)).tsum_sub (e8HeatCellTailTerm_summable hε r),
    integral_sub (e8HeatTailKernel_integrable hε (r/2)) (e8HeatTailKernel_integrable hε r)]
  unfold e8HeatTailDefect
  ring

theorem e8AnnularDefect_partition_sum {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      e8AnnularDefect (ε*((2:ℝ)^(k+1)*R)^2) ((2:ℝ)^(k+1)*R)) =
        e8HeatTailDefect ε R-e8HeatTailDefect ε ((2:ℝ)^n*R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, e8AnnularDefect_eq_tail_sub hε (by positivity)]
    have hhalf : ((2:ℝ)^(n+1)*R)/2 = (2:ℝ)^n*R := by rw [pow_succ]; ring
    rw [hhalf]
    ring

theorem e8AnnularDefect_partition_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R → ∀ n : ℕ,
      |∑ k ∈ Finset.range n,
        e8AnnularDefect (ε*((2:ℝ)^(k+1)*R)^2) ((2:ℝ)^(k+1)*R)| ≤ C/R^2 := by
  obtain ⟨C, hC, hb⟩ := e8AnnularDefect_uniform_bound
  refine ⟨(4/3:ℝ)*C, by positivity, ?_⟩
  intro ε hε R hR n
  have hR0 : 0 < R := by linarith
  let e (k : ℕ) := e8AnnularDefect (ε*((2:ℝ)^(k+1)*R)^2) ((2:ℝ)^(k+1)*R)
  have he (k : ℕ) : |e k| ≤ (C/R^2)*(1/4:ℝ)^k := by
    have h2 : 0 < (2:ℝ)^k := by positivity
    have hpow : R ≤ (2:ℝ)^(k+1)*R := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k+1)]
    have hg : (2:ℝ)^k*R ≤ (2:ℝ)^(k+1)*R := by rw [pow_succ]; nlinarith
    have hp : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    calc
      _ ≤ C/(((2:ℝ)^(k+1)*R)^2) :=
        hb _ (mul_nonneg hε (sq_nonneg _)) _ (hR.trans hpow)
      _ ≤ C/(((2:ℝ)^k*R)^2) := by gcongr
      _ = (C/R^2)*(1/4:ℝ)^k := by
        simp only [mul_pow, div_pow, one_pow, hp]
        field_simp [hR0.ne', h2.ne']
  calc
    _ ≤ ∑ k ∈ Finset.range n, |e k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (C/R^2)*(1/4:ℝ)^k := Finset.sum_le_sum (fun k _ => he k)
    _ = (C/R^2)*(∑ k ∈ Finset.range n, (1/4:ℝ)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/R^2)*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left (dyadic_quarter_sum_le n) (by positivity)
    _ = _ := by ring

/-- The previously explicit uniform-tail input is now discharged for the actual E8 objects. -/
theorem e8HeatTailDefect_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 1 ≤ R →
      |e8HeatTailDefect ε R| ≤ C/R^2 := by
  obtain ⟨C, hC, hb⟩ := e8AnnularDefect_partition_bound
  refine ⟨C, hC, ?_⟩
  intro ε hε R hR
  have hR0 : 0 < R := by linarith
  have hg : Tendsto (fun n : ℕ => (2:ℝ)^n*R) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).atTop_mul_const hR0
  have ht := (e8HeatTailDefect_radius_limit hε).comp hg
  have hc : Tendsto (fun _ : ℕ => e8HeatTailDefect ε R) atTop (𝓝 (e8HeatTailDefect ε R)) :=
    tendsto_const_nhds
  have hl := (hc.sub ht).abs
  have h := le_of_tendsto hl (show ∀ᶠ n : ℕ in atTop,
      |e8HeatTailDefect ε R-e8HeatTailDefect ε ((2:ℝ)^n*R)| ≤ C/R^2 from by
    apply Eventually.of_forall
    intro n
    rw [← e8AnnularDefect_partition_sum hε hR0 n]
    exact hb ε hε.le R hR n)
  simpa only [sub_zero] using h

#print axioms e8HeatAnnulus_eq_kernel
#print axioms e8HeatAnnulus_eq_tail_sub
#print axioms e8HeatAnnulus_integrable
#print axioms e8AnnularDefect_eq_tail_sub
#print axioms e8AnnularDefect_partition_sum
#print axioms e8AnnularDefect_partition_bound
#print axioms e8HeatTailDefect_uniform_bound
end SphericalRiesz
