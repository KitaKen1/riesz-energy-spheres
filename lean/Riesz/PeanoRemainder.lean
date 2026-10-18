import Riesz.PeanoInterior
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Taylor

/-! The Peano representation uses ordinary integrals and Fubini on a compact rectangle. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def peanoPrimitive (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, positiveFifth (x-t)*g t/120

private theorem continuous_peanoIntegrand {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (fun p : ℝ × ℝ => positiveFifth (p.1-p.2)*g p.2/120) := by
  unfold positiveFifth
  fun_prop

private theorem integrable_peanoRectangle {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun p : ℝ × ℝ => positiveFifth (p.1-p.2)*g p.2/120)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact ((continuous_peanoIntegrand hg).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem peanoPrimitive_intervalIntegrable {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (peanoPrimitive g) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change Integrable (fun x => ∫ t in (0 : ℝ)..1, positiveFifth (x-t)*g t/120)
    (volume.restrict (Set.Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    using (integrable_peanoRectangle hg).integral_prod_left

theorem quadrature_intervalIntegral (m : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ i : NodeIndex m, IntervalIntegrable (F (ruleNode m i)) volume 0 1) :
    quadrature m (fun x => ∫ t in (0 : ℝ)..1, F x t) =
      ∫ t in (0 : ℝ)..1, quadrature m (fun x => F x t) := by
  simp_rw [quadrature_as_node_sum]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum (fun i _ => hF i)]

theorem peanoPrimitive_integral {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x in (0 : ℝ)..1, peanoPrimitive g x) =
      ∫ t in (0 : ℝ)..1, ((1-t)^6/6)*g t/120 := by
  have hswap : (∫ x in (0 : ℝ)..1, peanoPrimitive g x) =
      ∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, positiveFifth (x-t)*g t/120 := by
    simp only [peanoPrimitive, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_integral_swap (integrable_peanoRectangle hg)
  rw [hswap]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_positiveFifth ht]

theorem peanoPrimitive_quadrature_error {g : ℝ → ℝ} (hg : Continuous g) (m : ℕ) :
    quadrature m (peanoPrimitive g) - (∫ x in (0 : ℝ)..1, peanoPrimitive g x) =
      ∫ t in (0 : ℝ)..1, unitPeanoKernel m t*g t := by
  have hc (x : ℝ) : Continuous (fun t => positiveFifth (x-t)*g t/120) := by
    unfold positiveFifth
    fun_prop
  have hq := quadrature_intervalIntegral m
    (fun x t => positiveFifth (x-t)*g t/120) (fun i => (hc _).intervalIntegrable _ _)
  change quadrature m (peanoPrimitive g) = _ at hq
  have hscalar (t : ℝ) : quadrature m (fun x => positiveFifth (x-t)*g t/120) =
      quadrature m (fun x => positiveFifth (x-t))*g t/120 := by
    calc
      _ = quadrature m (fun x => (g t/120)*positiveFifth (x-t)) := by
        congr 1; funext x; ring
      _ = _ := by rw [quadrature_mul_const]; ring
  simp_rw [hscalar] at hq
  have hcq : Continuous (fun t => quadrature m (fun x => positiveFifth (x-t))*g t/120) := by
    unfold quadrature positiveFifth
    fun_prop
  have hci : Continuous (fun t : ℝ => ((1-t)^6/6)*g t/120) := by fun_prop
  rw [hq, peanoPrimitive_integral hg,
    ← intervalIntegral.integral_sub (hcq.intervalIntegrable _ _) (hci.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  unfold unitPeanoKernel
  ring

/-- Exact polynomial cancellation and an actual Fubini-derived error identity. -/
theorem quadrature_peano_error_bound {m : ℕ} (hm : 8 ≤ m) (a : Fin 6 → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M) :
    |quadrature m (fun x => (∑ k : Fin 6, a k*x^k.val) + peanoPrimitive g x) -
      (∫ x in (0 : ℝ)..1, (∑ k : Fin 6, a k*x^k.val) + peanoPrimitive g x)| ≤
        (64/(m : ℝ)^6)*M := by
  have hp : Continuous (fun x : ℝ => ∑ k : Fin 6, a k*x^k.val) := by fun_prop
  rw [quadrature_add,
    intervalIntegral.integral_add (hp.intervalIntegrable _ _) (peanoPrimitive_intervalIntegrable hg),
    quadrature_degree_five hm a]
  rw [show ((∫ x in (0 : ℝ)..1, ∑ k : Fin 6, a k*x^k.val) + quadrature m (peanoPrimitive g)) -
      ((∫ x in (0 : ℝ)..1, ∑ k : Fin 6, a k*x^k.val) + ∫ x in (0 : ℝ)..1, peanoPrimitive g x) =
      quadrature m (peanoPrimitive g) - ∫ x in (0 : ℝ)..1, peanoPrimitive g x by ring]
  rw [peanoPrimitive_quadrature_error hg]
  exact unitPeanoKernel_weighted_integral_bound hm g M hM

#print axioms peanoPrimitive_intervalIntegrable
#print axioms peanoPrimitive_integral
#print axioms peanoPrimitive_quadrature_error
#print axioms quadrature_peano_error_bound

end SphericalRiesz.Boundary
