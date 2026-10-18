import Riesz.LocalQuadrature

/-!
# Two-coordinate tensor quadrature

We telescope QₓQᵧ − IₓIᵧ through QₓIᵧ, using norm-one stability
and finite-sum/Fubini interchange. Only pure sixth derivatives of the
slices are bounded: no mixed twelfth derivative or differentiation
under the integral is needed. This is the two-coordinate building block.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def quadrature2 (m : ℕ) (F : ℝ → ℝ → ℝ) : ℝ :=
  quadrature m (fun x => quadrature m (F x))

def unitIntegral2 (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y

theorem quadrature2_as_node_sum (m : ℕ) (F : ℝ → ℝ → ℝ) :
    quadrature2 m F =
      (∑ i : NodeIndex m, ∑ j : NodeIndex m, F (ruleNode m i) (ruleNode m j))/(m : ℝ)^2 := by
  unfold quadrature2
  simp_rw [quadrature_as_node_sum]
  rw [← Finset.sum_div, div_div, pow_two]

private theorem integrable_unitRectangle {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      ((Set.Icc (0 : ℝ) 1).prod (Set.Icc (0 : ℝ) 1))) :
    Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem unitIntegral2_swap {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      ((Set.Icc (0 : ℝ) 1).prod (Set.Icc (0 : ℝ) 1))) :
    unitIntegral2 F = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F x y := by
  simp only [unitIntegral2, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_integral_swap (integrable_unitRectangle hF)

theorem quadrature2_sixth_order_bound_on {m : ℕ} (hm : 8 ≤ m) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F)
      ((Set.Icc (0 : ℝ) 1).prod (Set.Icc (0 : ℝ) 1)))
    (hFx : ∀ y ∈ Set.Icc (0 : ℝ) 1, ContDiffOn ℝ 6 (fun x => F x y) (Set.Icc (0 : ℝ) 1))
    (hFy : ∀ x ∈ Set.Icc (0 : ℝ) 1, ContDiffOn ℝ 6 (F x) (Set.Icc (0 : ℝ) 1))
    (Mx My : ℝ)
    (hMx : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun t => F t y) (Set.Icc (0 : ℝ) 1) x| ≤ Mx)
    (hMy : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (F x) (Set.Icc (0 : ℝ) 1) y| ≤ My) :
    |quadrature2 m F - unitIntegral2 F| ≤ (64/(m : ℝ)^6)*(Mx+My) := by
  let A : ℝ := quadrature m (fun x => ∫ y in (0 : ℝ)..1, F x y)
  have hFyint (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      IntervalIntegrable (F x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (hFy x hx).continuousOn
  have h1 : |quadrature2 m F-A| ≤ (64/(m : ℝ)^6)*My := by
    dsimp only [quadrature2, A]
    rw [← quadrature_sub]
    apply quadrature_abs_le hm
    intro x hx
    exact quadrature_sixth_order_bound_on hm (hFy x hx) My (hMy x hx)
  have hq : A = ∫ y in (0 : ℝ)..1, quadrature m (fun x => F x y) :=
    quadrature_intervalIntegral m F (fun i =>
      hFyint _ (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm i)))
  have hi : IntervalIntegrable (fun y => ∫ x in (0 : ℝ)..1, F x y) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), Function.uncurry]
      using (integrable_unitRectangle hF).integral_prod_right
  have hqint : IntervalIntegrable (fun y => quadrature m (fun x => F x y)) volume 0 1 := by
    simp only [quadrature_as_node_sum]
    apply IntervalIntegrable.div_const
    simpa only [Finset.sum_fn] using
      (IntervalIntegrable.sum (Finset.univ : Finset (NodeIndex m)) (fun i _ =>
        hFyint _ (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm i))))
  have h2 : |A-unitIntegral2 F| ≤ (64/(m : ℝ)^6)*Mx := by
    rw [hq, unitIntegral2_swap hF, ← intervalIntegral.integral_sub hqint hi]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (f := fun y => quadrature m (fun x => F x y) - ∫ x in (0 : ℝ)..1, F x y)
      (C := (64/(m : ℝ)^6)*Mx) (by
        intro y hy
        have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by simpa using hy.1.le, by simpa using hy.2⟩
        rw [Real.norm_eq_abs]
        exact quadrature_sixth_order_bound_on hm (hFx y hy') Mx (fun x hx => hMx x hx y hy'))
    simpa using h
  calc
    |quadrature2 m F-unitIntegral2 F| ≤ |quadrature2 m F-A| + |A-unitIntegral2 F| := by
      rw [show quadrature2 m F-unitIntegral2 F =
        (quadrature2 m F-A)+(A-unitIntegral2 F) by ring]
      exact abs_add_le _ _
    _ ≤ (64/(m : ℝ)^6)*My + (64/(m : ℝ)^6)*Mx := add_le_add h1 h2
    _ = (64/(m : ℝ)^6)*(Mx+My) := by ring

#print axioms unitIntegral2_swap
#print axioms quadrature2_sixth_order_bound_on

end SphericalRiesz.Boundary
