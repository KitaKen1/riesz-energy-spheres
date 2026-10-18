import Riesz.PeanoRemainder

/-!
# Sixth-order quadrature error for C⁶ functions

The existing Taylor integral remainder is used only at order five. Its
derivatives on the interval are identified with global derivatives, and
the truncated-power representation is fed to the checked Peano estimate.
No general Euler–Maclaurin theorem is developed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem taylor_global_five (f : ℝ → ℝ) (x : ℝ) :
    taylorWithinEval f 5 Set.univ 0 x =
      ∑ k : Fin 6, ((k.val.factorial : ℝ)⁻¹ * iteratedDeriv k.val f 0)*x^k.val := by
  rw [taylor_within_apply]
  simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem peanoPrimitive_eq_initial_integral {g : ℝ → ℝ} (hg : Continuous g)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    peanoPrimitive g x = ∫ t in (0 : ℝ)..x, (x-t)^5*g t/120 := by
  have hc : Continuous (fun t => positiveFifth (x-t)*g t/120) := by
    unfold positiveFifth
    fun_prop
  have hzero : (∫ t in x..(1 : ℝ), positiveFifth (x-t)*g t/120) = 0 := by
    calc
      _ = ∫ _t in x..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hx.2] at ht
        unfold positiveFifth
        rw [max_eq_right (sub_nonpos.mpr ht.1)]
        simp
      _ = 0 := by simp
  unfold peanoPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x 1), hzero, add_zero]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le hx.1] at ht
  unfold positiveFifth
  rw [max_eq_left (sub_nonneg.mpr ht.2)]

/-- Taylor at the known endpoint zero supplies the required polynomial and Peano primitive. -/
theorem sixth_order_representation {f : ℝ → ℝ} (hf : ContDiff ℝ 6 f)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f x = (∑ k : Fin 6, ((k.val.factorial : ℝ)⁻¹ * iteratedDeriv k.val f 0)*x^k.val) +
      peanoPrimitive (iteratedDeriv 6 f) x := by
  have hg : Continuous (iteratedDeriv 6 f) := hf.continuous_iteratedDeriv 6 (by norm_num)
  by_cases hx0 : x = 0
  · subst x
    rw [← taylor_global_five f 0, taylorWithinEval_self,
      peanoPrimitive_eq_initial_integral hg hx]
    simp
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc (Ne.symm hx0)
  have hw (j : ℕ) (hj : j ≤ 6) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) x) :
      iteratedDerivWithin j f (Set.uIcc (0 : ℝ) x) t = iteratedDeriv j f t :=
    iteratedDerivWithin_eq_iteratedDeriv hs
      ((hf.of_le (by exact_mod_cast hj)).contDiffAt) ht
  have hp : taylorWithinEval f 5 (Set.uIcc (0 : ℝ) x) 0 x =
      taylorWithinEval f 5 Set.univ 0 x := by
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hj6 : j ≤ 6 := by simp only [Finset.mem_range] at hj; omega
    rw [hw j hj6 0 (by rw [Set.uIcc_of_le hx.1]; exact ⟨le_rfl, hx.1⟩)]
    simp only [iteratedDerivWithin_univ]
  have hi : (∫ t in (0 : ℝ)..x,
      ((x-t)^5/(Nat.factorial 5 : ℝ)) • iteratedDerivWithin 6 f (Set.uIcc (0 : ℝ) x) t) =
      peanoPrimitive (iteratedDeriv 6 f) x := by
    rw [peanoPrimitive_eq_initial_integral hg hx]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hw 6 (by omega) t ht]
    norm_num [smul_eq_mul] <;> ring
  have h := taylor_integral_remainder (n := 5) (x₀ := (0 : ℝ)) (x := x) hf.contDiffOn
  rw [hp, taylor_global_five f x, hi] at h
  linarith

/-- Full interval, actual quadrature and integral, no postulated error representation. -/
theorem quadrature_sixth_order_bound {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 6 f) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 6 f t| ≤ M) :
    |quadrature m f - ∫ x in (0 : ℝ)..1, f x| ≤ (64/(m : ℝ)^6)*M := by
  let a : Fin 6 → ℝ := fun k => (k.val.factorial : ℝ)⁻¹ * iteratedDeriv k.val f 0
  let g : ℝ → ℝ := iteratedDeriv 6 f
  have hg : Continuous g := hf.continuous_iteratedDeriv 6 (by norm_num)
  have hrepr : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      f x = (∑ k : Fin 6, a k*x^k.val) + peanoPrimitive g x :=
    fun _ hx => sixth_order_representation hf hx
  have hq : quadrature m f =
      quadrature m (fun x => (∑ k : Fin 6, a k*x^k.val) + peanoPrimitive g x) := by
    rw [quadrature_as_node_sum, quadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hrepr _ (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm i))
  have hi : (∫ x in (0 : ℝ)..1, f x) =
      ∫ x in (0 : ℝ)..1, (∑ k : Fin 6, a k*x^k.val) + peanoPrimitive g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hrepr x hx
  rw [hq, hi]
  exact quadrature_peano_error_bound hm a g hg M hM

#print axioms sixth_order_representation
#print axioms quadrature_sixth_order_bound

end SphericalRiesz.Boundary
