import Riesz.SmoothQuadrature

/-!
# Local sixth-order quadrature

Only smoothness on the closed unit interval is required. We extend the
continuous highest derivative by clamping its argument to the interval;
there is no need to construct a globally C⁶ extension of the function.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def unitClamp (x : ℝ) : ℝ := max 0 (min x 1)

theorem unitClamp_mem (x : ℝ) : unitClamp x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : unitClamp x = x := by
  simp only [unitClamp, min_eq_left hx.2, max_eq_right hx.1]

theorem continuous_unitClamp : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

theorem continuous_unit_extension {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    Continuous (fun x => g (unitClamp x)) :=
  hg.comp_continuous continuous_unitClamp unitClamp_mem

theorem iteratedDerivWithin_subset_interval {f : ℝ → ℝ} {s t : Set ℝ}
    (hst : s ⊆ t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    {n : ℕ} (hf : ContDiffOn ℝ n f t) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n f t x := by
  simp only [iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [iteratedFDerivWithin_subset hst hs ht hf hx]

theorem taylor_unit_five (f : ℝ → ℝ) (x : ℝ) :
    taylorWithinEval f 5 (Set.Icc (0 : ℝ) 1) 0 x =
      ∑ k : Fin 6, ((k.val.factorial : ℝ)⁻¹ *
        iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0)*x^k.val := by
  rw [taylor_within_apply]
  simp only [sub_zero, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sixth_order_local_representation {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 f (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f x = (∑ k : Fin 6, ((k.val.factorial : ℝ)⁻¹ *
      iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0)*x^k.val) +
        peanoPrimitive (fun t =>
          iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) (unitClamp t)) x := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hg : Continuous (fun t =>
      iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) (unitClamp t)) :=
    continuous_unit_extension (hf.continuousOn_iteratedDerivWithin (by norm_num) hu)
  by_cases hx0 : x = 0
  · subst x
    rw [← taylor_unit_five f 0, taylorWithinEval_self,
      peanoPrimitive_eq_initial_integral hg hx]
    simp
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc (Ne.symm hx0)
  have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hx.1]
    intro t ht
    exact ⟨ht.1, ht.2.trans hx.2⟩
  have hw (j : ℕ) (hj : j ≤ 6) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) x) :
      iteratedDerivWithin j f (Set.uIcc (0 : ℝ) x) t =
        iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) t :=
    iteratedDerivWithin_subset_interval hsub hs hu (hf.of_le (by exact_mod_cast hj)) ht
  have hp : taylorWithinEval f 5 (Set.uIcc (0 : ℝ) x) 0 x =
      taylorWithinEval f 5 (Set.Icc (0 : ℝ) 1) 0 x := by
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hj6 : j ≤ 6 := by simp only [Finset.mem_range] at hj; omega
    rw [hw j hj6 0 (by rw [Set.uIcc_of_le hx.1]; exact ⟨le_rfl, hx.1⟩)]
  have hi : (∫ t in (0 : ℝ)..x,
      ((x-t)^5/(Nat.factorial 5 : ℝ)) • iteratedDerivWithin 6 f (Set.uIcc (0 : ℝ) x) t) =
      peanoPrimitive (fun t =>
        iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) (unitClamp t)) x := by
    rw [peanoPrimitive_eq_initial_integral hg hx]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hw 6 (by omega) t ht, unitClamp_eq (hsub ht)]
    norm_num [smul_eq_mul]
    ring
  have h := taylor_integral_remainder (n := 5) (x₀ := (0 : ℝ)) (x := x) (hf.mono hsub)
  rw [hp, taylor_unit_five f x, hi] at h
  linarith

/-- Local smoothness includes one-sided derivatives at the endpoints. -/
theorem quadrature_sixth_order_bound_on {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 f (Set.Icc (0 : ℝ) 1)) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) t| ≤ M) :
    |quadrature m f - ∫ x in (0 : ℝ)..1, f x| ≤ (64/(m : ℝ)^6)*M := by
  let a : Fin 6 → ℝ := fun k => (k.val.factorial : ℝ)⁻¹ *
    iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0
  let g : ℝ → ℝ := fun t => iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) (unitClamp t)
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hg : Continuous g :=
    continuous_unit_extension (hf.continuousOn_iteratedDerivWithin (by norm_num) hu)
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M := by
    intro t ht
    dsimp only [g]
    rw [unitClamp_eq ht]
    exact hM t ht
  have hrepr : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      f x = (∑ k : Fin 6, a k*x^k.val) + peanoPrimitive g x :=
    fun _ hx => sixth_order_local_representation hf hx
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
  exact quadrature_peano_error_bound hm a g hg M hb

#print axioms sixth_order_local_representation
#print axioms quadrature_sixth_order_bound_on

end SphericalRiesz.Boundary
