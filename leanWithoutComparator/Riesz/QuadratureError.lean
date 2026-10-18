import Riesz.Quadrature

/-!
# Stability and polynomial cancellation

Positive equal weights give operator norm one on the uniform norm.  Exactness
then removes a polynomial before the error is estimated.  This file does not
claim the required uniform sixth-order Peano-kernel bound.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz.Boundary

theorem quadrature_const {m : ℕ} (hm : 8 ≤ m) (c : ℝ) :
    quadrature m (fun _ => c) = c := by
  have h : quadrature m (fun _ => (1 : ℝ)) = 1 := by
    simpa using quadrature_monomial hm (0 : Fin 6)
  simpa using (quadrature_mul_const m c (fun _ => 1)).trans (by rw [h, mul_one])

theorem quadrature_sub (m : ℕ) (f g : ℝ → ℝ) :
    quadrature m (fun x => f x-g x) = quadrature m f-quadrature m g := by
  simp only [quadrature, Finset.sum_sub_distrib]
  ring

theorem quadrature_mono {m : ℕ} (hm : 8 ≤ m) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ g x) : quadrature m f ≤ quadrature m g := by
  rw [quadrature_as_node_sum, quadrature_as_node_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  exact h _ (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm i))

theorem quadrature_abs_le {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) : |quadrature m f| ≤ M := by
  apply abs_le.mpr
  constructor
  · have hl := quadrature_mono hm (f := fun _ => -M) (g := f)
      (fun x hx => (abs_le.mp (h x hx)).1)
    simpa only [quadrature_const hm] using hl
  · have hu := quadrature_mono hm (f := f) (g := fun _ => M)
      (fun x hx => (abs_le.mp (h x hx)).2)
    simpa only [quadrature_const hm] using hu

/-- Any known polynomial approximation can be used directly, without constructing Taylor coefficients. -/
theorem quadrature_residual_bound {m : ℕ} (hm : 8 ≤ m) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) (a : Fin 6 → ℝ) (M : ℝ)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - ∑ k : Fin 6, a k*x^k.val| ≤ M) :
    |quadrature m f - ∫ x in (0 : ℝ)..1, f x| ≤ 2*M := by
  let p : ℝ → ℝ := fun x => ∑ k : Fin 6, a k*x^k.val
  have hp : Continuous p := by unfold p; fun_prop
  have hq : |quadrature m (fun x => f x-p x)| ≤ M := quadrature_abs_le hm h
  have hi : |∫ x in (0 : ℝ)..1, f x-p x| ≤ M := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := fun x => f x-p x) (C := M) (by
        intro x hx
        rw [Real.norm_eq_abs]
        exact h x ⟨by simpa using hx.1.le, by simpa using hx.2⟩)
    simpa using hi
  have heq : quadrature m f - (∫ x in (0 : ℝ)..1, f x) =
      quadrature m (fun x => f x-p x) - (∫ x in (0 : ℝ)..1, f x-p x) := by
    rw [quadrature_sub, intervalIntegral.integral_sub hf (hp.intervalIntegrable _ _)]
    rw [show quadrature m p = ∫ x in (0 : ℝ)..1, p x from quadrature_degree_five hm a]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

#print axioms quadrature_abs_le
#print axioms quadrature_residual_bound

end SphericalRiesz.Boundary
