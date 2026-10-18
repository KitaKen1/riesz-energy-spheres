import Riesz.LocalCellQuadrature

/-!
# The actual local error identity and the L1 sixth-derivative bound

This is the derivative-integral form used by the received candidate.
It retains the original boundary-corrected nodes. In particular, it
does not replace the interior grid with a new rule in every small cell.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem quadrature_peano_error_identity {m : ℕ} (hm : 8 ≤ m) (a : Fin 6 → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    quadrature m (fun x => (∑ k : Fin 6, a k*x^k.val)+peanoPrimitive g x)-
      (∫ x in (0 : ℝ)..1, (∑ k : Fin 6, a k*x^k.val)+peanoPrimitive g x) =
        ∫ t in (0 : ℝ)..1, unitPeanoKernel m t*g t := by
  have hp : Continuous (fun x : ℝ => ∑ k : Fin 6, a k*x^k.val) := by fun_prop
  rw [quadrature_add,
    intervalIntegral.integral_add (hp.intervalIntegrable _ _) (peanoPrimitive_intervalIntegrable hg),
    quadrature_degree_five hm a]
  have h := peanoPrimitive_quadrature_error hg m
  linarith

/-- The integrand is the actual sixth derivative on the closed interval. -/
theorem quadrature_sixth_order_error_on {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 f (Set.Icc (0 : ℝ) 1)) :
    quadrature m f-(∫ x in (0 : ℝ)..1, f x) =
      ∫ t in (0 : ℝ)..1, unitPeanoKernel m t*
        iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) t := by
  let a : Fin 6 → ℝ := fun k => (k.val.factorial : ℝ)⁻¹*
    iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0
  let g : ℝ → ℝ := fun t => iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) (unitClamp t)
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hg : Continuous g :=
    continuous_unit_extension (hf.continuousOn_iteratedDerivWithin (by norm_num) hu)
  have hrepr : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      f x = (∑ k : Fin 6, a k*x^k.val)+peanoPrimitive g x :=
    fun _ hx => sixth_order_local_representation hf hx
  have hq : quadrature m f =
      quadrature m (fun x => (∑ k : Fin 6, a k*x^k.val)+peanoPrimitive g x) := by
    rw [quadrature_as_node_sum, quadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hrepr _ (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm i))
  have hi : (∫ x in (0 : ℝ)..1, f x) =
      ∫ x in (0 : ℝ)..1, (∑ k : Fin 6, a k*x^k.val)+peanoPrimitive g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hrepr x hx
  rw [hq, hi, quadrature_peano_error_identity hm a g hg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only [g]
  rw [unitClamp_eq ht]

theorem unitPeanoKernel_weighted_l1_bound {m : ℕ} (hm : 8 ≤ m) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    |∫ t in (0 : ℝ)..1, unitPeanoKernel m t*g t| ≤
      (64/(m : ℝ)^6)*(∫ t in (0 : ℝ)..1, |g t|) := by
  have hi : IntervalIntegrable (fun t => |unitPeanoKernel m t*g t|) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.mul_apply] using
      ((unitPeanoKernel_continuous m).continuousOn.mul hg).abs
  have hj : IntervalIntegrable (fun t => (64/(m : ℝ)^6)*|g t|) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.mul_def] using
      (continuousOn_const (c := (64/(m : ℝ)^6))).mul hg.abs
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |unitPeanoKernel m t*g t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, (64/(m : ℝ)^6)*|g t| :=
      intervalIntegral.integral_mono_on (by norm_num) hi hj (by
        intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (unitPeanoKernel_bound hm ht) (abs_nonneg _))
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem quadrature_sixth_order_l1_bound_on {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 f (Set.Icc (0 : ℝ) 1)) :
    |quadrature m f-(∫ x in (0 : ℝ)..1, f x)| ≤ (64/(m : ℝ)^6)*
      (∫ t in (0 : ℝ)..1, |iteratedDerivWithin 6 f (Set.Icc (0 : ℝ) 1) t|) := by
  rw [quadrature_sixth_order_error_on hm hf]
  exact unitPeanoKernel_weighted_l1_bound hm _
    (hf.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc (by norm_num)))

theorem quadrature_cell_sixth_order_l1_bound_on {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (a w : ℝ) (hw : 0 < w) (hf : ContDiffOn ℝ 6 f (Set.Icc a (a+w))) :
    |w*quadrature m (fun t => f (a+w*t))-(∫ x in a..a+w, f x)| ≤
      (64/(m : ℝ)^6)*w^6*(∫ x in a..a+w, |iteratedDerivWithin 6 f (Set.Icc a (a+w)) x|) := by
  have hg : ContDiffOn ℝ 6 (fun t => f (a+w*t)) (Set.Icc (0 : ℝ) 1) :=
    hf.comp (by fun_prop) (fun _ ht => affine_mem_cell a w hw ht)
  have h := quadrature_sixth_order_l1_bound_on hm hg
  have hd : (∫ t in (0 : ℝ)..1,
      |iteratedDerivWithin 6 (fun u => f (a+w*u)) (Set.Icc (0 : ℝ) 1) t|) =
      w^6*(∫ t in (0 : ℝ)..1, |iteratedDerivWithin 6 f (Set.Icc a (a+w)) (a+w*t)|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only
    rw [iteratedDerivWithin_affine_cell a w hw hf ht, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ w^6)]
  have hi : (∫ x in a..a+w, f x) = w*(∫ t in (0 : ℝ)..1, f (a+w*t)) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f w a
  have hj : (∫ x in a..a+w, |iteratedDerivWithin 6 f (Set.Icc a (a+w)) x|) =
      w*(∫ t in (0 : ℝ)..1, |iteratedDerivWithin 6 f (Set.Icc a (a+w)) (a+w*t)|) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
        (fun x => |iteratedDerivWithin 6 f (Set.Icc a (a+w)) x|) w a
  rw [hd] at h
  rw [hi, hj, ← mul_sub, abs_mul, abs_of_pos hw]
  calc
    _ ≤ w*((64/(m : ℝ)^6)*(w^6*(∫ t in (0 : ℝ)..1,
        |iteratedDerivWithin 6 f (Set.Icc a (a+w)) (a+w*t)|))) :=
      mul_le_mul_of_nonneg_left h hw.le
    _ = _ := by ring

#print axioms quadrature_sixth_order_error_on
#print axioms quadrature_sixth_order_l1_bound_on
#print axioms quadrature_cell_sixth_order_l1_bound_on

end SphericalRiesz.Boundary
