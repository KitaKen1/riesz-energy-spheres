import Riesz.BoundaryTwelveLocalError

/-! Actual local error identity and derivative-integral form at order twelve. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz.Boundary

theorem twelveQuadrature_peano_error_identity {m : ℕ} (hm : 74 ≤ m) (a : Fin 12 → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    twelveQuadrature m (fun x => (∑ k : Fin 12, a k*x^k.val)+twelvePeanoPrimitive g x)-
      (∫ x in (0 : ℝ)..1, (∑ k : Fin 12, a k*x^k.val)+twelvePeanoPrimitive g x) =
        ∫ t in (0 : ℝ)..1, twelveUnitPeanoKernel m t*g t := by
  have hp : Continuous (fun x : ℝ => ∑ k : Fin 12, a k*x^k.val) := by fun_prop
  rw [twelveQuadrature_add,
    intervalIntegral.integral_add (hp.intervalIntegrable _ _) (twelvePeanoPrimitive_intervalIntegrable hg),
    twelveQuadrature_degree_eleven hm a]
  have h := twelvePeanoPrimitive_quadrature_error hg m
  linarith

/-- The integrand is the actual twelfth derivative on the closed interval. -/
theorem twelveQuadrature_twelfth_order_error_on {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 12 f (Set.Icc (0 : ℝ) 1)) :
    twelveQuadrature m f-(∫ x in (0 : ℝ)..1, f x) =
      ∫ t in (0 : ℝ)..1, twelveUnitPeanoKernel m t*
        iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) t := by
  let a : Fin 12 → ℝ := fun k => (k.val.factorial : ℝ)⁻¹*
    iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0
  let g : ℝ → ℝ := fun t => iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) (unitClamp t)
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hg : Continuous g :=
    continuous_unit_extension (hf.continuousOn_iteratedDerivWithin (by norm_num) hu)
  have hrepr : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      f x = (∑ k : Fin 12, a k*x^k.val)+twelvePeanoPrimitive g x :=
    fun _ hx => twelfth_order_local_representation hf hx
  have hq : twelveQuadrature m f =
      twelveQuadrature m (fun x => (∑ k : Fin 12, a k*x^k.val)+twelvePeanoPrimitive g x) := by
    rw [twelveQuadrature_as_node_sum, twelveQuadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hrepr _ (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm i))
  have hi : (∫ x in (0 : ℝ)..1, f x) =
      ∫ x in (0 : ℝ)..1, (∑ k : Fin 12, a k*x^k.val)+twelvePeanoPrimitive g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hrepr x hx
  rw [hq, hi, twelveQuadrature_peano_error_identity hm a g hg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only [g]
  rw [unitClamp_eq ht]

theorem twelveUnitPeanoKernel_weighted_l1_bound {m : ℕ} (hm : 74 ≤ m) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    |∫ t in (0 : ℝ)..1, twelveUnitPeanoKernel m t*g t| ≤
      ((10^24)/(m : ℝ)^12)*(∫ t in (0 : ℝ)..1, |g t|) := by
  have hi : IntervalIntegrable (fun t => |twelveUnitPeanoKernel m t*g t|) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.mul_apply] using
      ((twelveUnitPeanoKernel_continuous m).continuousOn.mul hg).abs
  have hj : IntervalIntegrable (fun t => ((10^24)/(m : ℝ)^12)*|g t|) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.mul_def] using
      (continuousOn_const (c := ((10^24)/(m : ℝ)^12))).mul hg.abs
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |twelveUnitPeanoKernel m t*g t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, ((10^24)/(m : ℝ)^12)*|g t| :=
      intervalIntegral.integral_mono_on (by norm_num) hi hj (by
        intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (twelveUnitPeanoKernel_bound hm ht) (abs_nonneg _))
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem twelveQuadrature_twelfth_order_l1_bound_on {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 12 f (Set.Icc (0 : ℝ) 1)) :
    |twelveQuadrature m f-(∫ x in (0 : ℝ)..1, f x)| ≤ ((10^24)/(m : ℝ)^12)*
      (∫ t in (0 : ℝ)..1, |iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) t|) := by
  rw [twelveQuadrature_twelfth_order_error_on hm hf]
  exact twelveUnitPeanoKernel_weighted_l1_bound hm _
    (hf.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc (by norm_num)))

theorem twelveQuadrature_cell_twelfth_order_l1_bound_on {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ}
    (a w : ℝ) (hw : 0 < w) (hf : ContDiffOn ℝ 12 f (Set.Icc a (a+w))) :
    |w*twelveQuadrature m (fun t => f (a+w*t))-(∫ x in a..a+w, f x)| ≤
      ((10^24)/(m : ℝ)^12)*w^12*(∫ x in a..a+w, |iteratedDerivWithin 12 f (Set.Icc a (a+w)) x|) := by
  have hg : ContDiffOn ℝ 12 (fun t => f (a+w*t)) (Set.Icc (0 : ℝ) 1) :=
    hf.comp (by fun_prop) (fun _ ht => affine_mem_cell a w hw ht)
  have h := twelveQuadrature_twelfth_order_l1_bound_on hm hg
  have hd : (∫ t in (0 : ℝ)..1,
      |iteratedDerivWithin 12 (fun u => f (a+w*u)) (Set.Icc (0 : ℝ) 1) t|) =
      w^12*(∫ t in (0 : ℝ)..1, |iteratedDerivWithin 12 f (Set.Icc a (a+w)) (a+w*t)|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only
    rw [iteratedDerivWithin_affine_cell a w hw hf ht, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ w^12)]
  have hi : (∫ x in a..a+w, f x) = w*(∫ t in (0 : ℝ)..1, f (a+w*t)) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f w a
  have hj : (∫ x in a..a+w, |iteratedDerivWithin 12 f (Set.Icc a (a+w)) x|) =
      w*(∫ t in (0 : ℝ)..1, |iteratedDerivWithin 12 f (Set.Icc a (a+w)) (a+w*t)|) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
        (fun x => |iteratedDerivWithin 12 f (Set.Icc a (a+w)) x|) w a
  rw [hd] at h
  rw [hi, hj, ← mul_sub, abs_mul, abs_of_pos hw]
  calc
    _ ≤ w*(((10^24)/(m : ℝ)^12)*(w^12*(∫ t in (0 : ℝ)..1,
        |iteratedDerivWithin 12 f (Set.Icc a (a+w)) (a+w*t)|))) :=
      mul_le_mul_of_nonneg_left h hw.le
    _ = _ := by ring


end SphericalRiesz.Boundary
