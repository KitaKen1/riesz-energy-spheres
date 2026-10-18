import Riesz.BoundaryTwelvePeano
import Riesz.LocalCellQuadrature

/-! Local twelfth-order Taylor/Fubini error for the actual positive rule.
One-sided derivatives on the closed physical cell suffice. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz.Boundary

def twelvePeanoPrimitive (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, positiveEleventh (x-t)*g t/39916800

private theorem continuous_peanoIntegrand {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (fun p : ℝ × ℝ => positiveEleventh (p.1-p.2)*g p.2/39916800) := by
  unfold positiveEleventh
  fun_prop

private theorem integrable_peanoRectangle {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun p : ℝ × ℝ => positiveEleventh (p.1-p.2)*g p.2/39916800)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact ((continuous_peanoIntegrand hg).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem twelvePeanoPrimitive_intervalIntegrable {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (twelvePeanoPrimitive g) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change Integrable (fun x => ∫ t in (0 : ℝ)..1, positiveEleventh (x-t)*g t/39916800)
    (volume.restrict (Set.Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    using (integrable_peanoRectangle hg).integral_prod_left

theorem twelveQuadrature_intervalIntegral (m : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ i : TwelveNodeIndex m, IntervalIntegrable (F (twelveRuleNode m i)) volume 0 1) :
    twelveQuadrature m (fun x => ∫ t in (0 : ℝ)..1, F x t) =
      ∫ t in (0 : ℝ)..1, twelveQuadrature m (fun x => F x t) := by
  simp_rw [twelveQuadrature_as_node_sum]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum (fun i _ => hF i)]

theorem twelvePeanoPrimitive_integral {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x in (0 : ℝ)..1, twelvePeanoPrimitive g x) =
      ∫ t in (0 : ℝ)..1, ((1-t)^12/12)*g t/39916800 := by
  have hswap : (∫ x in (0 : ℝ)..1, twelvePeanoPrimitive g x) =
      ∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, positiveEleventh (x-t)*g t/39916800 := by
    simp only [twelvePeanoPrimitive, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_integral_swap (integrable_peanoRectangle hg)
  rw [hswap]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_positiveEleventh ht]

theorem twelvePeanoPrimitive_quadrature_error {g : ℝ → ℝ} (hg : Continuous g) (m : ℕ) :
    twelveQuadrature m (twelvePeanoPrimitive g) - (∫ x in (0 : ℝ)..1, twelvePeanoPrimitive g x) =
      ∫ t in (0 : ℝ)..1, twelveUnitPeanoKernel m t*g t := by
  have hc (x : ℝ) : Continuous (fun t => positiveEleventh (x-t)*g t/39916800) := by
    unfold positiveEleventh
    fun_prop
  have hq := twelveQuadrature_intervalIntegral m
    (fun x t => positiveEleventh (x-t)*g t/39916800) (fun i => (hc _).intervalIntegrable _ _)
  change twelveQuadrature m (twelvePeanoPrimitive g) = _ at hq
  have hscalar (t : ℝ) : twelveQuadrature m (fun x => positiveEleventh (x-t)*g t/39916800) =
      twelveQuadrature m (fun x => positiveEleventh (x-t))*g t/39916800 := by
    calc
      _ = twelveQuadrature m (fun x => (g t/39916800)*positiveEleventh (x-t)) := by
        congr 1; funext x; ring
      _ = _ := by rw [twelveQuadrature_mul_const]; ring
  simp_rw [hscalar] at hq
  have hcq : Continuous (fun t => twelveQuadrature m (fun x => positiveEleventh (x-t))*g t/39916800) := by
    unfold twelveQuadrature positiveEleventh
    fun_prop
  have hci : Continuous (fun t : ℝ => ((1-t)^12/12)*g t/39916800) := by fun_prop
  rw [hq, twelvePeanoPrimitive_integral hg,
    ← intervalIntegral.integral_sub (hcq.intervalIntegrable _ _) (hci.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  unfold twelveUnitPeanoKernel
  ring

/-- Exact polynomial cancellation and an actual Fubini-derived error identity. -/
theorem twelveQuadrature_peano_error_bound {m : ℕ} (hm : 74 ≤ m) (a : Fin 12 → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M) :
    |twelveQuadrature m (fun x => (∑ k : Fin 12, a k*x^k.val) + twelvePeanoPrimitive g x) -
      (∫ x in (0 : ℝ)..1, (∑ k : Fin 12, a k*x^k.val) + twelvePeanoPrimitive g x)| ≤
        ((10^24)/(m : ℝ)^12)*M := by
  have hp : Continuous (fun x : ℝ => ∑ k : Fin 12, a k*x^k.val) := by fun_prop
  rw [twelveQuadrature_add,
    intervalIntegral.integral_add (hp.intervalIntegrable _ _) (twelvePeanoPrimitive_intervalIntegrable hg),
    twelveQuadrature_degree_eleven hm a]
  rw [show ((∫ x in (0 : ℝ)..1, ∑ k : Fin 12, a k*x^k.val) + twelveQuadrature m (twelvePeanoPrimitive g)) -
      ((∫ x in (0 : ℝ)..1, ∑ k : Fin 12, a k*x^k.val) + ∫ x in (0 : ℝ)..1, twelvePeanoPrimitive g x) =
      twelveQuadrature m (twelvePeanoPrimitive g) - ∫ x in (0 : ℝ)..1, twelvePeanoPrimitive g x by ring]
  rw [twelvePeanoPrimitive_quadrature_error hg]
  exact twelveUnitPeanoKernel_weighted_integral_bound hm g M hM


theorem twelvePeanoPrimitive_eq_initial_integral {g : ℝ → ℝ} (hg : Continuous g)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    twelvePeanoPrimitive g x = ∫ t in (0 : ℝ)..x, (x-t)^11*g t/39916800 := by
  have hc : Continuous (fun t => positiveEleventh (x-t)*g t/39916800) := by
    unfold positiveEleventh
    fun_prop
  have hzero : (∫ t in x..(1 : ℝ), positiveEleventh (x-t)*g t/39916800) = 0 := by
    calc
      _ = ∫ _t in x..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le hx.2] at ht
        unfold positiveEleventh
        rw [max_eq_right (sub_nonpos.mpr ht.1)]
        simp
      _ = 0 := by simp
  unfold twelvePeanoPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x 1), hzero, add_zero]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le hx.1] at ht
  unfold positiveEleventh
  rw [max_eq_left (sub_nonneg.mpr ht.2)]


theorem taylor_unit_eleven (f : ℝ → ℝ) (x : ℝ) :
    taylorWithinEval f 11 (Set.Icc (0 : ℝ) 1) 0 x =
      ∑ k : Fin 12, ((k.val.factorial : ℝ)⁻¹ *
        iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0)*x^k.val := by
  rw [taylor_within_apply]
  simp only [sub_zero, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem twelfth_order_local_representation {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 12 f (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    f x = (∑ k : Fin 12, ((k.val.factorial : ℝ)⁻¹ *
      iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0)*x^k.val) +
        twelvePeanoPrimitive (fun t =>
          iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) (unitClamp t)) x := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hg : Continuous (fun t =>
      iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) (unitClamp t)) :=
    continuous_unit_extension (hf.continuousOn_iteratedDerivWithin (by norm_num) hu)
  by_cases hx0 : x = 0
  · subst x
    rw [← taylor_unit_eleven f 0, taylorWithinEval_self,
      twelvePeanoPrimitive_eq_initial_integral hg hx]
    simp
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) x) := uniqueDiffOn_uIcc (Ne.symm hx0)
  have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hx.1]
    intro t ht
    exact ⟨ht.1, ht.2.trans hx.2⟩
  have hw (j : ℕ) (hj : j ≤ 12) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) x) :
      iteratedDerivWithin j f (Set.uIcc (0 : ℝ) x) t =
        iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) t :=
    iteratedDerivWithin_subset_interval hsub hs hu (hf.of_le (by exact_mod_cast hj)) ht
  have hp : taylorWithinEval f 11 (Set.uIcc (0 : ℝ) x) 0 x =
      taylorWithinEval f 11 (Set.Icc (0 : ℝ) 1) 0 x := by
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hj6 : j ≤ 12 := by simp only [Finset.mem_range] at hj; omega
    rw [hw j hj6 0 (by rw [Set.uIcc_of_le hx.1]; exact ⟨le_rfl, hx.1⟩)]
  have hi : (∫ t in (0 : ℝ)..x,
      ((x-t)^11/(Nat.factorial 11 : ℝ)) • iteratedDerivWithin 12 f (Set.uIcc (0 : ℝ) x) t) =
      twelvePeanoPrimitive (fun t =>
        iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) (unitClamp t)) x := by
    rw [twelvePeanoPrimitive_eq_initial_integral hg hx]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hw 12 (by omega) t ht, unitClamp_eq (hsub ht)]
    norm_num [smul_eq_mul]
    ring
  have h := taylor_integral_remainder (n := 11) (x₀ := (0 : ℝ)) (x := x) (hf.mono hsub)
  rw [hp, taylor_unit_eleven f x, hi] at h
  linarith

/-- Local smoothness includes one-sided derivatives at the endpoints. -/
theorem twelveQuadrature_twelfth_order_bound_on {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 12 f (Set.Icc (0 : ℝ) 1)) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) t| ≤ M) :
    |twelveQuadrature m f - ∫ x in (0 : ℝ)..1, f x| ≤ ((10^24)/(m : ℝ)^12)*M := by
  let a : Fin 12 → ℝ := fun k => (k.val.factorial : ℝ)⁻¹ *
    iteratedDerivWithin k.val f (Set.Icc (0 : ℝ) 1) 0
  let g : ℝ → ℝ := fun t => iteratedDerivWithin 12 f (Set.Icc (0 : ℝ) 1) (unitClamp t)
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hg : Continuous g :=
    continuous_unit_extension (hf.continuousOn_iteratedDerivWithin (by norm_num) hu)
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M := by
    intro t ht
    dsimp only [g]
    rw [unitClamp_eq ht]
    exact hM t ht
  have hrepr : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      f x = (∑ k : Fin 12, a k*x^k.val) + twelvePeanoPrimitive g x :=
    fun _ hx => twelfth_order_local_representation hf hx
  have hq : twelveQuadrature m f =
      twelveQuadrature m (fun x => (∑ k : Fin 12, a k*x^k.val) + twelvePeanoPrimitive g x) := by
    rw [twelveQuadrature_as_node_sum, twelveQuadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hrepr _ (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm i))
  have hi : (∫ x in (0 : ℝ)..1, f x) =
      ∫ x in (0 : ℝ)..1, (∑ k : Fin 12, a k*x^k.val) + twelvePeanoPrimitive g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hrepr x hx
  rw [hq, hi]
  exact twelveQuadrature_peano_error_bound hm a g hg M hb


theorem twelveQuadrature_cell_twelfth_order_bound_on {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ}
    (a w : ℝ) (hw : 0 < w) (hf : ContDiffOn ℝ 12 f (Set.Icc a (a+w))) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc a (a+w),
      |iteratedDerivWithin 12 f (Set.Icc a (a+w)) x| ≤ M) :
    |w*twelveQuadrature m (fun t => f (a+w*t)) - ∫ x in a..a+w, f x| ≤
      ((10^24)/(m : ℝ)^12)*w^13*M := by
  have hmap : Set.MapsTo (fun x => a+w*x) (Set.Icc (0 : ℝ) 1) (Set.Icc a (a+w)) :=
    fun _ hx => affine_mem_cell a w hw hx
  have hg : ContDiffOn ℝ 12 (fun t => f (a+w*t)) (Set.Icc (0 : ℝ) 1) :=
    hf.comp (by fun_prop) hmap
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 (fun x => f (a+w*x)) (Set.Icc (0 : ℝ) 1) t| ≤ w^12*M := by
    intro t ht
    rw [iteratedDerivWithin_affine_cell a w hw hf ht, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ w^12)]
    exact mul_le_mul_of_nonneg_left (hM _ (hmap ht)) (by positivity)
  have h := twelveQuadrature_twelfth_order_bound_on hm hg (w^12*M) hb
  have hi : (∫ x in a..a+w, f x) = w*(∫ t in (0 : ℝ)..1, f (a+w*t)) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f w a
  rw [hi, ← mul_sub, abs_mul, abs_of_pos hw]
  calc
    _ ≤ w*(((10^24)/(m : ℝ)^12)*(w^12*M)) := mul_le_mul_of_nonneg_left h hw.le
    _ = ((10^24)/(m : ℝ)^12)*w^13*M := by ring


end SphericalRiesz.Boundary
