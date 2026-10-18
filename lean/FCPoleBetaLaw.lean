import FCAreaBridge
import FCLaplaceLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RieszSphereFC

def poleBetaMeasure (k : ℕ) (c : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 2)).withDensity
    (fun v => ENNReal.ofReal (c * v ^ k * (2 - v) ^ k))

instance poleBetaMeasure_finite (k : ℕ) (c : ℝ) : IsFiniteMeasure (poleBetaMeasure k c) := by
  have hc : Continuous (fun v : ℝ => c * v ^ k * (2 - v) ^ k) := by fun_prop
  have hi : IntegrableOn (fun v : ℝ => c * v ^ k * (2 - v) ^ k) (Ioo 0 2) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  apply isFiniteMeasure_withDensity
  exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.2).ne

theorem poleBetaMeasure_ae_mem (k : ℕ) (c : ℝ) :
    ∀ᵐ v ∂poleBetaMeasure k c, v ∈ Ioo (0 : ℝ) 2 := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

theorem poleBetaMeasure_integral {c : ℝ} (hc : 0 ≤ c) (k : ℕ) (f : ℝ → ℝ) :
    (∫ v, f v ∂poleBetaMeasure k c) =
      c * ∫ v in Ioo (0 : ℝ) 2, f v * v ^ k * (2 - v) ^ k := by
  unfold poleBetaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hc (pow_nonneg hv.1.le _))
    (pow_nonneg (sub_nonneg.mpr hv.2.le) _)), smul_eq_mul]
  ring

theorem sphere_dist_le_two (d : ℕ) (x y : Sphere d) : dist x y ≤ 2 := by
  change ‖(x : EuclideanSpace ℝ (Fin (d + 1))) - y‖ ≤ 2
  calc
    _ ≤ ‖(x : EuclideanSpace ℝ (Fin (d + 1)))‖ + ‖(y : EuclideanSpace ℝ (Fin (d + 1)))‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere y]; norm_num

/-- The known Gaussian background determines the full distance-power distribution. -/
theorem sphere_riesz_integral_eq_beta {d k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hGaussian : ∀ t : ℝ, 0 < t →
      (∫ p : Sphere d × Sphere d, Real.exp (-(t * dist p.1 p.2 ^ 2))
        ∂((uniform d).prod (uniform d))) =
        c * ∫ v in Ioo (0 : ℝ) 2, Real.exp (-(2 * t * v)) * v ^ k * (2 - v) ^ k)
    (s : ℝ) :
    (∫ p : Sphere d × Sphere d, dist p.1 p.2 ^ (-s) ∂((uniform d).prod (uniform d))) =
      c * ∫ v in Ioo (0 : ℝ) 2, (2 * v) ^ (-s / 2) * v ^ k * (2 - v) ^ k := by
  letI : IsProbabilityMeasure (uniform d) := by
    rw [uniform_eq]
    infer_instance
  let μ := (uniform d).prod (uniform d)
  let X : Sphere d × Sphere d → ℝ := fun p => -(dist p.1 p.2 ^ 2)
  let Y : ℝ → ℝ := fun v => -(2 * v)
  have hX : Measurable X := by unfold X; fun_prop
  have hY : Measurable Y := by unfold Y; fun_prop
  have hC : ∀ᵐ p ∂μ, |X p| ≤ 4 := .of_forall fun p => by
    change |-(dist p.1 p.2 ^ 2)| ≤ (4 : ℝ)
    rw [abs_neg, abs_of_nonneg (sq_nonneg (dist p.1 p.2))]
    have h := sphere_dist_le_two d p.1 p.2
    nlinarith [dist_nonneg (x := p.1) (y := p.2)]
  have hD : ∀ᵐ v ∂poleBetaMeasure k c, |Y v| ≤ 4 := by
    filter_upwards [poleBetaMeasure_ae_mem k c] with v hv
    simp only [Y, abs_neg, abs_mul, abs_of_nonneg hv.1.le]
    norm_num
    linarith [hv.2]
  have hMap : μ.map X = (poleBetaMeasure k c).map Y := by
    apply map_eq_of_bounded_laplace hX hY hC hD
    intro t ht
    rw [poleBetaMeasure_integral hc]
    have he : (fun v : ℝ => Real.exp (t * Y v) * v ^ k * (2 - v) ^ k) =
        fun v : ℝ => Real.exp (-(2 * t * v)) * v ^ k * (2 - v) ^ k := by
      funext v
      congr 3
      dsimp [Y]
      ring
    rw [he]
    simpa only [μ, X, mul_neg] using hGaussian t ht
  let f : ℝ → ℝ := fun r => (-r) ^ (-s / 2)
  have hf : Measurable f := by unfold f; fun_prop
  have he := congrArg (fun m : Measure ℝ => ∫ r, f r ∂m) hMap
  rw [integral_map hX.aemeasurable hf.aestronglyMeasurable,
    integral_map hY.aemeasurable hf.aestronglyMeasurable,
    poleBetaMeasure_integral hc] at he
  have hpow (r : ℝ) (hr : 0 ≤ r) : (r ^ 2) ^ (-s / 2) = r ^ (-s) := by
    calc
      _ = (r ^ (2 : ℝ)) ^ (-s / 2) := by norm_num
      _ = r ^ ((2 : ℝ) * (-s / 2)) := (Real.rpow_mul hr _ _).symm
      _ = r ^ (-s) := by congr 1; ring
  simpa only [f, X, Y, neg_neg, hpow _ dist_nonneg] using he

end RieszSphereFC
