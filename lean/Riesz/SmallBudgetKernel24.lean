import Riesz.LeechGaussianEnds24

/-! The small-alpha Gaussian budget of a configuration on S²⁴ as a pair kernel.

`κ(x,y) = ∫_{(0,4]} α^(q-1) e^{-c α |x-y|²} dα` is symmetric, bounded by its constant diagonal
`4^q/q`, jointly measurable, and commutes with integration against finite measures.  The actual
budget of a configuration is `N H_q(X) = Σ_{i,j} κ(x_i,x_j) - N² β`.  No bound of the budget is
asserted here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

/-- Weighted Gaussian kernel of the small-alpha budget. -/
def smallBudgetKernel24 (c q : ℝ) (x y : SphereD 24) : ℝ :=
  ∫ α in Ioc (0:ℝ) 4, α^(q-1)*sphereGaussianKernel24 (c*α) x y

theorem rpow_sub_one_integrableOn_Ioc {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun α : ℝ => α^(q-1)) (Ioc 0 4) :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1) (a := 0) (b := 4)).1

theorem rpow_sub_one_integral_Ioc {q : ℝ} (hq : 0 < q) :
    ∫ α in Ioc (0:ℝ) 4, α^(q-1) = 4^q/q := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 4),
    integral_rpow (Or.inl (by linarith))]
  rw [show q-1+1 = q by ring, Real.zero_rpow hq.ne']
  ring

theorem smallBudgetIntegrand24_measurable (c q : ℝ) (x y : SphereD 24) :
    Measurable (fun α : ℝ => α^(q-1)*sphereGaussianKernel24 (c*α) x y) := by
  unfold sphereGaussianKernel24
  exact (measurable_id.pow_const (q-1)).mul (by fun_prop)

theorem smallBudgetIntegrand24_integrableOn {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (x y : SphereD 24) :
    IntegrableOn (fun α : ℝ => α^(q-1)*sphereGaussianKernel24 (c*α) x y) (Ioc 0 4) := by
  refine Integrable.mono' (rpow_sub_one_integrableOn_Ioc hq)
    (smallBudgetIntegrand24_measurable c q x y).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hα.1.le _),
    abs_of_nonneg (sphereGaussianKernel24_nonneg _ _ _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianKernel24_le_one (mul_nonneg hc hα.1.le) x y)

theorem smallBudgetKernel24_symm (c q : ℝ) (x y : SphereD 24) :
    smallBudgetKernel24 c q x y = smallBudgetKernel24 c q y x := by
  unfold smallBudgetKernel24 sphereGaussianKernel24
  simp_rw [dist_comm x y]

theorem smallBudgetKernel24_nonneg (c q : ℝ) (x y : SphereD 24) :
    0 ≤ smallBudgetKernel24 c q x y :=
  setIntegral_nonneg measurableSet_Ioc fun _α hα =>
    mul_nonneg (Real.rpow_nonneg hα.1.le _) (sphereGaussianKernel24_nonneg _ _ _)

theorem smallBudgetKernel24_self (c : ℝ) {q : ℝ} (hq : 0 < q) (x : SphereD 24) :
    smallBudgetKernel24 c q x x = 4^q/q := by
  unfold smallBudgetKernel24
  simp only [sphereGaussianKernel24_self, mul_one]
  exact rpow_sub_one_integral_Ioc hq

theorem smallBudgetKernel24_le {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x y : SphereD 24) :
    smallBudgetKernel24 c q x y ≤ 4^q/q := by
  rw [← rpow_sub_one_integral_Ioc hq]
  refine setIntegral_mono_on (smallBudgetIntegrand24_integrableOn hc hq x y)
    (rpow_sub_one_integrableOn_Ioc hq) measurableSet_Ioc ?_
  intro α hα
  exact mul_le_of_le_one_right (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianKernel24_le_one (mul_nonneg hc hα.1.le) x y)

theorem smallBudgetJoint24_measurable (c q : ℝ) :
    Measurable (fun z : (SphereD 24 × SphereD 24) × ℝ =>
      z.2^(q-1)*sphereGaussianKernel24 (c*z.2) z.1.1 z.1.2) := by
  unfold sphereGaussianKernel24
  apply Measurable.mul (measurable_snd.pow_const (q-1))
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.mul (measurable_const.mul measurable_snd)
  exact ((continuous_dist.comp (continuous_fst.comp continuous_fst |>.prodMk
    (continuous_snd.comp continuous_fst))).measurable).pow_const 2

theorem smallBudgetKernel24_measurable (c q : ℝ) :
    StronglyMeasurable (fun p : SphereD 24 × SphereD 24 => smallBudgetKernel24 c q p.1 p.2) :=
  (smallBudgetJoint24_measurable c q).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) 4))

theorem smallBudgetKernel24_row_measurable (c q : ℝ) (x : SphereD 24) :
    StronglyMeasurable (fun y : SphereD 24 => smallBudgetKernel24 c q x y) := by
  have hf : StronglyMeasurable (fun z : SphereD 24 × ℝ =>
      z.2^(q-1)*sphereGaussianKernel24 (c*z.2) x z.1) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel24
    apply Measurable.mul (measurable_snd.pow_const (q-1))
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_fst)).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 4))

/-- The kernel is bounded, hence integrable against every finite measure on pairs. -/
theorem smallBudgetKernel24_integrable {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (ρ : Measure (SphereD 24 × SphereD 24)) [IsFiniteMeasure ρ] :
    Integrable (fun p : SphereD 24 × SphereD 24 => smallBudgetKernel24 c q p.1 p.2) ρ := by
  refine Integrable.of_bound (smallBudgetKernel24_measurable c q).aestronglyMeasurable (4^q/q) ?_
  refine Eventually.of_forall fun p => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (smallBudgetKernel24_nonneg c q _ _)]
  exact smallBudgetKernel24_le hc hq _ _

theorem smallBudgetKernel24_row_integrable {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x : SphereD 24)
    (μ : Measure (SphereD 24)) [IsFiniteMeasure μ] :
    Integrable (fun y : SphereD 24 => smallBudgetKernel24 c q x y) μ := by
  refine Integrable.of_bound (smallBudgetKernel24_row_measurable c q x).aestronglyMeasurable
    (4^q/q) ?_
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (smallBudgetKernel24_nonneg c q _ _)]
  exact smallBudgetKernel24_le hc hq _ _

theorem sphereGaussianKernel24_integrable_finite {t : ℝ} (ht : 0 ≤ t)
    (ρ : Measure (SphereD 24 × SphereD 24)) [IsFiniteMeasure ρ] :
    Integrable (fun p : SphereD 24 × SphereD 24 => sphereGaussianKernel24 t p.1 p.2) ρ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel24; fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel24_nonneg _ _ _)]
  exact sphereGaussianKernel24_le_one ht p.1 p.2

theorem sphereGaussianKernel24_row_integrable_finite {t : ℝ} (ht : 0 ≤ t) (x : SphereD 24)
    (μ : Measure (SphereD 24)) [IsFiniteMeasure μ] :
    Integrable (fun y : SphereD 24 => sphereGaussianKernel24 t x y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel24; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel24_nonneg _ _ _)]
  exact sphereGaussianKernel24_le_one ht x y

/-- Joint integrability of the weighted Gaussian in the pair and the scale. -/
theorem smallBudgetJoint24_integrable {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (ρ : Measure (SphereD 24 × SphereD 24)) [IsFiniteMeasure ρ] :
    Integrable (fun z : (SphereD 24 × SphereD 24) × ℝ =>
      z.2^(q-1)*sphereGaussianKernel24 (c*z.2) z.1.1 z.1.2)
      (ρ.prod (volume.restrict (Ioc (0:ℝ) 4))) := by
  refine Integrable.mono' (Integrable.comp_snd (rpow_sub_one_integrableOn_Ioc hq) ρ)
    (smallBudgetJoint24_measurable c q).aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
    with z hz
  have hz0 : 0 ≤ z.2 := hz.1.le
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hz0 _),
    abs_of_nonneg (sphereGaussianKernel24_nonneg _ _ _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hz0 _)
    (sphereGaussianKernel24_le_one (mul_nonneg hc hz0) _ _)

theorem smallBudget_pair_integral_eq {c q : ℝ} (hc : 0 ≤ c) (μ₁ μ₂ : Measure (SphereD 24))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {α : ℝ} (hα : 0 ≤ α) :
    (∫ p : SphereD 24 × SphereD 24, α^(q-1)*sphereGaussianKernel24 (c*α) p.1 p.2 ∂μ₁.prod μ₂) =
      α^(q-1)*∫ x, ∫ y, sphereGaussianKernel24 (c*α) x y ∂μ₂ ∂μ₁ := by
  rw [integral_const_mul, integral_prod _
    (sphereGaussianKernel24_integrable_finite (mul_nonneg hc hα) (μ₁.prod μ₂))]

/-- The weighted scale integral commutes with integration against two finite measures. -/
theorem smallBudgetKernel24_integral_swap {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (μ₁ μ₂ : Measure (SphereD 24)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    ∫ x, ∫ y, smallBudgetKernel24 c q x y ∂μ₂ ∂μ₁ =
      ∫ α in Ioc (0:ℝ) 4, α^(q-1)*∫ x, ∫ y, sphereGaussianKernel24 (c*α) x y ∂μ₂ ∂μ₁ := by
  have hκ := smallBudgetKernel24_integrable hc hq (μ₁.prod μ₂)
  rw [← integral_prod _ hκ]
  have hswap := integral_integral_swap
    (f := fun (p : SphereD 24 × SphereD 24) (α : ℝ) =>
      α^(q-1)*sphereGaussianKernel24 (c*α) p.1 p.2)
    (smallBudgetJoint24_integrable hc hq (μ₁.prod μ₂))
  calc (∫ p : SphereD 24 × SphereD 24, smallBudgetKernel24 c q p.1 p.2 ∂μ₁.prod μ₂)
      = ∫ α in Ioc (0:ℝ) 4, ∫ p : SphereD 24 × SphereD 24,
          α^(q-1)*sphereGaussianKernel24 (c*α) p.1 p.2 ∂μ₁.prod μ₂ := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Ioc fun α hα =>
      smallBudget_pair_integral_eq hc μ₁ μ₂ hα.1.le

/-- Integrability in the scale of the weighted pair integral against two finite measures. -/
theorem smallBudgetScale_integrableOn {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q)
    (μ₁ μ₂ : Measure (SphereD 24)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    IntegrableOn (fun α : ℝ => α^(q-1)*∫ x, ∫ y, sphereGaussianKernel24 (c*α) x y ∂μ₂ ∂μ₁)
      (Ioc 0 4) := by
  have h := (smallBudgetJoint24_integrable hc hq (μ₁.prod μ₂)).integral_prod_right
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  exact smallBudget_pair_integral_eq hc μ₁ μ₂ hα.1.le

theorem smallBudgetScale_row_integrableOn {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x : SphereD 24)
    (μ : Measure (SphereD 24)) [IsFiniteMeasure μ] :
    IntegrableOn (fun α : ℝ => α^(q-1)*∫ y, sphereGaussianKernel24 (c*α) x y ∂μ) (Ioc 0 4) := by
  have h := smallBudgetScale_integrableOn hc hq (Measure.dirac x) μ
  simpa only [integral_dirac] using h

theorem smallBudgetKernel24_row_integral {c q : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (x : SphereD 24)
    (μ : Measure (SphereD 24)) [IsFiniteMeasure μ] :
    ∫ y, smallBudgetKernel24 c q x y ∂μ =
      ∫ α in Ioc (0:ℝ) 4, α^(q-1)*∫ y, sphereGaussianKernel24 (c*α) x y ∂μ := by
  have h := smallBudgetKernel24_integral_swap hc hq (Measure.dirac x) μ
  simpa only [integral_dirac] using h

/-- Background of the small-alpha budget at the density scale of `N` points. -/
def smallBudgetBackground24 (N : ℕ) (q : ℝ) : ℝ :=
  ∫ α in Ioc (0:ℝ) 4, α^(q-1)*sphereGaussianBackground24 (sphereGaussianDensityFactor24 N*α)

theorem sphereGaussianBackground24_scale_measurable (c : ℝ) :
    StronglyMeasurable (fun α : ℝ => sphereGaussianBackground24 (c*α)) := by
  have hf : StronglyMeasurable (fun z : ℝ × (SphereD 24 × SphereD 24) =>
      sphereGaussianKernel24 (c*z.1) z.2.1 z.2.2) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel24
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_fst)
    exact ((continuous_dist.comp (continuous_fst.comp continuous_snd |>.prodMk
      (continuous_snd.comp continuous_snd))).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := (sphereProbabilityD 24).prod (sphereProbabilityD 24))

theorem smallBudgetBackground24_integrableOn {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun α : ℝ => α^(q-1)*
      sphereGaussianBackground24 (sphereGaussianDensityFactor24 N*α)) (Ioc 0 4) := by
  have hc := sphereGaussianDensityFactor24_pos hN
  refine Integrable.mono' (rpow_sub_one_integrableOn_Ioc hq)
    (((measurable_id.pow_const (q-1)).aestronglyMeasurable).mul
      (sphereGaussianBackground24_scale_measurable _).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hα.1.le _),
    abs_of_nonneg (sphereGaussianBackground24_nonneg _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianBackground24_le_one (mul_nonneg hc.le hα.1.le))

/-- The actual small-alpha budget of a configuration in kernel form. -/
theorem sphereGaussianSmallBudget24_eq_kernel {N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 < q)
    (X : ConfigurationD 24 N) :
    (N:ℝ)*sphereGaussianSmallBudget24 q X =
      (∑ i, ∑ j, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (X i) (X j))-
        (N:ℝ)^2*smallBudgetBackground24 N q := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc0 : 0 ≤ sphereGaussianDensityFactor24 N := (sphereGaussianDensityFactor24_pos hN).le
  have hK : ∀ i j, IntegrableOn (fun α : ℝ => α^(q-1)*
      sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (X i) (X j)) (Ioc 0 4) :=
    fun i j => smallBudgetIntegrand24_integrableOn hc0 hq _ _
  have hB := smallBudgetBackground24_integrableOn hN hq
  have hpoint : ∀ α : ℝ, α^(q-1)*(sphereGaussianCenteredScaled24 α X+1) =
      (N:ℝ)⁻¹*(∑ i, ∑ j, α^(q-1)*
        sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (X i) (X j))-
        (N:ℝ)*(α^(q-1)*sphereGaussianBackground24 (sphereGaussianDensityFactor24 N*α)) := by
    intro α
    unfold sphereGaussianCenteredScaled24
    rw [sphereGaussianScale24_eq_factor]
    simp only [← Finset.mul_sum]
    field_simp
    ring
  have hA : Integrable (fun α : ℝ => (N:ℝ)⁻¹*(∑ i, ∑ j, α^(q-1)*
      sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (X i) (X j)))
      (volume.restrict (Ioc 0 4)) :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hK i j).const_mul _
  unfold sphereGaussianSmallBudget24
  simp_rw [hpoint]
  rw [integral_sub hA (hB.const_mul _), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hK i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hK _ j)]
  unfold smallBudgetKernel24 smallBudgetBackground24
  field_simp

end SphericalRiesz
