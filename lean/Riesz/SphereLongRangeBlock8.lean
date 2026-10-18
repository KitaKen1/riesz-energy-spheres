import Riesz.SphereLongRangeKernel8

/-! Gaussian representation of the long-range blocks.

A Gaussian block `kernelBlock8 G_t X S M` is the diffuse Gaussian defect of the points `X` against
the background `M σ|_S`.  The long-range block is the `α^p`-average over `0 < α ≤ 1` of the
Gaussian blocks at `t = cα` (Fubini on `Ioc 0 1` against finite measures; all integrands are
bounded by `α^p`).  Hence long-range blocks against any background are nonnegative, and the
off-diagonal residual energy differs from the full one by `r/(p+1)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem patchBackground8_integral (S : Set Sphere8) {F : Ambient9 → ℝ}
    (hF : AEStronglyMeasurable F (patchBackground8 S)) :
    ∫ x, F x ∂patchBackground8 S = ∫ x in S, F (x:Ambient9) ∂sphereProbability8 := by
  unfold patchBackground8
  exact integral_map (by fun_prop) hF

theorem continuous_gaussianKernel_uncurry (t : ℝ) :
    Continuous (fun q : Ambient9 × Ambient9 => gaussianKernel t q.1 q.2) := by
  unfold gaussianKernel
  fun_prop

theorem gaussianKernelPotential8_eq (t : ℝ) (S : Set Sphere8) (x : Sphere8) :
    kernelPotential8 (sphereGaussianKernel8 t) S x =
      ∫ y, gaussianKernel t (x:Ambient9) y ∂patchBackground8 S := by
  have hF : AEStronglyMeasurable (fun y : Ambient9 => gaussianKernel t (x:Ambient9) y)
      (patchBackground8 S) := by
    apply Continuous.aestronglyMeasurable
    unfold gaussianKernel
    fun_prop
  rw [patchBackground8_integral S hF]
  unfold kernelPotential8
  simp only [sphereGaussianKernel8_eq_ambient]

theorem gaussianKernelBackground8_eq {t : ℝ} (ht : 0 ≤ t) (S : Set Sphere8) :
    kernelBackground8 (sphereGaussianKernel8 t) S S =
      gaussianMeasurePair t (patchBackground8 S) (patchBackground8 S) := by
  rw [gaussianMeasurePair_iterated ht]
  have hm : StronglyMeasurable (fun x : Ambient9 => ∫ y, gaussianKernel t x y ∂patchBackground8 S) :=
    (continuous_gaussianKernel_uncurry t).stronglyMeasurable.integral_prod_right'
  rw [patchBackground8_integral S hm.aestronglyMeasurable]
  unfold kernelBackground8
  simp_rw [gaussianKernelPotential8_eq]

/-- A Gaussian block is a diffuse Gaussian defect. -/
theorem gaussianKernelBlock8_eq {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (sphereGaussianKernel8 t) X S M =
      diffuseGaussianDefect t M (fun i => (X i : Ambient9)) (patchBackground8 S) := by
  unfold kernelBlock8
  rw [gaussianKernelBackground8_eq ht]
  simp_rw [gaussianKernelPotential8_eq]
  unfold kernelPair8 diffuseGaussianDefect
  simp only [sphereGaussianKernel8_eq_ambient]

theorem gaussianKernelBlock8_nonneg {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t)
    (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    0 ≤ kernelBlock8 (sphereGaussianKernel8 t) X S M := by
  rw [gaussianKernelBlock8_eq ht]
  exact diffuseGaussianDefect_nonneg ht M _ _

theorem gaussianKernelPotential8_abs_le {t : ℝ} (ht : 0 ≤ t) (S : Set Sphere8) (x : Sphere8) :
    |kernelPotential8 (sphereGaussianKernel8 t) S x| ≤ 1 :=
  kernelPotential8_abs_le (fun x y => by
    rw [abs_of_nonneg (sphereGaussianKernel8_nonneg _ _ _)]
    exact sphereGaussianKernel8_le_one ht x y) S x

theorem gaussianKernelPotential8_param_measurable (c : ℝ) (S : Set Sphere8) :
    StronglyMeasurable (fun z : Sphere8 × ℝ =>
      kernelPotential8 (sphereGaussianKernel8 (c*z.2)) S z.1) := by
  have hf : Continuous (fun q : (Sphere8 × ℝ) × Sphere8 =>
      sphereGaussianKernel8 (c*q.1.2) q.1.1 q.2) := by
    unfold sphereGaussianKernel8
    fun_prop
  exact hf.stronglyMeasurable.integral_prod_right' (ν := sphereProbability8.restrict S)

/-- Fubini for one long-range potential. -/
theorem longRangePotential8_eq {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (S : Set Sphere8)
    (x : Sphere8) :
    kernelPotential8 (longRangeKernel8 c p) S x =
      ∫ α in Ioc (0:ℝ) 1, α^p*kernelPotential8 (sphereGaussianKernel8 (c*α)) S x := by
  have hint : Integrable (Function.uncurry fun (y : Sphere8) (α : ℝ) =>
      α^p*sphereGaussianKernel8 (c*α) x y)
      ((sphereProbability8.restrict S).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    have hdom : Integrable (fun z : Sphere8 × ℝ => (1:ℝ)*‖z.2^p‖)
        ((sphereProbability8.restrict S).prod (volume.restrict (Ioc (0:ℝ) 1))) :=
      (integrable_const (1:ℝ)).mul_prod (longRange_weight_integrable hp).norm
    refine hdom.mono' ?_ ?_
    · exact ((longRange_integrand_measurable c p).comp
        (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).aestronglyMeasurable
    · filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
        with z hz
      simp only [Function.uncurry_def, one_mul]
      have h := longRange_integrand_le (p := p) hc hz x z.1
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hz.1.le _)]
  unfold kernelPotential8 longRangeKernel8
  rw [integral_integral_swap hint]
  simp_rw [integral_const_mul]


theorem gaussianKernelPotential8_alpha_measurable (c : ℝ) (S : Set Sphere8) (x : Sphere8) :
    StronglyMeasurable (fun α : ℝ => kernelPotential8 (sphereGaussianKernel8 (c*α)) S x) := by
  have hf : Continuous (fun q : ℝ × Sphere8 => sphereGaussianKernel8 (c*q.1) x q.2) := by
    unfold sphereGaussianKernel8
    fun_prop
  exact hf.stronglyMeasurable.integral_prod_right' (ν := sphereProbability8.restrict S)

theorem gaussianKernelPotential8_alpha_joint (c : ℝ) (S : Set Sphere8) :
    StronglyMeasurable (fun q : ℝ × Sphere8 =>
      kernelPotential8 (sphereGaussianKernel8 (c*q.1)) S q.2) := by
  have hf : Continuous (fun q : (ℝ × Sphere8) × Sphere8 =>
      sphereGaussianKernel8 (c*q.1.1) q.1.2 q.2) := by
    unfold sphereGaussianKernel8
    fun_prop
  exact hf.stronglyMeasurable.integral_prod_right' (ν := sphereProbability8.restrict S)

theorem gaussianKernelBackground8_alpha_measurable (c : ℝ) (S : Set Sphere8) :
    StronglyMeasurable (fun α : ℝ => kernelBackground8 (sphereGaussianKernel8 (c*α)) S S) :=
  (gaussianKernelPotential8_alpha_joint c S).integral_prod_right'
    (ν := sphereProbability8.restrict S)

theorem gaussianKernelBackground8_abs_le {t : ℝ} (ht : 0 ≤ t) (S : Set Sphere8) :
    |kernelBackground8 (sphereGaussianKernel8 t) S S| ≤ 1 := by
  unfold kernelBackground8
  calc |∫ x in S, kernelPotential8 (sphereGaussianKernel8 t) S x ∂sphereProbability8|
      = ‖∫ x in S, kernelPotential8 (sphereGaussianKernel8 t) S x ∂sphereProbability8‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ 1*(sphereProbability8.restrict S).real univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact gaussianKernelPotential8_abs_le ht S x)
    _ ≤ 1*1 := by
        apply mul_le_mul_of_nonneg_left _ zero_le_one
        rw [measureReal_restrict_apply_univ]
        exact measureReal_le_one
    _ = 1 := one_mul 1

theorem gaussianKernelPair8_abs_le {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (X : ι → Sphere8) :
    |kernelPair8 (sphereGaussianKernel8 t) X| ≤ (Fintype.card ι:ℝ)^2 := by
  unfold kernelPair8
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sphereGaussianKernel8_nonneg _ _ _)]
  calc ∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j) ≤ ∑ _i : ι, ∑ _j : ι, (1:ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => sphereGaussianKernel8_le_one ht _ _
    _ = (Fintype.card ι:ℝ)^2 := by simp [sq]

theorem gaussianKernelPair8_alpha_continuous {ι : Type*} [Fintype ι] (c : ℝ) (X : ι → Sphere8) :
    Continuous (fun α : ℝ => kernelPair8 (sphereGaussianKernel8 (c*α)) X) := by
  unfold kernelPair8
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_gaussian_param c (X i) (X j)

/-- `α^p` times a bounded measurable function is integrable on `Ioc 0 1`. -/
theorem weighted_bounded_integrable {p B : ℝ} (hp : -1 < p) {f : ℝ → ℝ}
    (hf : StronglyMeasurable f) (hb : ∀ α ∈ Ioc (0:ℝ) 1, |f α| ≤ B) :
    IntegrableOn (fun α : ℝ => α^p*f α) (Ioc 0 1) := by
  have hdom : IntegrableOn (fun α : ℝ => B*α^p) (Ioc 0 1) :=
    (longRange_weight_integrable hp).const_mul B
  refine hdom.mono' (((measurable_id.pow_const p).mul hf.measurable).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  have h0 : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hb α hα) h0

/-- Fubini for the long-range background. -/
theorem longRangeBackground8_eq {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (S : Set Sphere8) :
    kernelBackground8 (longRangeKernel8 c p) S S =
      ∫ α in Ioc (0:ℝ) 1, α^p*kernelBackground8 (sphereGaussianKernel8 (c*α)) S S := by
  have hint : Integrable (Function.uncurry fun (x : Sphere8) (α : ℝ) =>
      α^p*kernelPotential8 (sphereGaussianKernel8 (c*α)) S x)
      ((sphereProbability8.restrict S).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    have hdom : Integrable (fun z : Sphere8 × ℝ => (1:ℝ)*‖z.2^p‖)
        ((sphereProbability8.restrict S).prod (volume.restrict (Ioc (0:ℝ) 1))) :=
      (integrable_const (1:ℝ)).mul_prod (longRange_weight_integrable hp).norm
    have hjoint := (gaussianKernelPotential8_alpha_joint c S).measurable.comp
      (measurable_snd.prodMk measurable_fst)
    refine hdom.mono' (((measurable_snd.pow_const p).mul hjoint).aestronglyMeasurable) ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
      with z hz
    simp only [Function.uncurry_def, one_mul, Function.comp_apply]
    have h0 : 0 ≤ z.2^p := Real.rpow_nonneg hz.1.le _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right h0
      (gaussianKernelPotential8_abs_le (mul_nonneg hc hz.1.le) S z.1)
  unfold kernelBackground8
  simp_rw [longRangePotential8_eq hc hp S]
  rw [integral_integral_swap hint]
  simp_rw [integral_const_mul]

/-- Fubini for the long-range pair sum. -/
theorem longRangePair8_eq {ι : Type*} [Fintype ι] {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p)
    (X : ι → Sphere8) :
    kernelPair8 (longRangeKernel8 c p) X =
      ∫ α in Ioc (0:ℝ) 1, α^p*kernelPair8 (sphereGaussianKernel8 (c*α)) X := by
  unfold kernelPair8 longRangeKernel8
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => longRange_integrand_integrable hc hp (X i) (X j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => longRange_integrand_integrable hc hp (X i) (X j))]

/-- The long-range block is the `α^p`-average of the Gaussian blocks. -/
theorem longRangeBlock8_eq {ι : Type*} [Fintype ι] {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p)
    (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (longRangeKernel8 c p) X S M =
      ∫ α in Ioc (0:ℝ) 1, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M := by
  have hA : IntegrableOn (fun α : ℝ => α^p*kernelPair8 (sphereGaussianKernel8 (c*α)) X) (Ioc 0 1) :=
    weighted_bounded_integrable hp (gaussianKernelPair8_alpha_continuous c X).stronglyMeasurable
      (fun α hα => gaussianKernelPair8_abs_le (mul_nonneg hc hα.1.le) X)
  have hB : ∀ i, IntegrableOn (fun α : ℝ => α^p*kernelPotential8 (sphereGaussianKernel8 (c*α)) S
      (X i)) (Ioc 0 1) := fun i =>
    weighted_bounded_integrable hp (gaussianKernelPotential8_alpha_measurable c S (X i))
      (fun α hα => gaussianKernelPotential8_abs_le (mul_nonneg hc hα.1.le) S (X i))
  have hC : IntegrableOn (fun α : ℝ => α^p*kernelBackground8 (sphereGaussianKernel8 (c*α)) S S)
      (Ioc 0 1) :=
    weighted_bounded_integrable hp (gaussianKernelBackground8_alpha_measurable c S)
      (fun α hα => gaussianKernelBackground8_abs_le (mul_nonneg hc hα.1.le) S)
  have hBs : IntegrableOn (fun α : ℝ => ∑ i, α^p*kernelPotential8 (sphereGaussianKernel8 (c*α)) S
      (X i)) (Ioc 0 1) := integrable_finsetSum _ (fun i _ => hB i)
  have e : (fun α : ℝ => α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M) =
      fun α => (α^p*kernelPair8 (sphereGaussianKernel8 (c*α)) X-
        2*M*∑ i, α^p*kernelPotential8 (sphereGaussianKernel8 (c*α)) S (X i))+
        M^2*(α^p*kernelBackground8 (sphereGaussianKernel8 (c*α)) S S) := by
    funext α
    unfold kernelBlock8
    rw [← Finset.mul_sum]
    ring
  have hBB : IntegrableOn (fun α : ℝ => 2*M*∑ i, α^p*kernelPotential8
      (sphereGaussianKernel8 (c*α)) S (X i)) (Ioc 0 1) := hBs.const_mul (2*M)
  have hAB : IntegrableOn (fun α : ℝ => α^p*kernelPair8 (sphereGaussianKernel8 (c*α)) X-
      2*M*∑ i, α^p*kernelPotential8 (sphereGaussianKernel8 (c*α)) S (X i)) (Ioc 0 1) := hA.sub hBB
  have hCC : IntegrableOn (fun α : ℝ => M^2*(α^p*kernelBackground8
      (sphereGaussianKernel8 (c*α)) S S)) (Ioc 0 1) := hC.const_mul (M^2)
  rw [e, integral_add hAB hCC, integral_sub hA hBB, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hB i)]
  unfold kernelBlock8
  rw [longRangePair8_eq hc hp, longRangeBackground8_eq hc hp]
  simp_rw [longRangePotential8_eq hc hp]

/-- Long-range blocks are nonnegative. -/
theorem longRangeBlock8_nonneg {ι : Type*} [Fintype ι] {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p)
    (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    0 ≤ kernelBlock8 (longRangeKernel8 c p) X S M := by
  rw [longRangeBlock8_eq hc hp]
  exact setIntegral_nonneg measurableSet_Ioc fun α hα =>
    mul_nonneg (Real.rpow_nonneg hα.1.le _)
      (gaussianKernelBlock8_nonneg (mul_nonneg hc hα.1.le) X S M)

/-- The off-diagonal residual energy differs from the full one by the diagonal mass. -/
theorem longRange_residual_off_eq {c p : ℝ} (hp : -1 < p) (A : Set Sphere8) (L : Sphere8 → ℝ)
    {r : ℕ} (Z : Fin r → Sphere8) (hZ : Function.Injective Z) :
    residualNeutralizedEnergy (sphereRestrictedProbability8 A) (longRangeOffKernel8 c p) L Z =
      residualNeutralizedEnergy (sphereRestrictedProbability8 A) (longRangeKernel8 c p) L Z-
        (r:ℝ)/(p+1) := by
  have hrow : ∀ x, residualRowPotential (sphereRestrictedProbability8 A) (longRangeOffKernel8 c p) x =
      residualRowPotential (sphereRestrictedProbability8 A) (longRangeKernel8 c p) x := by
    intro x
    unfold residualRowPotential
    exact integral_congr_ae (longRangeOffKernel8_ae_eq c p _ x)
  have hbg : residualBackground (sphereRestrictedProbability8 A) (longRangeOffKernel8 c p) =
      residualBackground (sphereRestrictedProbability8 A) (longRangeKernel8 c p) := by
    unfold residualBackground
    simp_rw [hrow]
  have hpair : residualPairEnergy (longRangeOffKernel8 c p) Z =
      residualPairEnergy (longRangeKernel8 c p) Z-(r:ℝ)/(p+1) := by
    classical
    unfold residualPairEnergy
    have hi : ∀ i, ∑ j, longRangeOffKernel8 c p (Z i) (Z j) =
        (∑ j, longRangeKernel8 c p (Z i) (Z j))-1/(p+1) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        longRangeOffKernel8_self, longRangeKernel8_self c hp, zero_add]
      have hcongr : ∑ j ∈ Finset.univ.erase i, longRangeOffKernel8 c p (Z i) (Z j) =
          ∑ j ∈ Finset.univ.erase i, longRangeKernel8 c p (Z i) (Z j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact longRangeOffKernel8_of_ne c p (fun h => (Finset.mem_erase.mp hj).1 (hZ h).symm)
      rw [hcongr]
      ring
    simp_rw [hi]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold residualNeutralizedEnergy
  rw [hpair, hbg]
  simp_rw [hrow]
  ring

end SphericalRiesz
