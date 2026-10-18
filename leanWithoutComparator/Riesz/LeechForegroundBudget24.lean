import Riesz.LeechForegroundDefect24
import Riesz.SmallBudgetKernel24

/-! Small-alpha budget of a foreground family with the smooth residual background.

In kernel form the neutralized Gaussian energy of the mixed measure (foreground points plus
`N σ` on the residual region `R`) is

`Σ_{i,j} K(x_i,x_j) + 2N Σ_i ∫_R K(x_i,·) dσ + N² ∫_R∫_R K dσ dσ - N² B(t)`

whenever the total charge is `N`.  Integrating against `α^(q-1)` on `(0,4]` and using the
twelfth-order profile gives a budget whose family-dependent part vanishes under refinement.
The residual points themselves are not chosen here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SphericalRiesz
open Boundary

/-- Integral against the mixed measure of a bounded measurable function. -/
theorem mixedForegroundMeasure24_integral {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) (g : AmbientD 24 → ℝ) (hg : StronglyMeasurable g) (C : ℝ)
    (hC : ∀ y, |g y| ≤ C) :
    ∫ y, g y ∂(mixedForegroundMeasure24 x N R) =
      (∑ i, g (x i : AmbientD 24))+
        (N:ℝ)*∫ y in R, g (y : AmbientD 24) ∂(sphereProbabilityD 24) := by
  have hI : ∀ (μ : Measure (AmbientD 24)) [IsFiniteMeasure μ], Integrable g μ := fun μ _ =>
    Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)
  unfold mixedForegroundMeasure24
  rw [integral_add_measure (hI _) (hI _), finitePointMeasure_integral,
    integral_smul_nnreal_measure, integral_map (by fun_prop) hg.aestronglyMeasurable,
    NNReal.smul_def, NNReal.coe_natCast, smul_eq_mul]

theorem gaussianKernel_ambient_stronglyMeasurable (t : ℝ) :
    StronglyMeasurable (fun p : AmbientD 24 × AmbientD 24 => gaussianKernel t p.1 p.2) :=
  (by unfold gaussianKernel; fun_prop :
    Continuous fun p : AmbientD 24 × AmbientD 24 => gaussianKernel t p.1 p.2).stronglyMeasurable

theorem gaussianKernel_potential_measurable (t : ℝ) (μ : Measure (AmbientD 24))
    [IsFiniteMeasure μ] :
    StronglyMeasurable (fun w : AmbientD 24 => ∫ y, gaussianKernel t w y ∂μ) :=
  (gaussianKernel_ambient_stronglyMeasurable t).integral_prod_right' (ν := μ)

theorem gaussianKernel_row_integrable {t : ℝ} (ht : 0 ≤ t) (w : AmbientD 24)
    (μ : Measure (AmbientD 24)) [IsFiniteMeasure μ] :
    Integrable (fun y => gaussianKernel t w y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold gaussianKernel; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianKernel_nonneg _ _ _)]
  exact gaussianKernel_le_one ht _ _

theorem gaussianKernel_potential_abs_le {t : ℝ} (ht : 0 ≤ t) (μ : Measure (AmbientD 24))
    [IsFiniteMeasure μ] (w : AmbientD 24) :
    |∫ y, gaussianKernel t w y ∂μ| ≤ μ.real univ := by
  rw [abs_of_nonneg (integral_nonneg fun y => gaussianKernel_nonneg _ _ _)]
  calc ∫ y, gaussianKernel t w y ∂μ ≤ ∫ _y, (1:ℝ) ∂μ :=
        integral_mono (gaussianKernel_row_integrable ht w μ) (integrable_const 1)
          (fun y => gaussianKernel_le_one ht w y)
    _ = μ.real univ := by simp

theorem mixedForeground_kernel_row {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) {t : ℝ} (ht : 0 ≤ t) (w : AmbientD 24) :
    ∫ y, gaussianKernel t w y ∂(mixedForegroundMeasure24 x N R) =
      (∑ j, gaussianKernel t w (x j : AmbientD 24))+
        (N:ℝ)*∫ y in R, gaussianKernel t w (y : AmbientD 24) ∂(sphereProbabilityD 24) :=
  mixedForegroundMeasure24_integral x N R (fun y => gaussianKernel t w y)
    (by unfold gaussianKernel; fun_prop :
      Continuous fun y : AmbientD 24 => gaussianKernel t w y).stronglyMeasurable 1
    (fun y => by
      rw [abs_of_nonneg (gaussianKernel_nonneg _ _ _)]
      exact gaussianKernel_le_one ht _ _)

/-- Pair energy of the mixed measure against the sphere probability. -/
theorem mixedForeground_pair_sphere {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) {t : ℝ} (ht : 0 ≤ t) :
    gaussianMeasurePair t (mixedForegroundMeasure24 x N R) ambientSphereProbability24 =
      ((Fintype.card ι : ℝ)+(N:ℝ)*(sphereProbabilityD 24).real R)*
        sphereGaussianBackground24 t := by
  have hpot : ∀ y : SphereD 24,
      (∫ y', gaussianKernel t (y : AmbientD 24) y' ∂ambientSphereProbability24) =
        sphereGaussianBackground24 t := fun y => by
    rw [ambientSphereProbability24_kernel_integral, ← sphereGaussianBackground24_eq_potential ht y]
  rw [gaussianMeasurePair_iterated ht,
    mixedForegroundMeasure24_integral x N R
      (fun w => ∫ y, gaussianKernel t w y ∂ambientSphereProbability24)
      (gaussianKernel_potential_measurable t ambientSphereProbability24) 1
      (fun w => by simpa using gaussianKernel_potential_abs_le ht ambientSphereProbability24 w)]
  simp_rw [hpot]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, setIntegral_const, smul_eq_mul]
  ring

theorem sphereGaussianKernel24_comm (t : ℝ) (x y : SphereD 24) :
    sphereGaussianKernel24 t x y = sphereGaussianKernel24 t y x := by
  unfold sphereGaussianKernel24
  rw [dist_comm]

/-- Pair energy of the mixed measure with itself, in kernel form. -/
theorem mixedForeground_pair_self {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) {t : ℝ} (ht : 0 ≤ t) :
    gaussianMeasurePair t (mixedForegroundMeasure24 x N R) (mixedForegroundMeasure24 x N R) =
      (∑ i, ∑ j, sphereGaussianKernel24 t (x i) (x j))+
      2*(N:ℝ)*(∑ i, ∫ y in R, sphereGaussianKernel24 t (x i) y ∂(sphereProbabilityD 24))+
      (N:ℝ)^2*(∫ y in R, ∫ y' in R, sphereGaussianKernel24 t y y' ∂(sphereProbabilityD 24)
        ∂(sphereProbabilityD 24)) := by
  have h1 : gaussianMeasurePair t (mixedForegroundMeasure24 x N R)
      (mixedForegroundMeasure24 x N R) =
      (∑ i, ∫ y, gaussianKernel t (x i : AmbientD 24) y ∂(mixedForegroundMeasure24 x N R))+
        (N:ℝ)*∫ y' in R, (∫ y, gaussianKernel t (y' : AmbientD 24) y
          ∂(mixedForegroundMeasure24 x N R)) ∂(sphereProbabilityD 24) := by
    rw [gaussianMeasurePair_iterated ht]
    exact mixedForegroundMeasure24_integral x N R
      (fun w => ∫ y, gaussianKernel t w y ∂(mixedForegroundMeasure24 x N R))
      (gaussianKernel_potential_measurable t _) ((mixedForegroundMeasure24 x N R).real univ)
      (gaussianKernel_potential_abs_le ht _)
  have h2 : ∀ w : SphereD 24,
      (∫ y, gaussianKernel t (w : AmbientD 24) y ∂(mixedForegroundMeasure24 x N R)) =
      (∑ j, sphereGaussianKernel24 t w (x j))+
        (N:ℝ)*∫ y in R, sphereGaussianKernel24 t w y ∂(sphereProbabilityD 24) := by
    intro w
    rw [mixedForeground_kernel_row x N R ht]
    simp_rw [← sphereGaussianKernel24_eq_ambient]
  have hI1 : Integrable (fun y' : SphereD 24 => ∑ j, sphereGaussianKernel24 t y' (x j))
      ((sphereProbabilityD 24).restrict R) :=
    integrable_finsetSum _ fun j _ =>
      (sphereGaussianKernel24_row_integrable_finite ht (x j) _).congr
        (Filter.Eventually.of_forall fun y' => sphereGaussianKernel24_comm t (x j) y')
  have hI2 : Integrable (fun y' : SphereD 24 =>
      ∫ y in R, sphereGaussianKernel24 t y' y ∂(sphereProbabilityD 24))
      ((sphereProbabilityD 24).restrict R) :=
    (sphereGaussianKernel24_integrable_finite ht
      (((sphereProbabilityD 24).restrict R).prod ((sphereProbabilityD 24).restrict R))).integral_prod_left
  have hsym : ∀ j, (∫ y' in R, sphereGaussianKernel24 t y' (x j) ∂(sphereProbabilityD 24)) =
      ∫ y in R, sphereGaussianKernel24 t (x j) y ∂(sphereProbabilityD 24) := fun j =>
    integral_congr_ae (Filter.Eventually.of_forall fun y' => sphereGaussianKernel24_comm t y' (x j))
  rw [h1]
  simp_rw [h2]
  rw [integral_add hI1 (hI2.const_mul _), integral_finsetSum _ (fun j _ =>
      (sphereGaussianKernel24_row_integrable_finite ht (x j) _).congr
        (Filter.Eventually.of_forall fun y' => sphereGaussianKernel24_comm t (x j) y')),
    integral_const_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [hsym]
  ring

/-- Neutralized Gaussian defect of the mixed measure in kernel form, at total charge `N`. -/
theorem mixedForeground_defect_eq_kernel {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24))
    (hmass : (Fintype.card ι : ℝ)+(N:ℝ)*(sphereProbabilityD 24).real R = N) {t : ℝ}
    (ht : 0 ≤ t) :
    gaussianMeasureDefect t (N:ℝ) (mixedForegroundMeasure24 x N R) ambientSphereProbability24 =
      (∑ i, ∑ j, sphereGaussianKernel24 t (x i) (x j))+
      2*(N:ℝ)*(∑ i, ∫ y in R, sphereGaussianKernel24 t (x i) y ∂(sphereProbabilityD 24))+
      (N:ℝ)^2*(∫ y in R, ∫ y' in R, sphereGaussianKernel24 t y y' ∂(sphereProbabilityD 24)
        ∂(sphereProbabilityD 24))-
      (N:ℝ)^2*sphereGaussianBackground24 t := by
  unfold gaussianMeasureDefect
  rw [mixedForeground_pair_self x N R ht, mixedForeground_pair_sphere x N R ht, hmass,
    ambientSphereProbability24_kernel_pair]
  ring

/-- Small-alpha budget of the foreground with smooth residual background, in kernel form. -/
def mixedSmallBudget24 {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) (q : ℝ) : ℝ :=
  (∑ i, ∑ j, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (x i) (x j))+
    2*(N:ℝ)*(∑ i, ∫ y in R, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (x i) y
      ∂(sphereProbabilityD 24))+
    (N:ℝ)^2*(∫ y in R, ∫ y' in R, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q y y'
      ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))-
    (N:ℝ)^2*smallBudgetBackground24 N q

/-- The kernel form is the weighted scale integral of the neutralized defects. -/
theorem mixedSmallBudget24_eq_integral {ι : Type*} [Fintype ι] (x : ι → SphereD 24) {N : ℕ}
    (hN : 0 < N) (R : Set (SphereD 24))
    (hmass : (Fintype.card ι : ℝ)+(N:ℝ)*(sphereProbabilityD 24).real R = N) {q : ℝ}
    (hq : 0 < q) :
    mixedSmallBudget24 x N R q = (∫ α in Ioc (0:ℝ) 4, α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor24 N*α) (N:ℝ)
        (mixedForegroundMeasure24 x N R) ambientSphereProbability24) ∧
    IntegrableOn (fun α : ℝ => α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor24 N*α) (N:ℝ)
        (mixedForegroundMeasure24 x N R) ambientSphereProbability24) (Ioc 0 4) := by
  have hc : 0 ≤ sphereGaussianDensityFactor24 N := (sphereGaussianDensityFactor24_pos hN).le
  have hf₁ : ∀ i j, IntegrableOn (fun α : ℝ => α^(q-1)*
      sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j)) (Ioc 0 4) :=
    fun i j => smallBudgetIntegrand24_integrableOn hc hq _ _
  have hf₂ : ∀ i, IntegrableOn (fun α : ℝ => α^(q-1)*
      ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
        ∂(sphereProbabilityD 24)) (Ioc 0 4) :=
    fun i => smallBudgetScale_row_integrableOn hc hq (x i) _
  have hf₃ : IntegrableOn (fun α : ℝ => α^(q-1)*
      ∫ y in R, ∫ y' in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) y y'
        ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24)) (Ioc 0 4) :=
    smallBudgetScale_integrableOn hc hq _ _
  have hf₄ := smallBudgetBackground24_integrableOn hN hq
  have hS₁ : IntegrableOn (fun α : ℝ => ∑ i, ∑ j, α^(q-1)*
      sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j)) (Ioc 0 4) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hf₁ i j
  have hS₂ : IntegrableOn (fun α : ℝ => ∑ i, α^(q-1)*
      ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
        ∂(sphereProbabilityD 24)) (Ioc 0 4) :=
    integrable_finsetSum _ fun i _ => hf₂ i
  have hkey : EqOn (fun α : ℝ => α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor24 N*α) (N:ℝ)
        (mixedForegroundMeasure24 x N R) ambientSphereProbability24)
      (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
            ∂(sphereProbabilityD 24))+
        (N:ℝ)^2*(α^(q-1)*
          ∫ y in R, ∫ y' in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) y y'
            ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))-
        (N:ℝ)^2*(α^(q-1)*sphereGaussianBackground24 (sphereGaussianDensityFactor24 N*α)))
      (Ioc 0 4) := by
    intro α hα
    simp only
    rw [mixedForeground_defect_eq_kernel x N R hmass (mul_nonneg hc hα.1.le)]
    simp only [← Finset.mul_sum]
    ring
  have hT₂ : IntegrableOn (fun α : ℝ => 2*(N:ℝ)*(∑ i, α^(q-1)*
      ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
        ∂(sphereProbabilityD 24))) (Ioc 0 4) := hS₂.const_mul _
  have hT₃ : IntegrableOn (fun α : ℝ => (N:ℝ)^2*(α^(q-1)*
      ∫ y in R, ∫ y' in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) y y'
        ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))) (Ioc 0 4) := hf₃.const_mul _
  have hT₄ : IntegrableOn (fun α : ℝ => (N:ℝ)^2*(α^(q-1)*
      sphereGaussianBackground24 (sphereGaussianDensityFactor24 N*α))) (Ioc 0 4) :=
    hf₄.const_mul _
  have hT₁₂ : IntegrableOn (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
            ∂(sphereProbabilityD 24))) (Ioc 0 4) := hS₁.add hT₂
  have hT₁₂₃ : IntegrableOn (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
            ∂(sphereProbabilityD 24))+
        (N:ℝ)^2*(α^(q-1)*
          ∫ y in R, ∫ y' in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) y y'
            ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))) (Ioc 0 4) := hT₁₂.add hT₃
  have hRint : IntegrableOn (fun α : ℝ => (∑ i, ∑ j, α^(q-1)*
          sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j))+
        2*(N:ℝ)*(∑ i, α^(q-1)*
          ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
            ∂(sphereProbabilityD 24))+
        (N:ℝ)^2*(α^(q-1)*
          ∫ y in R, ∫ y' in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) y y'
            ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))-
        (N:ℝ)^2*(α^(q-1)*sphereGaussianBackground24 (sphereGaussianDensityFactor24 N*α)))
      (Ioc 0 4) := hT₁₂₃.sub hT₄
  have e₁ : (∫ α in Ioc (0:ℝ) 4, ∑ i, ∑ j, α^(q-1)*
      sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) (x j)) =
      ∑ i, ∑ j, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (x i) (x j) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hf₁ i j)]
    simp_rw [integral_finsetSum _ (fun j _ => hf₁ _ j)]
    rfl
  have e₂ : (∫ α in Ioc (0:ℝ) 4, ∑ i, α^(q-1)*
      ∫ y in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) (x i) y
        ∂(sphereProbabilityD 24)) =
      ∑ i, ∫ y in R, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q (x i) y
        ∂(sphereProbabilityD 24) := by
    rw [integral_finsetSum _ (fun i _ => hf₂ i)]
    exact Finset.sum_congr rfl fun i _ =>
      (smallBudgetKernel24_row_integral hc hq (x i) _).symm
  have e₃ : (∫ α in Ioc (0:ℝ) 4, α^(q-1)*
      ∫ y in R, ∫ y' in R, sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α) y y'
        ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24)) =
      ∫ y in R, ∫ y' in R, smallBudgetKernel24 (sphereGaussianDensityFactor24 N) q y y'
        ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24) :=
    (smallBudgetKernel24_integral_swap hc hq _ _).symm
  refine ⟨?_, hRint.congr_fun hkey.symm measurableSet_Ioc⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hkey, integral_sub hT₁₂₃ hT₄,
    integral_add hT₁₂ hT₃, integral_add hS₁ hT₂, integral_const_mul, integral_const_mul,
    integral_const_mul, e₁, e₂, e₃]
  rfl

/-- Small-alpha budget of a twelfth-order foreground family with smooth residual background. -/
theorem leechPatchFamily_mixedSmallBudget_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m),
      ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℝ)+
        (((d*m)^24:ℕ):ℝ)*(sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ =
          (((d*m)^24:ℕ):ℝ)) →
      ∀ q : ℝ, 0 < q → q ≤ 24 →
      mixedSmallBudget24 (leechFamilyNodes24 P (a*m) hn) ((d*m)^24) (leechFamilyUnion24 P)ᶜ q ≤
        (((d*m)^24:ℕ):ℝ)*(leechForegroundProfileConst24*(4^q/q)+
          leechForegroundProfileGain24 q*((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-q)*(4^(q/2)/(q/2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := leechPatchFamily_mixed_defect_profile
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn hmass q hq hq24
  have hNpos : 0 < (d*m)^24 := by positivity
  obtain ⟨heq, hint⟩ := mixedSmallBudget24_eq_integral (leechFamilyNodes24 P (a*m) hn) hNpos
    (leechFamilyUnion24 P)ᶜ hmass hq
  rw [heq]
  set G := leechForegroundProfileGain24 q*((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-q) with hG
  set C₀ := leechForegroundProfileConst24 with hC₀
  have hq2 : 0 < q/2 := by positivity
  have hpt : ∀ α ∈ Ioc (0:ℝ) 4, α^(q-1)*
      gaussianMeasureDefect (sphereGaussianDensityFactor24 ((d*m)^24)*α) (((d*m)^24:ℕ):ℝ)
        (mixedForegroundMeasure24 (leechFamilyNodes24 P (a*m) hn) ((d*m)^24)
          (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 ≤
      (((d*m)^24:ℕ):ℝ)*(C₀*α^(q-1)+G*α^(q/2-1)) := by
    intro α hα
    have h := hb P hv hε hdisj a d m hd hm hratio hn q hq hq24 α hα
    rw [sphereGaussianScale24_eq_factor] at h
    have hαq : 0 ≤ α^(q-1) := Real.rpow_nonneg hα.1.le _
    have hpow : α^(q-1)*α^(-(q/2)) = α^(q/2-1) := by
      rw [← Real.rpow_add hα.1]
      congr 1
      ring
    calc _ ≤ α^(q-1)*((((d*m)^24:ℕ):ℝ)*(C₀+G*α^(-(q/2)))) :=
          mul_le_mul_of_nonneg_left h hαq
      _ = (((d*m)^24:ℕ):ℝ)*(C₀*α^(q-1)+G*(α^(q-1)*α^(-(q/2)))) := by ring
      _ = _ := by rw [hpow]
  have hI₁ := rpow_sub_one_integrableOn_Ioc hq
  have hI₂ := rpow_sub_one_integrableOn_Ioc hq2
  have hR : IntegrableOn (fun α : ℝ => (((d*m)^24:ℕ):ℝ)*(C₀*α^(q-1)+G*α^(q/2-1))) (Ioc 0 4) :=
    ((hI₁.const_mul C₀).add (hI₂.const_mul G)).const_mul _
  calc _ ≤ ∫ α in Ioc (0:ℝ) 4, (((d*m)^24:ℕ):ℝ)*(C₀*α^(q-1)+G*α^(q/2-1)) :=
        setIntegral_mono_on hint hR measurableSet_Ioc hpt
    _ = _ := by
      rw [integral_const_mul, integral_add (hI₁.const_mul C₀) (hI₂.const_mul G),
        integral_const_mul, integral_const_mul, rpow_sub_one_integral_Ioc hq,
        rpow_sub_one_integral_Ioc hq2]

end SphericalRiesz
