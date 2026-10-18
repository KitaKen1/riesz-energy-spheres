import Riesz.SphereNegMacroKernel8
import Riesz.SphereLongRangeBlock8
import Riesz.SphereMassSplitAssembly8

/-! Blocks of the subtracted macroscopic kernel (stage NEG, second half).

The neutralized block of a kernel given as a parameter integral `∫ K_α dρ(α)` is the integral of
the blocks of `K_α`, as soon as `K` is jointly measurable and dominated by an integrable function
of `α` (Fubini on finite sphere measures). For `K_α = α^p (G_{cα} - 1)` on `(0,δ]` the block of
`G_{cα} - 1` is the Gaussian block minus `(#X - M σ(S))²`, so with exact mass `#X = M σ(S)`:
`block(K') = ∫_{(0,δ]} α^p block(G_{cα}) dα`, the macroscopic end of the negative-exponent
Mellin integral. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

section
variable (K : ℝ → Sphere8 → Sphere8 → ℝ) (ρ : Measure ℝ) [SFinite ρ] (g : ℝ → ℝ)

theorem integralKernel_dom_integrable (μ : Measure Sphere8) [IsFiniteMeasure μ]
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2))
    (hg : Integrable g ρ) (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α) (x : Sphere8) :
    Integrable (Function.uncurry fun (y : Sphere8) (α : ℝ) => K α x y) (μ.prod ρ) := by
  have hdomi : Integrable (fun z : Sphere8 × ℝ => (1:ℝ)*g z.2) (μ.prod ρ) :=
    (integrable_const (1:ℝ)).mul_prod hg
  refine hdomi.mono' ?_ ?_
  · exact (hK.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hdom] with z hz
    rw [Real.norm_eq_abs, one_mul]
    exact hz x z.1

theorem integralKernel_potential_eq
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2))
    (hg : Integrable g ρ) (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α) (S : Set Sphere8)
    (x : Sphere8) :
    kernelPotential8 (fun x y => ∫ α, K α x y ∂ρ) S x = ∫ α, kernelPotential8 (K α) S x ∂ρ := by
  unfold kernelPotential8
  exact integral_integral_swap
    (integralKernel_dom_integrable K ρ g (sphereProbability8.restrict S) hK hg hdom x)

theorem integralKernel_potential_joint
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2)) (S : Set Sphere8) :
    StronglyMeasurable (fun q : Sphere8 × ℝ => kernelPotential8 (K q.2) S q.1) := by
  have hm : Measurable (fun q : (Sphere8 × ℝ) × Sphere8 => K q.1.2 q.1.1 q.2) :=
    hK.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hf : StronglyMeasurable (fun q : (Sphere8 × ℝ) × Sphere8 => K q.1.2 q.1.1 q.2) :=
    hm.stronglyMeasurable
  exact hf.integral_prod_right' (ν := sphereProbability8.restrict S)

theorem integralKernel_potential_abs_le (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α)
    (S : Set Sphere8) : ∀ᵐ α ∂ρ, ∀ x, |kernelPotential8 (K α) S x| ≤ g α := by
  filter_upwards [hdom] with α hα x
  unfold kernelPotential8
  calc |∫ y in S, K α x y ∂sphereProbability8| = ‖∫ y in S, K α x y ∂sphereProbability8‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ g α*(sphereProbability8.restrict S).real univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hα x y)
    _ ≤ g α*1 := by
        have hg0 : 0 ≤ g α := (abs_nonneg _).trans (hα x x)
        apply mul_le_mul_of_nonneg_left _ hg0
        rw [measureReal_restrict_apply_univ]
        exact measureReal_le_one
    _ = g α := mul_one _

theorem integralKernel_background_eq
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2))
    (hg : Integrable g ρ) (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α) (S : Set Sphere8) :
    kernelBackground8 (fun x y => ∫ α, K α x y ∂ρ) S S = ∫ α, kernelBackground8 (K α) S S ∂ρ := by
  unfold kernelBackground8
  simp_rw [integralKernel_potential_eq K ρ g hK hg hdom S]
  apply integral_integral_swap
  have hdomi : Integrable (fun z : Sphere8 × ℝ => (1:ℝ)*g z.2)
      ((sphereProbability8.restrict S).prod ρ) := (integrable_const (1:ℝ)).mul_prod hg
  refine hdomi.mono' (integralKernel_potential_joint K hK S).aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (integralKernel_potential_abs_le K ρ g hdom S)] with z hz
  rw [Real.norm_eq_abs, one_mul]
  exact hz z.1

theorem integralKernel_pair_eq {ι : Type*} [Fintype ι]
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2))
    (hg : Integrable g ρ) (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α) (X : ι → Sphere8) :
    kernelPair8 (fun x y => ∫ α, K α x y ∂ρ) X = ∫ α, kernelPair8 (K α) X ∂ρ := by
  have hi : ∀ x y : Sphere8, Integrable (fun α => K α x y) ρ := by
    intro x y
    have hm : Measurable (fun α : ℝ => K α x y) :=
      hK.comp (measurable_id.prodMk (measurable_const (a := (x, y))))
    refine hg.mono' hm.aestronglyMeasurable ?_
    filter_upwards [hdom] with α hα
    rw [Real.norm_eq_abs]
    exact hα x y
  unfold kernelPair8
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi (X i) (X j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi (X i) (X j))]

/-- The block of a dominated parameter-integral kernel is the integral of the blocks. -/
theorem integralKernel_block_eq {ι : Type*} [Fintype ι]
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2))
    (hg : Integrable g ρ) (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α) (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (fun x y => ∫ α, K α x y ∂ρ) X S M = ∫ α, kernelBlock8 (K α) X S M ∂ρ := by
  have hpair : Integrable (fun α => kernelPair8 (K α) X) ρ := by
    unfold kernelPair8
    refine integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))
    have hm : Measurable (fun α : ℝ => K α (X i) (X j)) :=
      hK.comp (measurable_id.prodMk (measurable_const (a := (X i, X j))))
    refine hg.mono' hm.aestronglyMeasurable ?_
    filter_upwards [hdom] with α hα
    rw [Real.norm_eq_abs]
    exact hα _ _
  have hpot : ∀ x, Integrable (fun α => kernelPotential8 (K α) S x) ρ := by
    intro x
    refine hg.mono' ?_ ?_
    · exact ((integralKernel_potential_joint K hK S).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [integralKernel_potential_abs_le K ρ g hdom S] with α hα
      rw [Real.norm_eq_abs]
      exact hα x
  have hbg : Integrable (fun α => kernelBackground8 (K α) S S) ρ := by
    refine hg.mono' ?_ ?_
    · have hj := integralKernel_potential_joint K hK S
      have hm : StronglyMeasurable (fun α : ℝ => kernelBackground8 (K α) S S) := by
        have hf : StronglyMeasurable (fun q : ℝ × Sphere8 => kernelPotential8 (K q.1) S q.2) :=
          hj.comp_measurable (measurable_snd.prodMk measurable_fst)
        exact hf.integral_prod_right' (ν := sphereProbability8.restrict S)
      exact hm.aestronglyMeasurable
    · filter_upwards [integralKernel_potential_abs_le K ρ g hdom S, hdom] with α hα hα'
      rw [Real.norm_eq_abs]
      unfold kernelBackground8
      calc |∫ x in S, kernelPotential8 (K α) S x ∂sphereProbability8|
          = ‖∫ x in S, kernelPotential8 (K α) S x ∂sphereProbability8‖ := (Real.norm_eq_abs _).symm
        _ ≤ g α*(sphereProbability8.restrict S).real univ :=
            norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs]; exact hα x)
        _ ≤ g α*1 := by
            have p0 : Sphere8 := ⟨EuclideanSpace.single 0 1, by simp⟩
            have hg0 : 0 ≤ g α := (abs_nonneg _).trans (hα' p0 p0)
            apply mul_le_mul_of_nonneg_left _ hg0
            rw [measureReal_restrict_apply_univ]
            exact measureReal_le_one
        _ = g α := mul_one _
  have hsum : Integrable (fun α => ∑ i, kernelPotential8 (K α) S (X i)) ρ :=
    integrable_finsetSum _ (fun i _ => hpot (X i))
  unfold kernelBlock8
  rw [integralKernel_pair_eq K ρ g hK hg hdom X, integralKernel_background_eq K ρ g hK hg hdom S]
  simp_rw [integralKernel_potential_eq K ρ g hK hg hdom S]
  rw [← integral_finsetSum _ (fun i _ => hpot (X i))]
  have h1 : Integrable (fun α => kernelPair8 (K α) X-2*M*∑ i, kernelPotential8 (K α) S (X i)) ρ :=
    hpair.sub (hsum.const_mul _)
  have h2 : Integrable (fun α => M^2*kernelBackground8 (K α) S S) ρ := hbg.const_mul _
  have h3 : Integrable (fun α => 2*M*∑ i, kernelPotential8 (K α) S (X i)) ρ := hsum.const_mul _
  rw [integral_add h1 h2, integral_sub hpair h3, integral_const_mul, integral_const_mul]

end

theorem gaussianKernel8_row_integrable_restrict {t : ℝ} (ht : 0 ≤ t) (S : Set Sphere8) (x : Sphere8) :
    Integrable (sphereGaussianKernel8 t x) (sphereProbability8.restrict S) :=
  (sphereGaussianKernel8_integrable ht x).restrict

theorem gaussianKernelPotential8_restrict_integrable {t : ℝ} (ht : 0 ≤ t) (S : Set Sphere8) :
    Integrable (kernelPotential8 (sphereGaussianKernel8 t) S) (sphereProbability8.restrict S) := by
  have hm : StronglyMeasurable (kernelPotential8 (sphereGaussianKernel8 t) S) := by
    have hf : Continuous (fun q : Sphere8 × Sphere8 => sphereGaussianKernel8 t q.1 q.2) := by
      unfold sphereGaussianKernel8; fun_prop
    exact hf.stronglyMeasurable.integral_prod_right' (ν := sphereProbability8.restrict S)
  exact (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact gaussianKernelPotential8_abs_le ht S x)

/-- The block of `a (G_t - 1)`. -/
theorem subtractedGaussianBlock8_eq {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (a : ℝ)
    (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (fun x y => a*(sphereGaussianKernel8 t x y-1)) X S M =
      a*(kernelBlock8 (sphereGaussianKernel8 t) X S M-((Fintype.card ι:ℝ)-M*sphereProbability8.real S)^2) := by
  have hpot : ∀ x, kernelPotential8 (fun x y => a*(sphereGaussianKernel8 t x y-1)) S x =
      a*(kernelPotential8 (sphereGaussianKernel8 t) S x-sphereProbability8.real S) := by
    intro x
    unfold kernelPotential8
    rw [integral_const_mul, integral_sub (gaussianKernel8_row_integrable_restrict ht S x)
      (integrable_const 1), setIntegral_const, smul_eq_mul, mul_one]
  have hbg : kernelBackground8 (fun x y => a*(sphereGaussianKernel8 t x y-1)) S S =
      a*(kernelBackground8 (sphereGaussianKernel8 t) S S-sphereProbability8.real S*sphereProbability8.real S) := by
    unfold kernelBackground8
    simp_rw [hpot]
    rw [integral_const_mul, integral_sub (gaussianKernelPotential8_restrict_integrable ht S)
      (integrable_const _), setIntegral_const, smul_eq_mul]
  have hpair : kernelPair8 (fun x y => a*(sphereGaussianKernel8 t x y-1)) X =
      a*(kernelPair8 (sphereGaussianKernel8 t) X-(Fintype.card ι:ℝ)^2) := by
    unfold kernelPair8
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  unfold kernelBlock8
  rw [hpair, hbg]
  simp_rw [hpot]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

theorem negMacro_integrand_measurable (c p : ℝ) :
    Measurable (fun z : ℝ × (Sphere8 × Sphere8) =>
      z.1^p*(sphereGaussianKernel8 (c*z.1) z.2.1 z.2.2-1)) := by
  apply Measurable.mul (measurable_fst.pow_const p)
  apply Measurable.sub _ measurable_const
  have hf : Continuous (fun z : ℝ × (Sphere8 × Sphere8) => sphereGaussianKernel8 (c*z.1) z.2.1 z.2.2) := by
    unfold sphereGaussianKernel8; fun_prop
  exact hf.measurable

/-- The block of the subtracted macroscopic kernel is the `α^p`-integral of the Gaussian blocks
minus the squared mass defect. -/
theorem negMacroBlock8_eq {ι : Type*} [Fintype ι] {c p δ : ℝ} (hc : 0 ≤ c) (hp : -2 < p)
    (hδ : 0 ≤ δ) (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (negMacroKernel8 c p δ) X S M =
      ∫ α in Ioc 0 δ, α^p*(kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M-
        ((Fintype.card ι:ℝ)-M*sphereProbability8.real S)^2) := by
  set K : ℝ → Sphere8 → Sphere8 → ℝ := fun α x y => α^p*(sphereGaussianKernel8 (c*α) x y-1) with hKdef
  have hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2) :=
    negMacro_integrand_measurable c p
  have hg : Integrable (fun α : ℝ => (4*c)*α^(p+1)) (volume.restrict (Ioc 0 δ)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
  have hdom : ∀ᵐ α ∂(volume.restrict (Ioc 0 δ)), ∀ x y, |K α x y| ≤ (4*c)*α^(p+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα x y
    obtain ⟨h1, h2⟩ := negMacro_integrand_bounds hc hα.1 (dist_nonneg (x := x) (y := y)) p
    have he : sphereGaussianKernel8 (c*α) x y = Real.exp (-(c*α*(dist x y)^2)) := by
      unfold sphereGaussianKernel8; ring_nf
    have hd2 : (dist x y)^2 ≤ 4 := by
      have := sphere8_dist_le_two x y
      have := dist_nonneg (x := x) (y := y)
      nlinarith
    have hw : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
    have hpa : α^p*α = α^(p+1) := by rw [Real.rpow_add_one (ne_of_gt hα.1)]
    simp only [hKdef]
    rw [he, abs_of_nonpos h2]
    calc -(α^p*(Real.exp (-(c*α*(dist x y)^2))-1)) ≤ α^p*(c*α*(dist x y)^2) := by linarith
      _ ≤ α^p*(c*α*4) := by
          apply mul_le_mul_of_nonneg_left _ hw
          exact mul_le_mul_of_nonneg_left hd2 (mul_nonneg hc hα.1.le)
      _ = (4*c)*(α^p*α) := by ring
      _ = (4*c)*α^(p+1) := by rw [hpa]
  have h := integralKernel_block_eq K (volume.restrict (Ioc 0 δ)) (fun α => (4*c)*α^(p+1)) hK hg
    hdom X S M
  have hker : negMacroKernel8 c p δ = fun x y => ∫ α, K α x y ∂(volume.restrict (Ioc 0 δ)) := by
    funext x y; rfl
  rw [hker, h]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro α hα
  exact subtractedGaussianBlock8_eq (mul_nonneg hc hα.1.le) _ X S M

/-- With exact mass `#X = M σ(S)` the block of the subtracted macroscopic kernel is the
`α^p`-integral of the Gaussian blocks. -/
theorem negMacroBlock8_eq_of_mass {ι : Type*} [Fintype ι] {c p δ : ℝ} (hc : 0 ≤ c) (hp : -2 < p)
    (hδ : 0 ≤ δ) (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ)
    (hmass : (Fintype.card ι:ℝ) = M*sphereProbability8.real S) :
    kernelBlock8 (negMacroKernel8 c p δ) X S M =
      ∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M := by
  rw [negMacroBlock8_eq hc hp hδ X S M, hmass, sub_self]
  simp

/-- For `N` points against the full background, the block of the subtracted macroscopic kernel at
the density factor is `N` times the macroscopic end `∫_{(0,δ]} α^p (F_N(α) + 1) dα`. -/
theorem negMacroBlock8_config {N : ℕ} (hN : 0 < N) (Y : Configuration N) {p δ : ℝ}
    (hp : -2 < p) (hδ : 0 ≤ δ) :
    kernelBlock8 (negMacroKernel8 (sphereGaussianDensityFactor8 N) p δ) (fun i => Y i) univ N =
      (N:ℝ)*∫ α in Ioc 0 δ, α^p*(sphereGaussianCenteredScaled8 α Y+1) := by
  have hc := (sphereGaussianDensityFactor8_pos hN).le
  have hmass : (Fintype.card (Fin N):ℝ) = (N:ℝ)*sphereProbability8.real univ := by
    simp
  rw [negMacroBlock8_eq_of_mass hc hp hδ (fun i => Y i) univ N hmass, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro α hα
  dsimp only
  rw [← sphereGaussianScale8_eq_factor, gaussianKernelBlock8_config hN hα.1.le]
  ring

#print axioms integralKernel_dom_integrable
#print axioms integralKernel_potential_eq
#print axioms integralKernel_potential_joint
#print axioms integralKernel_potential_abs_le
#print axioms integralKernel_background_eq
#print axioms integralKernel_pair_eq
#print axioms integralKernel_block_eq
#print axioms gaussianKernel8_row_integrable_restrict
#print axioms gaussianKernelPotential8_restrict_integrable
#print axioms subtractedGaussianBlock8_eq
#print axioms negMacro_integrand_measurable
#print axioms negMacroBlock8_eq
#print axioms negMacroBlock8_eq_of_mass
#print axioms negMacroBlock8_config

end SphericalRiesz
