import Riesz.DiffuseGaussianBackground
import Riesz.SphereNegMacroBlock8

/-! Cauchy–Schwarz for neutralized Gaussian blocks of unions (stage NEG, second half).

The neutralized Gaussian defect of `μ - M ν` is `∫ |φ_μ - M φ_ν|² dγ` (characteristic functions
against the standard Gaussian), so for `μ = μ₁ + μ₂`, `ν = ν₁ + ν₂` the amplitude splits and
`|u₁ + u₂|² ≤ 2|u₁|² + 2|u₂|²` gives `D(μ₁+μ₂, ν₁+ν₂) ≤ 2 D(μ₁,ν₁) + 2 D(μ₂,ν₂)`.
On the sphere: the Gaussian block of `X ∪ Z` against `M σ` is at most twice the block of `X`
against `M σ|_S` plus twice the block of `Z` against `M σ|_{Sᶜ}`. With exact masses in both
parts the same holds for the subtracted macroscopic kernel `K'` (integrate against `α^p` on
`(0,δ]`), which splits the macroscopic end into the patch part and the residual part. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [FiniteDimensional ℝ E] [SecondCountableTopology E] in
theorem charFun_add_measure (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : E) :
    charFun (μ+ν) z = charFun μ z+charFun ν z := by
  have hc : Continuous (fun x : E => Complex.exp (⟪x, z⟫ * Complex.I)) := by fun_prop
  have hi : ∀ ρ : Measure E, IsFiniteMeasure ρ →
      Integrable (fun x : E => Complex.exp (⟪x, z⟫ * Complex.I)) ρ := by
    intro ρ _
    refine (integrable_const (1:ℝ)).mono' hc.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply, charFun_apply, charFun_apply,
    integral_add_measure (hi μ inferInstance) (hi ν inferInstance)]

theorem charFun_defect_normSq_integrable (r M : ℝ) (μ ν ρ : Measure E)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    Integrable (fun z => Complex.normSq (charFun μ (r • z)-(M:ℂ)*charFun ν (r • z))) ρ := by
  have hμ : StronglyMeasurable (fun z : E => charFun μ (r • z)) :=
    (stronglyMeasurable_charFun (μ := μ)).comp_measurable (by fun_prop)
  have hν : StronglyMeasurable (fun z : E => charFun ν (r • z)) :=
    (stronglyMeasurable_charFun (μ := ν)).comp_measurable (by fun_prop)
  have hm : StronglyMeasurable
      (fun z => Complex.normSq (charFun μ (r • z)-(M:ℂ)*charFun ν (r • z))) :=
    Complex.continuous_normSq.comp_stronglyMeasurable (hμ.sub (stronglyMeasurable_const.mul hν))
  refine (integrable_const ((μ.real univ+|M| * ν.real univ)^2)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  have h1 : ‖charFun μ (r • z)-(M:ℂ)*charFun ν (r • z)‖ ≤ μ.real univ+|M| * ν.real univ := by
    calc ‖charFun μ (r • z)-(M:ℂ)*charFun ν (r • z)‖
        ≤ ‖charFun μ (r • z)‖+‖(M:ℂ)*charFun ν (r • z)‖ := norm_sub_le _ _
      _ ≤ μ.real univ+|M| * ν.real univ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (norm_charFun_le _)
          (mul_le_mul_of_nonneg_left (norm_charFun_le _) (abs_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem normSq_add_le_two (u v : ℂ) :
    Complex.normSq (u+v) ≤ 2*Complex.normSq u+2*Complex.normSq v := by
  have h1 := Complex.normSq_add u v
  have h2 := Complex.normSq_sub u v
  have h3 := Complex.normSq_nonneg (u-v)
  linarith

/-- Cauchy–Schwarz for the neutralized Gaussian defect of a sum of foregrounds against a sum of
backgrounds. -/
theorem gaussianMeasureDefect_add_le {t : ℝ} (ht : 0 ≤ t) (M : ℝ) (μ₁ μ₂ ν₁ ν₂ : Measure E)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    gaussianMeasureDefect t M (μ₁+μ₂) (ν₁+ν₂) ≤
      2*gaussianMeasureDefect t M μ₁ ν₁+2*gaussianMeasureDefect t M μ₂ ν₂ := by
  rw [gaussianMeasureDefect_eq_normSq ht, gaussianMeasureDefect_eq_normSq ht,
    gaussianMeasureDefect_eq_normSq ht]
  set r := Real.sqrt (2*t)
  have h1 := charFun_defect_normSq_integrable r M μ₁ ν₁ (stdGaussian E)
  have h2 := charFun_defect_normSq_integrable r M μ₂ ν₂ (stdGaussian E)
  have h0 := charFun_defect_normSq_integrable r M (μ₁+μ₂) (ν₁+ν₂) (stdGaussian E)
  calc (∫ z, Complex.normSq (charFun (μ₁+μ₂) (r • z)-(M:ℂ)*charFun (ν₁+ν₂) (r • z))
        ∂stdGaussian E)
      ≤ ∫ z, (2*Complex.normSq (charFun μ₁ (r • z)-(M:ℂ)*charFun ν₁ (r • z))+
          2*Complex.normSq (charFun μ₂ (r • z)-(M:ℂ)*charFun ν₂ (r • z))) ∂stdGaussian E := by
        apply integral_mono h0 ((h1.const_mul 2).add (h2.const_mul 2))
        intro z
        dsimp only
        rw [charFun_add_measure, charFun_add_measure]
        have he : charFun μ₁ (r • z)+charFun μ₂ (r • z)-(M:ℂ)*(charFun ν₁ (r • z)+charFun ν₂ (r • z)) =
            (charFun μ₁ (r • z)-(M:ℂ)*charFun ν₁ (r • z))+
              (charFun μ₂ (r • z)-(M:ℂ)*charFun ν₂ (r • z)) := by ring
        rw [he]
        exact normSq_add_le_two _ _
    _ = 2*(∫ z, Complex.normSq (charFun μ₁ (r • z)-(M:ℂ)*charFun ν₁ (r • z)) ∂stdGaussian E)+
          2*∫ z, Complex.normSq (charFun μ₂ (r • z)-(M:ℂ)*charFun ν₂ (r • z)) ∂stdGaussian E := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul]

end

theorem finitePointMeasure_sum_elim {E : Type*} [MeasurableSpace E] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (x : ι → E) (y : κ → E) :
    finitePointMeasure (Sum.elim x y) = finitePointMeasure x+finitePointMeasure y := by
  unfold finitePointMeasure
  rw [Fintype.sum_sum_type]
  rfl

/-- The ambient image of the sphere probability restricted to `S`. -/
def ambientRestrictedProbability8 (S : Set Sphere8) : Measure Ambient9 :=
  (sphereProbability8.restrict S).map (fun x : Sphere8 => (x:Ambient9))

instance ambientRestrictedProbability8_finite (S : Set Sphere8) :
    IsFiniteMeasure (ambientRestrictedProbability8 S) := by
  unfold ambientRestrictedProbability8
  infer_instance

theorem ambientRestricted8_kernel_integral (t : ℝ) (S : Set Sphere8) (x : Sphere8) :
    (∫ y, gaussianKernel t (x:Ambient9) y ∂ambientRestrictedProbability8 S) =
      kernelPotential8 (sphereGaussianKernel8 t) S x := by
  rw [ambientRestrictedProbability8, integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [kernelPotential8, sphereGaussianKernel8_eq_ambient]

theorem ambientRestricted8_kernel_pair {t : ℝ} (ht : 0 ≤ t) (S : Set Sphere8) :
    gaussianMeasurePair t (ambientRestrictedProbability8 S) (ambientRestrictedProbability8 S) =
      kernelBackground8 (sphereGaussianKernel8 t) S S := by
  have hint : Integrable (fun q : Sphere8 × Sphere8 => sphereGaussianKernel8 t q.1 q.2)
      ((sphereProbability8.restrict S).prod (sphereProbability8.restrict S)) := by
    have hc : Continuous (fun q : Sphere8 × Sphere8 => sphereGaussianKernel8 t q.1 q.2) := by
      unfold sphereGaussianKernel8; fun_prop
    refine (integrable_const (1:ℝ)).mono' hc.aestronglyMeasurable ?_
    filter_upwards [] with q
    rw [Real.norm_eq_abs, sphereGaussianKernel8, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  unfold gaussianMeasurePair ambientRestrictedProbability8
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [Prod.map_fst, Prod.map_snd, ← sphereGaussianKernel8_eq_ambient]
  unfold kernelBackground8 kernelPotential8
  exact integral_prod _ hint

/-- The sphere Gaussian block is the ambient neutralized defect of the point measure against the
image of `σ|_S`. -/
theorem gaussianBlock8_eq_defect {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (sphereGaussianKernel8 t) X S M =
      gaussianMeasureDefect t M (finitePointMeasure (fun i => (X i:Ambient9)))
        (ambientRestrictedProbability8 S) := by
  rw [← diffuseGaussianDefect_eq_measureDefect ht]
  unfold kernelBlock8 kernelPair8 diffuseGaussianDefect
  simp only [← sphereGaussianKernel8_eq_ambient, ambientRestricted8_kernel_integral,
    ambientRestricted8_kernel_pair ht]

theorem ambientRestricted8_univ {S : Set Sphere8} (hS : MeasurableSet S) :
    ambientRestrictedProbability8 univ =
      ambientRestrictedProbability8 S+ambientRestrictedProbability8 Sᶜ := by
  unfold ambientRestrictedProbability8
  rw [Measure.restrict_univ, ← Measure.map_add _ _ (by fun_prop),
    Measure.restrict_add_restrict_compl hS]

/-- Cauchy–Schwarz for Gaussian blocks of a union: `X` against `M σ|_S`, `Z` against
`M σ|_{Sᶜ}`. -/
theorem gaussianBlock8_union_le {ι κ : Type*} [Fintype ι] [Fintype κ] {t : ℝ} (ht : 0 ≤ t)
    (X : ι → Sphere8) (Z : κ → Sphere8) {S : Set Sphere8} (hS : MeasurableSet S) (M : ℝ) :
    kernelBlock8 (sphereGaussianKernel8 t) (Sum.elim X Z) univ M ≤
      2*kernelBlock8 (sphereGaussianKernel8 t) X S M+
        2*kernelBlock8 (sphereGaussianKernel8 t) Z Sᶜ M := by
  have hfun : (fun i => ((Sum.elim X Z i : Sphere8) : Ambient9)) =
      Sum.elim (fun i => (X i:Ambient9)) (fun j => (Z j:Ambient9)) := by
    funext i; cases i <;> rfl
  rw [gaussianBlock8_eq_defect ht, gaussianBlock8_eq_defect ht, gaussianBlock8_eq_defect ht,
    hfun, finitePointMeasure_sum_elim, ambientRestricted8_univ hS]
  exact gaussianMeasureDefect_add_le ht M _ _ _ _

section
variable (K : ℝ → Sphere8 → Sphere8 → ℝ) (ρ : Measure ℝ) [SFinite ρ] (g : ℝ → ℝ)

/-- The blocks of a dominated parameter family are integrable in the parameter. -/
theorem integralKernel_block_integrable {ι : Type*} [Fintype ι]
    (hK : Measurable (fun z : ℝ × (Sphere8 × Sphere8) => K z.1 z.2.1 z.2.2))
    (hg : Integrable g ρ) (hdom : ∀ᵐ α ∂ρ, ∀ x y, |K α x y| ≤ g α) (X : ι → Sphere8)
    (S : Set Sphere8) (M : ℝ) :
    Integrable (fun α => kernelBlock8 (K α) X S M) ρ := by
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
  exact (hpair.sub (hsum.const_mul _)).add (hbg.const_mul _)

end

/-- With exact mass, `α ↦ α^p · block(G_{cα})` is integrable on `(0,δ]` for `p > -2`. -/
theorem negMacroGaussian_integrable {ι : Type*} [Fintype ι] {c p δ : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hδ : 0 ≤ δ) (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ)
    (hmass : (Fintype.card ι:ℝ) = M*sphereProbability8.real S) :
    IntegrableOn (fun α => α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M) (Ioc 0 δ) := by
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
  have hI := integralKernel_block_integrable K (volume.restrict (Ioc 0 δ)) (fun α => (4*c)*α^(p+1))
    hK hg hdom X S M
  refine hI.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  simp only [hKdef]
  rw [subtractedGaussianBlock8_eq (mul_nonneg hc hα.1.le) _ X S M, hmass, sub_self]
  ring

/-- Cauchy–Schwarz for the subtracted macroscopic kernel: with exact masses in both parts, the
block of `X ∪ Z` against `M σ` is at most twice the block of `X` against `M σ|_S` plus twice the
block of `Z` against `M σ|_{Sᶜ}`. -/
theorem negMacroBlock8_union_le {ι κ : Type*} [Fintype ι] [Fintype κ] {c p δ : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hδ : 0 ≤ δ) (X : ι → Sphere8) (Z : κ → Sphere8) {S : Set Sphere8}
    (hS : MeasurableSet S) (M : ℝ) (hX : (Fintype.card ι:ℝ) = M*sphereProbability8.real S)
    (hZ : (Fintype.card κ:ℝ) = M*sphereProbability8.real Sᶜ) :
    kernelBlock8 (negMacroKernel8 c p δ) (Sum.elim X Z) univ M ≤
      2*kernelBlock8 (negMacroKernel8 c p δ) X S M+
        2*kernelBlock8 (negMacroKernel8 c p δ) Z Sᶜ M := by
  have hU : (Fintype.card (ι ⊕ κ):ℝ) = M*sphereProbability8.real univ := by
    rw [Fintype.card_sum, Nat.cast_add, hX, hZ, ← mul_add,
      measureReal_add_measureReal_compl hS]
  rw [negMacroBlock8_eq_of_mass hc hp hδ _ _ _ hU, negMacroBlock8_eq_of_mass hc hp hδ _ _ _ hX,
    negMacroBlock8_eq_of_mass hc hp hδ _ _ _ hZ]
  have iX := negMacroGaussian_integrable hc hp hδ X S M hX
  have iZ := negMacroGaussian_integrable hc hp hδ Z Sᶜ M hZ
  have iU := negMacroGaussian_integrable hc hp hδ (Sum.elim X Z) univ M hU
  calc (∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) (Sum.elim X Z) univ M)
      ≤ ∫ α in Ioc 0 δ, (2*(α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M)+
          2*(α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) Z Sᶜ M)) := by
        apply setIntegral_mono_on iU ((iX.const_mul 2).add (iZ.const_mul 2)) measurableSet_Ioc
        intro α hα
        have h := gaussianBlock8_union_le (mul_nonneg hc hα.1.le) X Z hS M
        have hw : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
        have := mul_le_mul_of_nonneg_left h hw
        simp only [Pi.add_apply]
        linarith
    _ = 2*(∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S M)+
          2*∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) Z Sᶜ M := by
        rw [integral_add (iX.const_mul 2) (iZ.const_mul 2), integral_const_mul,
          integral_const_mul]

#print axioms charFun_add_measure
#print axioms charFun_defect_normSq_integrable
#print axioms normSq_add_le_two
#print axioms gaussianMeasureDefect_add_le
#print axioms finitePointMeasure_sum_elim
#print axioms ambientRestricted8_kernel_integral
#print axioms ambientRestricted8_kernel_pair
#print axioms gaussianBlock8_eq_defect
#print axioms ambientRestricted8_univ
#print axioms gaussianBlock8_union_le
#print axioms integralKernel_block_integrable
#print axioms negMacroGaussian_integrable
#print axioms negMacroBlock8_union_le

end SphericalRiesz
