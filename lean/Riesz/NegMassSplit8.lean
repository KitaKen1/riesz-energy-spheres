import Riesz.NegJointResidual8
import Riesz.NegMacroEndBounds8
import Riesz.SphereMassSplitAssembly8
import Riesz.RationalLongRangeResidual8

/-! Adding the missing points for every `N` (stage NEG, all `N`).

For `N` between rational sizes, the `M = (d m)^8 ≤ N` points of a sharp configuration are kept
(against `M σ`) and the `r = N - M` missing points are chosen one per cell of an exact-mass
stratification of the whole sphere at their own scale (against `r σ`), jointly for the `s = 4`
kernel and `λ K'(1)`.

* Cauchy–Schwarz with two densities: `D(μ₁ + μ₂, (M₁ + M₂) ν) ≤ 2 D(μ₁, M₁ ν) + 2 D(μ₂, M₂ ν)`
  (characteristic functions), hence for the blocks of `K'` with exact masses.
* Rescaling: `K'(l c, t) = l^(-(p+1)) K'(c, l t)` (substitution `β = l α`), which moves the
  density factor from `c_M` to `c_N`.
* Stratified addition: the `s = 4` block of the union is at most the block of the kept points
  plus `λ Ω`, and the `K'(1)`-block of the added points is at most `Ω` plus the `s = 4` deviation
  over `λ` (mass-split assembly `sphereFiniteBlock4_mass_assembly`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ComplexConjugate ENNReal
namespace SphericalRiesz

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Cauchy–Schwarz for the neutralized Gaussian defect with two densities. -/
theorem gaussianMeasureDefect_mass_add_le {t : ℝ} (ht : 0 ≤ t) (M₁ M₂ : ℝ)
    (μ₁ μ₂ ν : Measure E) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν] :
    gaussianMeasureDefect t (M₁+M₂) (μ₁+μ₂) ν ≤
      2*gaussianMeasureDefect t M₁ μ₁ ν+2*gaussianMeasureDefect t M₂ μ₂ ν := by
  rw [gaussianMeasureDefect_eq_normSq ht, gaussianMeasureDefect_eq_normSq ht,
    gaussianMeasureDefect_eq_normSq ht]
  set r := Real.sqrt (2*t)
  have h1 := charFun_defect_normSq_integrable r M₁ μ₁ ν (stdGaussian E)
  have h2 := charFun_defect_normSq_integrable r M₂ μ₂ ν (stdGaussian E)
  have h0 := charFun_defect_normSq_integrable r (M₁+M₂) (μ₁+μ₂) ν (stdGaussian E)
  calc (∫ z, Complex.normSq (charFun (μ₁+μ₂) (r • z)-((M₁+M₂:ℝ):ℂ)*charFun ν (r • z))
        ∂stdGaussian E)
      ≤ ∫ z, (2*Complex.normSq (charFun μ₁ (r • z)-(M₁:ℂ)*charFun ν (r • z))+
          2*Complex.normSq (charFun μ₂ (r • z)-(M₂:ℂ)*charFun ν (r • z))) ∂stdGaussian E := by
        apply integral_mono h0 ((h1.const_mul 2).add (h2.const_mul 2))
        intro z
        dsimp only
        rw [charFun_add_measure]
        have he : charFun μ₁ (r • z)+charFun μ₂ (r • z)-((M₁+M₂:ℝ):ℂ)*charFun ν (r • z) =
            (charFun μ₁ (r • z)-(M₁:ℂ)*charFun ν (r • z))+
              (charFun μ₂ (r • z)-(M₂:ℂ)*charFun ν (r • z)) := by
          push_cast
          ring
        rw [he]
        exact normSq_add_le_two _ _
    _ = 2*(∫ z, Complex.normSq (charFun μ₁ (r • z)-(M₁:ℂ)*charFun ν (r • z)) ∂stdGaussian E)+
          2*∫ z, Complex.normSq (charFun μ₂ (r • z)-(M₂:ℂ)*charFun ν (r • z)) ∂stdGaussian E := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
          integral_const_mul]

end

/-- Cauchy–Schwarz for Gaussian blocks with two densities on the whole sphere. -/
theorem gaussianBlock8_mass_union_le {ι κ : Type*} [Fintype ι] [Fintype κ] {t : ℝ} (ht : 0 ≤ t)
    (X : ι → Sphere8) (Z : κ → Sphere8) (M₁ M₂ : ℝ) :
    kernelBlock8 (sphereGaussianKernel8 t) (Sum.elim X Z) univ (M₁+M₂) ≤
      2*kernelBlock8 (sphereGaussianKernel8 t) X univ M₁+
        2*kernelBlock8 (sphereGaussianKernel8 t) Z univ M₂ := by
  have hfun : (fun i => ((Sum.elim X Z i : Sphere8) : Ambient9)) =
      Sum.elim (fun i => (X i:Ambient9)) (fun j => (Z j:Ambient9)) := by
    funext i; cases i <;> rfl
  rw [gaussianBlock8_eq_defect ht, gaussianBlock8_eq_defect ht, gaussianBlock8_eq_defect ht,
    hfun, finitePointMeasure_sum_elim]
  exact gaussianMeasureDefect_mass_add_le ht M₁ M₂ _ _ _

/-- Cauchy–Schwarz for the subtracted macroscopic kernel with two densities (exact masses). -/
theorem negMacroBlock8_mass_union_le {ι κ : Type*} [Fintype ι] [Fintype κ] {c p δ : ℝ}
    (hc : 0 ≤ c) (hp : -2 < p) (hδ : 0 ≤ δ) (X : ι → Sphere8) (Z : κ → Sphere8) (M₁ M₂ : ℝ)
    (hX : (Fintype.card ι:ℝ) = M₁) (hZ : (Fintype.card κ:ℝ) = M₂) :
    kernelBlock8 (negMacroKernel8 c p δ) (Sum.elim X Z) univ (M₁+M₂) ≤
      2*kernelBlock8 (negMacroKernel8 c p δ) X univ M₁+
        2*kernelBlock8 (negMacroKernel8 c p δ) Z univ M₂ := by
  have hu : sphereProbability8.real univ = 1 := probReal_univ
  have hX' : (Fintype.card ι:ℝ) = M₁*sphereProbability8.real univ := by rw [hu, mul_one, hX]
  have hZ' : (Fintype.card κ:ℝ) = M₂*sphereProbability8.real univ := by rw [hu, mul_one, hZ]
  have hU' : (Fintype.card (ι ⊕ κ):ℝ) = (M₁+M₂)*sphereProbability8.real univ := by
    rw [Fintype.card_sum, Nat.cast_add, hX, hZ, hu, mul_one]
  rw [negMacroBlock8_eq_of_mass hc hp hδ _ _ _ hU', negMacroBlock8_eq_of_mass hc hp hδ _ _ _ hX',
    negMacroBlock8_eq_of_mass hc hp hδ _ _ _ hZ']
  have iX := negMacroGaussian_integrable hc hp hδ X univ M₁ hX'
  have iZ := negMacroGaussian_integrable hc hp hδ Z univ M₂ hZ'
  have iU := negMacroGaussian_integrable hc hp hδ (Sum.elim X Z) univ (M₁+M₂) hU'
  calc (∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) (Sum.elim X Z) univ (M₁+M₂))
      ≤ ∫ α in Ioc 0 δ, (2*(α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X univ M₁)+
          2*(α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) Z univ M₂)) := by
        apply setIntegral_mono_on iU ((iX.const_mul 2).add (iZ.const_mul 2)) measurableSet_Ioc
        intro α hα
        have h := gaussianBlock8_mass_union_le (mul_nonneg hc hα.1.le) X Z M₁ M₂
        have hw : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
        have := mul_le_mul_of_nonneg_left h hw
        simp only [Pi.add_apply]
        linarith
    _ = 2*(∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X univ M₁)+
          2*∫ α in Ioc 0 δ, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) Z univ M₂ := by
        rw [integral_add (iX.const_mul 2) (iZ.const_mul 2), integral_const_mul,
          integral_const_mul]

/-- Rescaling the density factor of the subtracted macroscopic kernel. -/
theorem negMacroKernel8_rescale {l : ℝ} (hl : 0 < l) (c p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (x y : Sphere8) :
    negMacroKernel8 (l*c) p t x y = l^(-(p+1))*negMacroKernel8 c p (l*t) x y := by
  unfold negMacroKernel8
  have hlt : 0 ≤ l*t := mul_nonneg hl.le ht
  rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le hlt]
  set g : ℝ → ℝ := fun β => β^p*(sphereGaussianKernel8 (c*β) x y-1) with hg
  have hpt : Set.EqOn (fun α : ℝ => α^p*(sphereGaussianKernel8 (l*c*α) x y-1))
      (fun α => l^(-p)*g (l*α)) (uIcc 0 t) := by
    intro α hα
    rw [uIcc_of_le ht] at hα
    have hα0 : 0 ≤ α := hα.1
    simp only [hg]
    rw [Real.mul_rpow hl.le hα0]
    have hk : sphereGaussianKernel8 (l*c*α) x y = sphereGaussianKernel8 (c*(l*α)) x y := by
      congr 1; ring
    rw [hk]
    have hll : l^(-p)*l^p = 1 := by
      rw [← Real.rpow_add hl]
      simp
    calc α^p*(sphereGaussianKernel8 (c*(l*α)) x y-1)
        = (l^(-p)*l^p)*α^p*(sphereGaussianKernel8 (c*(l*α)) x y-1) := by rw [hll]; ring
      _ = l^(-p)*(l^p*α^p*(sphereGaussianKernel8 (c*(l*α)) x y-1)) := by ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left g hl.ne', mul_zero, smul_eq_mul]
  rw [show (-(p+1)) = -p+(-1) by ring, Real.rpow_add hl, Real.rpow_neg_one]
  ring

/-- Blocks are linear in a constant factor of the kernel. -/
theorem kernelBlock8_const_mul_kernel (k : Sphere8 → Sphere8 → ℝ) (a : ℝ) {ι : Type*}
    [Fintype ι] (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (fun x y => a*k x y) X S M = a*kernelBlock8 k X S M := by
  have hpot : ∀ T x, kernelPotential8 (fun x y => a*k x y) T x = a*kernelPotential8 k T x := by
    intro T x
    unfold kernelPotential8
    exact integral_const_mul a _
  have hbg : kernelBackground8 (fun x y => a*k x y) S S = a*kernelBackground8 k S S := by
    unfold kernelBackground8
    simp_rw [hpot]
    exact integral_const_mul a _
  have hpair : kernelPair8 (fun x y => a*k x y) X = a*kernelPair8 k X := by
    unfold kernelPair8
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  unfold kernelBlock8
  rw [hpair, hbg]
  simp only [hpot]
  rw [← Finset.mul_sum]
  ring

/-- Rescaling the density factor in the blocks of the subtracted macroscopic kernel. -/
theorem negMacroBlock8_rescale {l : ℝ} (hl : 0 < l) (c p : ℝ) {t : ℝ} (ht : 0 ≤ t) {ι : Type*}
    [Fintype ι] (X : ι → Sphere8) (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 (negMacroKernel8 (l*c) p t) X S M =
      l^(-(p+1))*kernelBlock8 (negMacroKernel8 c p (l*t)) X S M := by
  have hk : negMacroKernel8 (l*c) p t = fun x y => l^(-(p+1))*negMacroKernel8 c p (l*t) x y := by
    funext x y
    exact negMacroKernel8_rescale hl c p ht x y
  rw [hk, kernelBlock8_const_mul_kernel]

/-- Stratified addition of `r` points over the whole sphere, jointly for the `s = 4` kernel and
`λ K'(1)`. -/
theorem sphere8_neg_stratified_addition {q r : ℕ} (X : Fin q → Sphere8) (M : ℝ) (hr : 0 < r)
    (C : Fin r → Set Sphere8) (hCm : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hunion : (⋃ j, C j) = univ)
    (hmass : ∀ j, sphereProbability8 (C j) = sphereProbability8 univ/r)
    {c p lam : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hlam : 0 < lam)
    (dm : Fin r → ℝ) (hdiam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧ (∀ j, Z j ∈ C j ∧ Z j ∉ range X) ∧
      sphereFiniteBlock4 (Sum.elim X Z) univ (M+r) ≤ sphereFiniteBlock4 X univ M+
        lam*∑ j, c*(dm j)^2*((1:ℝ)^(p+2)/(p+2)) ∧
      kernelBlock8 (negMacroKernel8 c p 1) Z univ r ≤ (∑ j, c*(dm j)^2*((1:ℝ)^(p+2)/(p+2)))+
        (sphereFiniteBlock4 X univ M-sphereFiniteBlock4 (Sum.elim X Z) univ (M+r))/lam := by
  obtain ⟨Z, hZ, hZC, hjoint⟩ := sphere8_exists_stratified_residual_joint X univ univ
    MeasurableSet.univ sphereProbability8_univ_ne_zero M hr C hCm hdisj hunion hmass
    (c := 1) (p := 0) one_pos (by norm_num) (by norm_num) (le_refl 0) hc hp zero_le_one hlam.le
    dm hdiam
  have hassm := sphereFiniteBlock4_mass_assembly X Z M
  have hNE3 := residualNE_eq_kernelBlock8 (k := negMacroKernel8 c p 1) univ
    sphereProbability8_univ_ne_zero Z (r:ℝ) (by rw [probReal_univ, mul_one])
  have hpos3 : 0 ≤ kernelBlock8 (negMacroKernel8 c p 1) Z univ r :=
    negMacroBlock8_nonneg_of_mass hc hp zero_le_one Z univ (r:ℝ)
      (by rw [Fintype.card_fin, probReal_univ, mul_one])
  rw [hNE3, zero_mul, add_zero] at hjoint
  have hl3 := mul_nonneg hlam.le hpos3
  refine ⟨Z, hZ, hZC, ?_, ?_⟩
  · rw [hassm]
    linarith
  · have h : lam*kernelBlock8 (negMacroKernel8 c p 1) Z univ r ≤
        lam*(∑ j, c*(dm j)^2*((1:ℝ)^(p+2)/(p+2)))+
          (sphereFiniteBlock4 X univ M-sphereFiniteBlock4 (Sum.elim X Z) univ (M+r)) := by
      rw [hassm]
      linarith
    rw [add_div' _ _ _ hlam.ne', le_div_iff₀ hlam]
    linarith

/-- Adding `r` stratified points to a configuration of `M` points. -/
theorem configuration_add_points_neg {M N r : ℕ} (hMN : M+r = N) (hr : 0 < r)
    (Y : Configuration M) (C : Fin r → Set Sphere8) (hCm : ∀ j, MeasurableSet (C j))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hunion : (⋃ j, C j) = univ)
    (hmass : ∀ j, sphereProbability8 (C j) = sphereProbability8 univ/r)
    {c p lam : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hlam : 0 < lam)
    (dm : Fin r → ℝ) (hdiam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ Y' : Configuration N,
      energy4 Y'-(7/16:ℝ)*(N:ℝ)^2 ≤ (energy4 Y-(7/16:ℝ)*(M:ℝ)^2)+
        lam*∑ j, c*(dm j)^2*((1:ℝ)^(p+2)/(p+2)) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        kernelBlock8 (negMacroKernel8 c p t) (fun i => Y' i) univ N ≤
          2*kernelBlock8 (negMacroKernel8 c p t) (fun i => Y i) univ M+
            2*((∑ j, c*(dm j)^2*((1:ℝ)^(p+2)/(p+2)))+
              ((energy4 Y-(7/16:ℝ)*(M:ℝ)^2)-(energy4 Y'-(7/16:ℝ)*(N:ℝ)^2))/lam) := by
  classical
  subst hMN
  obtain ⟨Z, hZ, havoid, hblock, hK⟩ := sphere8_neg_stratified_addition (fun i => Y i) (M:ℝ) hr C
    hCm hdisj hunion hmass hc hp hlam dm hdiam
  have hinj : Function.Injective (Sum.elim (fun i => Y i) Z) := by
    intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Y.2 huv)
      | inr v => exact False.elim ((havoid v).2 ⟨u, huv⟩)
    | inr u =>
      cases v with
      | inl v => exact False.elim ((havoid u).2 ⟨v, huv.symm⟩)
      | inr v => exact congrArg Sum.inr (hZ huv)
  let e : Fin M ⊕ Fin r ≃ Fin (M+r) := finSumFinEquiv
  let Y' : Configuration (M+r) := ⟨(Sum.elim (fun i => Y i) Z) ∘ e.symm, hinj.comp e.symm.injective⟩
  have hYfun : (fun i => Y' i) ∘ e = Sum.elim (fun i => Y i) Z := by
    funext u
    simp [Y']
  have hcast : ((M+r:ℕ):ℝ) = (M:ℝ)+r := by push_cast; ring
  have hE' : energy4 Y'-(7/16:ℝ)*((M+r:ℕ):ℝ)^2 =
      sphereFiniteBlock4 (Sum.elim (fun i => Y i) Z) univ ((M:ℝ)+r) := by
    rw [← sphereFiniteBlock4_eq_energy4 Y', ← hcast]
    have h := sphereFiniteBlock4_reindex e (fun i => Y' i) univ ((M+r:ℕ):ℝ)
    rw [hYfun] at h
    exact h.symm
  have hE : energy4 Y-(7/16:ℝ)*(M:ℝ)^2 = sphereFiniteBlock4 (fun i => Y i) univ (M:ℝ) :=
    (sphereFiniteBlock4_eq_energy4 Y).symm
  refine ⟨Y', ?_, fun t ht ht1 => ?_⟩
  · rw [hE', hE]
    exact hblock
  · have hL' : kernelBlock8 (negMacroKernel8 c p t) (fun i => Y' i) univ ((M+r:ℕ):ℝ) =
        kernelBlock8 (negMacroKernel8 c p t) (Sum.elim (fun i => Y i) Z) univ ((M:ℝ)+r) := by
      rw [← hcast]
      have h := kernelBlock8_reindex (negMacroKernel8 c p t) e (fun i => Y' i) univ ((M+r:ℕ):ℝ)
      rw [hYfun] at h
      exact h.symm
    have hU := negMacroBlock8_mass_union_le hc hp ht (fun i => Y i) Z (M:ℝ) (r:ℝ)
      (by rw [Fintype.card_fin]) (by rw [Fintype.card_fin])
    have hmono := negMacroBlock8_mono_cutoff hc hp ht ht1 Z univ (r:ℝ)
      (by rw [Fintype.card_fin, probReal_univ, mul_one])
    rw [hL', hE', hE]
    linarith

#print axioms gaussianMeasureDefect_mass_add_le
#print axioms gaussianBlock8_mass_union_le
#print axioms negMacroBlock8_mass_union_le
#print axioms negMacroKernel8_rescale
#print axioms kernelBlock8_const_mul_kernel
#print axioms negMacroBlock8_rescale
#print axioms sphere8_neg_stratified_addition
#print axioms configuration_add_points_neg

end SphericalRiesz
