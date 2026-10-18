import Riesz.LeechNegBlock24

/-! Block configurations on S²⁴ with three Gaussian controls (stage LOG of the S²⁴ chain).

The module has three parts.

* `LeechUniversalJoint24`: one joint stratified choice of residual points for the subtracted
  macroscopic kernel, the short-range kernel with the foreground cross pairs, and one Gaussian
  window.
* `LeechShortRangeF24`: the short-range cost of a separated family of fourteenth-order patch
  nodes.
* `LeechLogBlock24`: for a tolerance index `L ≥ 2` and every large refinement, an actual
  configuration of `(d m)²⁴` points with a Gaussian window, a small macroscopic end at a
  negative exponent and a bounded short-range cost.  The short-range kernel enters the joint
  choice with the weight `L⁻²`, so that its centering term of size `N` stays below `N C/L²`.

No energy statement is made here and no Gaussian certificate is used.  The stratification of the
residual regions is the hypothesis `LeechResidualStratifiable24`, which is proved in
`Riesz.SphereStratification24`. -/

section

/-! One joint residual choice on S²⁴ for the subtracted macroscopic kernel, the short-range tail
and one Gaussian window.

The residual region is the union of measurable pairwise disjoint cells of probability `1/N` with
diameters `d_j`.  One point is chosen in every cell, injectively and away from the foreground
points, so that the weighted sum of three quantities is at most `n w₃ + c_N/(p'+2) Σ_j d_j²`:

* the neutralized energy of the subtracted macroscopic kernel `K'_{p'}` (which is nonnegative);
* the short-range kernel `T_p`, with the residual/foreground cross pairs, centered by the bound
  `(2M+n)/(11-p)`;
* one Gaussian window among the residual points, centered by the bound `n N B(t₀)`.

The same choice therefore serves the macroscopic end, the tail and the window of a block.  No
foreground estimate, configuration or attaining sequence is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

/-- One joint residual choice for the subtracted macroscopic kernel, the short-range kernel and
one Gaussian window on S²⁴. -/
theorem exists_leech_universal_joint_residual24 {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {p' p t₀ w₂ w₃ : ℝ} (hp' : -2 < p') (hp0 : -1 ≤ p) (hp : p < 11) (ht₀ : 0 ≤ t₀)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    {ι : Type*} [Fintype ι] (X : ι → SphereD 24)
    (C : Fin n → Set (SphereD 24)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹)
    (dm : Fin n → ℝ) (hdm : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ z : Fin n → SphereD 24, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧
      (∀ j, z j ∉ range X) ∧
      0 ≤ residualNeutralizedEnergy (sphereRestrictedProbability24 (⋃ j, C j))
        (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1) (fun _ => 0) z ∧
      residualNeutralizedEnergy (sphereRestrictedProbability24 (⋃ j, C j))
          (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1) (fun _ => 0) z+
        w₂*(residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X z-
          (2*(Fintype.card ι:ℝ)+(n:ℝ))/(11-p))+
        w₃*(cellPairSum (sphereGaussianKernel24 t₀) z-
          (n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀)) ≤
      (n:ℝ)*w₃+sphereGaussianDensityFactor24 N/(p'+2)*∑ j, (dm j)^2 := by
  classical
  have hc : 0 < sphereGaussianDensityFactor24 N := sphereGaussianDensityFactor24_pos hN
  have hRm : MeasurableSet (⋃ j, C j) := MeasurableSet.iUnion hCm
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (N:ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h11 : 0 < 11-p := by linarith
  have hnne : (n:ℝ) ≠ 0 := hnR.ne'
  have hNne : (N:ℝ) ≠ 0 := hNR.ne'
  have hp2 : 0 < p'+2 := by linarith
  have hσR : (sphereProbabilityD 24) (⋃ j, C j) = (n:ℝ≥0∞)*(N:ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hR0 : (sphereProbabilityD 24) (⋃ j, C j) ≠ 0 := by
    rw [hσR]
    exact mul_ne_zero hn0 (ENNReal.inv_ne_zero.mpr hNt)
  have hinv : ((sphereProbabilityD 24) (⋃ j, C j))⁻¹ = (N:ℝ≥0∞)*(n:ℝ≥0∞)⁻¹ := by
    rw [hσR, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), inv_inv, mul_comm]
  have htoReal : (((sphereProbabilityD 24) (⋃ j, C j))⁻¹).toReal = (N:ℝ)/(n:ℝ) := by
    rw [hinv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  -- the residual probability measure, as a variable with its defining equation
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure (SphereD 24), μ = sphereRestrictedProbability24 (⋃ j, C j) :=
    ⟨_, rfl⟩
  have hμP : IsProbabilityMeasure μ := by
    rw [hμdef]
    exact sphereRestrictedProbability24_probability _ hR0
  have hμA : NullSingletonClass μ := by
    rw [hμdef]
    infer_instance
  have hμC : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹ := by
    intro j
    have hsub : C j ∩ ⋃ i, C i = C j := inter_eq_left.mpr (subset_iUnion C j)
    rw [hμdef]
    simp only [sphereRestrictedProbability24, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j), hsub, hCmass j, hinv, mul_comm (N:ℝ≥0∞) _, mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, mul_one]
  have hcover : μ (⋃ j, C j)ᶜ = 0 := by
    rw [hμdef]
    exact sphereRestrictedProbability24_compl _ hRm
  have hB : μ (range X) = 0 := (finite_range X).measure_zero μ
  have hint_eq : ∀ f : SphereD 24 → ℝ,
      (∫ y, f y ∂μ) = (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, f y ∂(sphereProbabilityD 24) := by
    intro f
    rw [hμdef]
    simp only [sphereRestrictedProbability24]
    rw [integral_smul_measure, smul_eq_mul, htoReal]
  have hmassR : (n:ℝ) = (N:ℝ)*(sphereProbabilityD 24).real (⋃ j, C j) := by
    rw [Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast]
    field_simp
  -- integrability of the three kernels
  have hKprod : Integrable (Function.uncurry
      (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1)) (μ.prod μ) :=
    negMacroKernel24_integrable hc.le hp' zero_le_one (μ.prod μ)
  have hKk : ∀ x, Integrable (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x) μ :=
    fun x => negMacroKernel24_row_integrable hc.le hp' zero_le_one x μ
  have hKV : Integrable (residualRowPotential μ
      (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1)) μ := hKprod.integral_prod_left
  have hTk : ∀ x, Integrable (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x) μ := by
    intro x
    rw [hμdef]
    exact shortRangeKernel24_restricted_integrable hc hp _ x
  have hTV : Integrable (residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)) μ := by
    rw [hμdef]
    exact shortRangeKernel24_restricted_rowPotential_integrable hc hp _ hR0
  have hTprod : Integrable (Function.uncurry
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry
        (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)) (μ.prod μ) :=
      (shortRangeKernel24_measurable (sphereGaussianDensityFactor24 N) p).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).mpr ⟨Filter.Eventually.of_forall fun x => hTk x, ?_⟩
    refine hTV.congr (Filter.Eventually.of_forall fun x => ?_)
    unfold residualRowPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y =
      ‖shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y‖
    rw [Real.norm_eq_abs, abs_of_nonneg (shortRangeKernel24_nonneg _ _ _ _)]
  have hGprod : Integrable (Function.uncurry (sphereGaussianKernel24 t₀)) (μ.prod μ) :=
    sphereGaussianKernel24_integrable_finite ht₀ (μ.prod μ)
  have hGk : ∀ x, Integrable (sphereGaussianKernel24 t₀ x) μ :=
    fun x => sphereGaussianKernel24_row_integrable_finite ht₀ x μ
  have hGV : Integrable (residualRowPotential μ (sphereGaussianKernel24 t₀)) μ :=
    hGprod.integral_prod_left
  have hL₂ : Integrable (residualCrossLinear μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n) μ :=
    residualCrossLinear_integrable (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)
      (shortRangeKernel24_symm _ p) X hTk hTV n
  have hL₃ : Integrable (residualCrossLinear μ (sphereGaussianKernel24 t₀)
      (Fin.elim0 : Fin 0 → SphereD 24) n) μ :=
    residualCrossLinear_integrable (sphereGaussianKernel24 t₀) (sphereGaussianKernel24_comm t₀)
      (Fin.elim0 : Fin 0 → SphereD 24) hGk hGV n
  have hk₁₂ : ∀ x, Integrable (fun y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
      w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y) μ :=
    fun x => (hKk x).add ((hTk x).const_mul w₂)
  have hV₁₂ : Integrable (residualRowPotential μ
      (fun x y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
        w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y)) μ :=
    residualRowPotential_add_smul_integrable _ _ w₂ hKk hTk hKV hTV
  have hL₁₂ : Integrable (fun x => (0:ℝ)+w₂*residualCrossLinear μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n x) μ :=
    (integrable_zero _ _ _).add (hL₂.const_mul w₂)
  -- the joint choice
  obtain ⟨z, hinj, hzC, hzB, hne⟩ := exists_stratified_residualNeutralizedEnergy_le_diag μ
    (fun x y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
      w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y+
      w₃*sphereGaussianKernel24 t₀ x y)
    (fun x => (0:ℝ)+w₂*residualCrossLinear μ
        (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n x+
      w₃*residualCrossLinear μ (sphereGaussianKernel24 t₀)
        (Fin.elim0 : Fin 0 → SphereD 24) n x)
    (fun x y => show negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
        w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y+
        w₃*sphereGaussianKernel24 t₀ x y =
        negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 y x+
          w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p y x+
          w₃*sphereGaussianKernel24 t₀ y x by
      rw [negMacroKernel24_symm _ p' 1 x y, shortRangeKernel24_symm _ p x y,
        sphereGaussianKernel24_comm t₀ x y])
    (0+w₂*0+w₃*1)
    (fun x => show negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x x+
        w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x x+
        w₃*sphereGaussianKernel24 t₀ x x = 0+w₂*0+w₃*1 by
      rw [negMacroKernel24_self, shortRangeKernel24_self _ hp0, sphereGaussianKernel24_self])
    hn C hCm hCd hcover hμC
    (fun j => w₃+sphereGaussianDensityFactor24 N/(p'+2)*(dm j)^2)
    (fun j x hx y hy => show 0+w₂*0+w₃*1-
        (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
          w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y+
          w₃*sphereGaussianKernel24 t₀ x y) ≤
        w₃+sphereGaussianDensityFactor24 N/(p'+2)*(dm j)^2 by
      have hvar := negMacroKernel24_variance hc.le hp' zero_le_one x y
      rw [Real.one_rpow] at hvar
      have hd := hdm j x hx y hy
      have hd0 : 0 ≤ dist x y := dist_nonneg
      have hd2 : (dist x y)^2 ≤ (dm j)^2 := pow_le_pow_left₀ hd0 hd 2
      have hG := sphereGaussianKernel24_nonneg t₀ x y
      have hT := shortRangeKernel24_nonneg (sphereGaussianDensityFactor24 N) p x y
      have hcp : 0 ≤ sphereGaussianDensityFactor24 N/(p'+2) := div_nonneg hc.le hp2.le
      have h1 : sphereGaussianDensityFactor24 N*(dist x y)^2*(1/(p'+2)) ≤
          sphereGaussianDensityFactor24 N/(p'+2)*(dm j)^2 := by
        calc sphereGaussianDensityFactor24 N*(dist x y)^2*(1/(p'+2))
            = sphereGaussianDensityFactor24 N/(p'+2)*(dist x y)^2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hd2 hcp
      have h2 : 0 ≤ w₃*sphereGaussianKernel24 t₀ x y := mul_nonneg hw₃ hG
      have h3 : 0 ≤ w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y :=
        mul_nonneg hw₂ hT
      linarith)
    (fun x => (hk₁₂ x).add ((hGk x).const_mul w₃))
    (residualRowPotential_add_smul_integrable _ _ w₃ hk₁₂ hGk hV₁₂ hGV)
    ((hKprod.add (hTprod.const_mul w₂)).add (hGprod.const_mul w₃))
    (hL₁₂.add (hL₃.const_mul w₃)) (range X) hB
  have hKnonneg := negMacro_residualNeutralizedEnergy_nonneg hc.le hp' zero_le_one z (⋃ j, C j)
    hR0 hmassR
  rw [← hμdef] at hKnonneg
  refine ⟨z, hinj, hzC, hzB, ?_, ?_⟩
  · rw [← hμdef]
    exact hKnonneg
  have hsplit₁ : residualNeutralizedEnergy μ
      (fun x y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
        w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y+
        w₃*sphereGaussianKernel24 t₀ x y)
      (fun x => (0:ℝ)+w₂*residualCrossLinear μ
          (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n x+
        w₃*residualCrossLinear μ (sphereGaussianKernel24 t₀)
          (Fin.elim0 : Fin 0 → SphereD 24) n x) z =
      residualNeutralizedEnergy μ
        (fun x y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
          w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y)
        (fun x => (0:ℝ)+w₂*residualCrossLinear μ
          (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n x) z+
      w₃*residualNeutralizedEnergy μ (sphereGaussianKernel24 t₀)
        (residualCrossLinear μ (sphereGaussianKernel24 t₀)
          (Fin.elim0 : Fin 0 → SphereD 24) n) z :=
    residualNeutralizedEnergy_add_smul
      (fun x y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
        w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y)
      (sphereGaussianKernel24 t₀)
      (fun x => (0:ℝ)+w₂*residualCrossLinear μ
        (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n x)
      (residualCrossLinear μ (sphereGaussianKernel24 t₀) (Fin.elim0 : Fin 0 → SphereD 24) n)
      w₃ hk₁₂ hGk hV₁₂ hGV hL₁₂ hL₃ z
  have hsplit₂ : residualNeutralizedEnergy μ
      (fun x y => negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1 x y+
        w₂*shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y)
      (fun x => (0:ℝ)+w₂*residualCrossLinear μ
        (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n x) z =
      residualNeutralizedEnergy μ (negMacroKernel24 (sphereGaussianDensityFactor24 N) p' 1)
        (fun _ => 0) z+
      w₂*residualNeutralizedEnergy μ (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p)
        (residualCrossLinear μ (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X n) z :=
    residualNeutralizedEnergy_add_smul _ _ (fun _ => (0:ℝ)) _ w₂ hKk hTk hKV hTV
      (integrable_zero _ _ _) hL₂ z
  have hcrossT := residualNeutralizedEnergy_crossLinear
    (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) (shortRangeKernel24_symm _ p) X
    hTk hTV z
  have hcrossG := residualNeutralizedEnergy_crossLinear (sphereGaussianKernel24 t₀)
    (sphereGaussianKernel24_comm t₀) (Fin.elim0 : Fin 0 → SphereD 24) hGk hGV z
  rw [hsplit₁, hsplit₂, hcrossT, hcrossG] at hne
  -- the short-range kernel: bounded smooth mean
  have hTrow : ∀ x, (n:ℝ)*residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) x ≤ 1/(11-p) := by
    intro x
    have h := shortRangeKernel24_cell_rows_le hN hp C hCm hCd hCmass x
    rw [sphereRestrictedProbability24_sum_integral C hCm hCd hCmass
      (shortRangeKernel24_row_integrable (sphereGaussianScale24_pos hN zero_lt_one) hp x)] at h
    unfold residualRowPotential
    rw [hint_eq]
    calc (n:ℝ)*((N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y ∂(sphereProbabilityD 24))
        = (N:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel24 (sphereGaussianDensityFactor24 N) p x y
            ∂(sphereProbabilityD 24) := by field_simp
      _ ≤ 1/(11-p) := h
  have hTU : ∀ x, residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) x ≤ 1/((n:ℝ)*(11-p)) := by
    intro x
    have h := hTrow x
    rw [le_div_iff₀ (mul_pos hnR h11)]
    calc _ = ((n:ℝ)*residualRowPotential μ
          (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) x)*(11-p) := by ring
      _ ≤ 1/(11-p)*(11-p) := mul_le_mul_of_nonneg_right h h11.le
      _ = 1 := by field_simp
  have hTbg : residualBackground μ (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) ≤
      1/((n:ℝ)*(11-p)) := by
    unfold residualBackground
    calc _ ≤ ∫ _x, 1/((n:ℝ)*(11-p)) ∂μ := integral_mono hTV (integrable_const _) hTU
      _ = _ := by simp
  have hTsum : (n:ℝ)*(∑ i, residualRowPotential μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) (X i)) ≤
      (Fintype.card ι:ℝ)/(11-p) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _i : ι, 1/(11-p) := Finset.sum_le_sum fun i _ => hTrow (X i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hTbgn : (n:ℝ)^2*residualBackground μ
      (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) ≤ (n:ℝ)/(11-p) := by
    calc _ ≤ (n:ℝ)^2*(1/((n:ℝ)*(11-p))) := mul_le_mul_of_nonneg_left hTbg (by positivity)
      _ = _ := by field_simp
  have hc₂ : residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X z-
      (2*(Fintype.card ι:ℝ)+(n:ℝ))/(11-p) ≤
      residualCentered μ (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X z := by
    rw [residualCentered_eq_crossSum]
    have he : (2*(Fintype.card ι:ℝ)+(n:ℝ))/(11-p) =
        2*((Fintype.card ι:ℝ)/(11-p))+(n:ℝ)/(11-p) := by ring
    rw [he]
    linarith
  -- the Gaussian window: bounded smooth mean
  have hGU : ∀ x, residualRowPotential μ (sphereGaussianKernel24 t₀) x ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀ := by
    intro x
    unfold residualRowPotential
    rw [hint_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∫ y in ⋃ j, C j, sphereGaussianKernel24 t₀ x y ∂(sphereProbabilityD 24))
        ≤ ∫ y, sphereGaussianKernel24 t₀ x y ∂(sphereProbabilityD 24) :=
          setIntegral_le_integral (sphereGaussianKernel24_integrable ht₀ x)
            (Filter.Eventually.of_forall fun y => sphereGaussianKernel24_nonneg _ _ _)
      _ = sphereGaussianBackground24 t₀ := (sphereGaussianBackground24_eq_potential ht₀ x).symm
  have hGbg : residualBackground μ (sphereGaussianKernel24 t₀) ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀ := by
    unfold residualBackground
    calc _ ≤ ∫ _x, (N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀ ∂μ :=
          integral_mono hGV (integrable_const _) hGU
      _ = _ := by simp
  have hc₃ : cellPairSum (sphereGaussianKernel24 t₀) z-
      (n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀) ≤
      residualCentered μ (sphereGaussianKernel24 t₀) (Fin.elim0 : Fin 0 → SphereD 24) z := by
    have hbgn : (n:ℝ)^2*residualBackground μ (sphereGaussianKernel24 t₀) ≤
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀) := by
      calc _ ≤ (n:ℝ)^2*((N:ℝ)/(n:ℝ)*sphereGaussianBackground24 t₀) :=
            mul_le_mul_of_nonneg_left hGbg (by positivity)
        _ = _ := by field_simp
    unfold residualCentered residualPairEnergy cellPairSum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero, sub_zero,
      add_zero]
    linarith
  have hm₂ := mul_le_mul_of_nonneg_left hc₂ hw₂
  have hm₃ := mul_le_mul_of_nonneg_left hc₃ hw₃
  have hsum : (∑ j, (w₃+sphereGaussianDensityFactor24 N/(p'+2)*(dm j)^2)) =
      (n:ℝ)*w₃+sphereGaussianDensityFactor24 N/(p'+2)*∑ j, (dm j)^2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum] at hne
  rw [← hμdef]
  linarith

end SphericalRiesz
end
end

section

/-! Short-range cost of a fourteenth-order foreground family of one common scale.

Inside one patch the cost is the computed rational-density budget of the fourteenth-order nodes.
Two nodes of different patches are separated by a fixed positive distance `δ`, and the
short-range kernel at separation `δ` is at most `e^{-cδ²/2} Γ(p+1) (2/(cδ²))^(p+1)`.  Hence

`Σ_{fg,fg} T ≤ M B + M² e^{-cδ²/2} Γ(p+1) (2/(cδ²))^(p+1)`,  `M = K n²⁴`.

This is the order-fourteen counterpart of `leechPatchFamily_shortRange_le`.  The residual points
and the full configuration are not part of this statement. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Short-range cost of a separated fourteenth-order foreground family. -/
theorem leechPatchFamily_shortRange_leF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m) (p : ℝ), -1 < p →
      (∑ q, ∑ q', shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p
          (leechFamilyNodesF24 P (a*m) hn q) (leechFamilyNodesF24 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^24*
          leechGaussianTailBudget24
            (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) p+
        ((K:ℝ)*((a*m:ℕ):ℝ)^24)^2*
          separatedShortRangeBound24 (sphereGaussianDensityFactor24 ((d*m)^24)) p δ := by
  classical
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaLeechFourteenth24_rational_density_budget
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn p hp
  have hc0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24) :=
    sphereGaussianDensityFactor24_pos (by positivity)
  set c := sphereGaussianDensityFactor24 ((d*m)^24) with hc
  set τ := separatedShortRangeBound24 c p δ with hτ
  have hτ0 : 0 ≤ τ := separatedShortRangeBound24_nonneg hc0 hp hδ
  set B := leechGaussianTailBudget24
    (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) p with hB
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hcardNodes : (Fintype.card (Fin 24 → FourteenNodeIndex (a*m)) : ℝ) = n^24 := by
    rw [fourteenCubeNode_card 24 (a*m) hn]
    exact Nat.cast_pow _ _
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, shortRangeKernel24 c p
      (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P i) (a*m) hn w)) ≤
      n^24*B := by
    intro i
    have h := hb (P i).g (P i).v (P i).c (hv i) (P i).c_mem (P i).ε (P i).ε_pos (hε i)
      (P i).small leechUnitDensityRadius24 p leechUnitDensityRadius24_pos hp a d m ha hd hm
      (hratio i) hn
    have h' := (div_le_iff₀ (pow_pos hn0 24)).mp h
    calc _ ≤ B*n^24 := h'
      _ = _ := mul_comm _ _
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, shortRangeKernel24 c p
      (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P j) (a*m) hn w) ≤ τ :=
    fun i j hij u w => shortRangeKernel24_le_of_separated hc0 hp hδ
      (hsep i j hij _ (smallLeechPatchNodesF24_mem (P i) _ hn u) _
        (smallLeechPatchNodesF24_mem (P j) _ hn w))
  have hrow : ∀ i u, (∑ j, ∑ w, shortRangeKernel24 c p
      (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P j) (a*m) hn w)) ≤
      (∑ w, shortRangeKernel24 c p (smallLeechPatchNodesF24 (P i) (a*m) hn u)
        (smallLeechPatchNodesF24 (P i) (a*m) hn w))+(K:ℝ)*(n^24*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, shortRangeKernel24 c p
        (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P j) (a*m) hn w)) ≤
        (if j = i then ∑ w, shortRangeKernel24 c p (smallLeechPatchNodesF24 (P i) (a*m) hn u)
          (smallLeechPatchNodesF24 (P i) (a*m) hn w) else 0)+n^24*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 24).le hτ0)
      · rw [ite_eq_right hji, zero_add]
        calc _ ≤ ∑ _w : Fin 24 → FourteenNodeIndex (a*m), τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = n^24*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, shortRangeKernel24 c p
            (smallLeechPatchNodesF24 (P i) (a*m) hn u)
            (smallLeechPatchNodesF24 (P i) (a*m) hn w) else 0)+n^24*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- all pairs
  have hsplit : (∑ q, ∑ q', shortRangeKernel24 c p
      (leechFamilyNodesF24 P (a*m) hn q) (leechFamilyNodesF24 P (a*m) hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, shortRangeKernel24 c p
        (smallLeechPatchNodesF24 (P i) (a*m) hn u) (smallLeechPatchNodesF24 (P j) (a*m) hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, shortRangeKernel24 c p (smallLeechPatchNodesF24 (P i) (a*m) hn u)
          (smallLeechPatchNodesF24 (P i) (a*m) hn w))+(K:ℝ)*(n^24*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, shortRangeKernel24 c p (smallLeechPatchNodesF24 (P i) (a*m) hn u)
          (smallLeechPatchNodesF24 (P i) (a*m) hn w))+(K:ℝ)*(n^24*((K:ℝ)*(n^24*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ ≤ (∑ _i : Fin K, n^24*B)+(K:ℝ)*(n^24*((K:ℝ)*(n^24*τ))) :=
      add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end SphericalRiesz
end
end

section

/-! Block configurations on S²⁴ with three Gaussian controls (stage LOG).

For a tolerance index `L ≥ 2` take a near-full rational Leech patch family of residual fraction
below `L⁻¹⁴`, the fourteenth-order nodes of a refinement `m`, and one residual point per cell of
an exact-mass stratification of the complement, chosen jointly for the subtracted macroscopic
kernel, the short-range kernel with weight `L⁻²` and one Gaussian window.  The resulting
configuration of `N = (d m)²⁴` points satisfies

* the window `Full_α ≤ (1+1/L)(Θ(α(1-1/L)²)+2/L)+(1+L) C/L²` for every `α ≥ 1/L`,
* the macroscopic end `∫_{(0,w]} α^(s/2-1)(F+1) ≤ 2(A w^(s/2+2)/(s/2+2)+w^(s/2+1)/(L(s/2+1)))+2C/L²`
  for every cutoff `0 < w ≤ 1`,
* the short-range cost `Σ T_p/N ≤ D`,

with `A`, `C`, `D` independent of `L` and of the refinement.  The weight `L⁻²` keeps the centering
term `(2M+n)/(11-p) = O(N)` of the short-range kernel below `N C/L²`, so that the window and the
macroscopic end stay as small as in the negative-exponent block, while the cost itself is at most
`N C`.  The stratification of the residual regions is the hypothesis
`LeechResidualStratifiable24`.  No energy statement is made here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

/-- Residual constant of the logarithmic blocks. -/
def leechLogBlockConst24 (s p Bst : ℝ) : ℝ := leechNegBlockConst24 s Bst+3/(11-p)

/-- Short-range constant of the logarithmic blocks. -/
def leechLogBlockTailConst24 (s p Bst : ℝ) : ℝ :=
  leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) p+1+
    leechLogBlockConst24 s p Bst

/-- One block with three controls: explicit conditions on the family, the refinement and the
residual cells give an actual configuration with a Gaussian window, a small macroscopic end and
a bounded short-range cost. -/
theorem exists_leech_log_block_configuration24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {p : ℝ}
    (hp0 : 0 ≤ p) (hp11 : p < 11) {L : ℕ} (hL : 2 ≤ L) {Bst : ℝ} (hBst : 0 ≤ Bst) :
    ∃ ρ > 0, ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (a d : ℕ) {δ : ℝ},
      0 < a → 0 < d → 0 < δ →
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      ∀ m : ℕ, 0 < m → 48 ≤ a*m →
      2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) ≤ 1/(L:ℝ) →
      (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) →
      leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) ≤ 1/(L:ℝ) →
      (((d*m)^24:ℕ):ℝ)*separatedShortRangeBound24
        (sphereGaussianDensityFactor24 ((d*m)^24)) p δ ≤ 1 →
      ∀ {n : ℕ}, 0 < n →
      Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m)))+n = (d*m)^24 →
      (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ) →
      ∀ (C : Fin n → Set (SphereD 24)) (dm : Fin n → ℝ), (∀ i, MeasurableSet (C i)) →
      Pairwise (fun i j => Disjoint (C i) (C j)) →
      (∀ i, (sphereProbabilityD 24) (C i) = (((d*m)^24:ℕ):ℝ≥0∞)⁻¹) →
      (⋃ j, C j) = (leechFamilyUnion24 P)ᶜ →
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) →
      (∑ j, sphereGaussianDensityFactor24 ((d*m)^24)*(dm j)^2) ≤
        Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) →
      ∃ X : ConfigurationD 24 ((d*m)^24),
        (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
            (1+(L:ℝ))*(leechLogBlockConst24 s p Bst/(L:ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
            2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(leechLogBlockConst24 s p Bst/(L:ℝ)^2)) ∧
        cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p) X/
          (((d*m)^24:ℕ):ℝ) ≤ leechLogBlockTailConst24 s p Bst := by
  have hp : -2 < s/2-1 := by linarith
  have hp2 : 0 < s/2+1 := by linarith
  have hT1 : -1 < p := by linarith
  have hT0 : -1 ≤ p := by linarith
  have h11 : 0 < 11-p := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) < 1 := by
    rw [div_lt_one hL0]
    linarith
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hκ := leechConservativeRowFactor24_pos
  obtain ⟨ρ₁,hρ₁,_,hmacro⟩ := leechPatchFamily_mixed_defect_macroF
  obtain ⟨ρ₂,hρ₂,_,htail⟩ := leechPatchFamily_shortRange_leF
  obtain ⟨ρ₃,hρ₃,_,hwindow⟩ := leechPatchFamily_gaussianWindow_leF hη hη1
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), ?_⟩
  intro K P a d δ ha hd hδ hv hε hratio hdisj hsep m hm hn he4 he5 he6 he3 n hnpos hcard hnfrac
    C dm hCm hCd hCmass hCu hdiam hstrat
  have hv₁ : ∀ i, ‖(P i).v‖ ≤ ρ₁ := fun i => (hv i).trans (min_le_left _ _)
  have hv₂ : ∀ i, ‖(P i).v‖ ≤ ρ₂ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hv₃ : ∀ i, ‖(P i).v‖ ≤ ρ₃ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε₁ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₁ := fun i =>
    (hε i).trans (min_le_left _ _)
  have hε₂ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₂ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₃ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₃ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (0:ℝ) < (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hNpos
  have hc0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24) := sphereGaussianDensityFactor24_pos hNpos
  have ht₀ : 0 ≤ sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)) :=
    (sphereGaussianScale24_pos hNpos hη).le
  have hw₂ : (0:ℝ) ≤ 1/(L:ℝ)^2 := one_div_nonneg.mpr (pow_pos hL0 2).le
  -- one joint residual choice for the macroscopic kernel, the tail and the window
  obtain ⟨z, hz, _, havoid, hK0, hjoint⟩ := exists_leech_universal_joint_residual24 hNpos hnpos
    hp hT0 hp11 ht₀ hw₂ (zero_le_one : (0:ℝ) ≤ 1) (leechFamilyNodesF24 P (a*m) hn) C hCm hCd
    hCmass dm hdiam
  rw [show s/2-1+2 = s/2+1 by ring] at hjoint
  -- cardinalities as real numbers
  have hM0 : (0:ℝ) ≤ ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hMn : ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hcard
  have hn0R : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hMN : ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) ≤
      (((d*m)^24:ℕ):ℝ) := by linarith
  have hMK : ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) =
      (K:ℝ)*((a*m:ℕ):ℝ)^24 := by
    rw [Fintype.card_prod, Fintype.card_fin, fourteenCubeNode_card 24 (a*m) hn, Nat.cast_mul,
      Nat.cast_pow]
  -- the residual quantities are at most `N C/L²`
  have hBcap : (((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))) ≤ (L:ℝ)^12 := by
    have h := sphereGaussianBackground24_scaled_cap hNpos hη
    have e : ((1/(L:ℝ))^12)⁻¹ = (L:ℝ)^12 := by rw [one_div, inv_pow, inv_inv]
    rw [e] at h
    exact h
  have hNB0 : 0 ≤ (((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))) :=
    mul_nonneg hNR.le (sphereGaussianBackground24_nonneg _)
  have hsumdm : sphereGaussianDensityFactor24 ((d*m)^24)/(s/2+1)*∑ j, (dm j)^2 ≤
      (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ))/(s/2+1) := by
    rw [div_mul_eq_mul_div, Finset.mul_sum]
    exact div_le_div_of_nonneg_right hstrat hp2.le
  have hLpow : 1/(L:ℝ)^14 ≤ 1/(L:ℝ)^2 :=
    one_div_le_one_div_of_le (pow_pos hL0 2) (pow_le_pow_right₀ hL1 (by norm_num))
  have hn2 : (n:ℝ) ≤ 1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) :=
    hnfrac.trans (mul_le_mul_of_nonneg_right hLpow hNR.le)
  have hL14 : (L:ℝ)^14 = (L:ℝ)^2*(L:ℝ)^12 := by ring
  have hL12 : (0:ℝ) < (L:ℝ)^12 := pow_pos hL0 12
  have hc12 : 1/(L:ℝ)^14*(L:ℝ)^12 = 1/(L:ℝ)^2 := by
    rw [hL14, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hL12.ne', mul_one]
  have hnB : (n:ℝ)*((((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) ≤
      1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) := by
    calc (n:ℝ)*((((d*m)^24:ℕ):ℝ)*
          sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))))
        ≤ (1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ))*(L:ℝ)^12 :=
          mul_le_mul hnfrac hBcap hNB0
            (mul_nonneg (one_div_nonneg.mpr (pow_pos hL0 14).le) hNR.le)
      _ = (1/(L:ℝ)^14*(L:ℝ)^12)*(((d*m)^24:ℕ):ℝ) := by ring
      _ = 1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) := by rw [hc12]
  have hRbound : (n:ℝ)+(Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ))/(s/2+1)+
      (n:ℝ)*((((d*m)^24:ℕ):ℝ)*
        sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) ≤
      (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
    have h1 : (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ))/(s/2+1) ≤
        ((Bst+1)*(1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ)))/(s/2+1) := by
      refine div_le_div_of_nonneg_right ?_ hp2.le
      have h := mul_le_mul_of_nonneg_left hn2 hBst
      linarith
    have e : (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) =
        1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ)+((Bst+1)*(1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ)))/(s/2+1)+
          1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) := by
      unfold leechNegBlockConst24
      ring
    rw [e]
    linarith
  -- the three residual quantities are at most `N C/L²`, the tail at most `N C`
  have hT3 : 1/(L:ℝ)^2*((2*((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(11-p)) ≤
      (((d*m)^24:ℕ):ℝ)*((3/(11-p))/(L:ℝ)^2) := by
    have h1 : (2*((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(11-p) ≤
        (3*(((d*m)^24:ℕ):ℝ))/(11-p) := div_le_div_of_nonneg_right (by linarith) h11.le
    calc 1/(L:ℝ)^2*((2*((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(11-p))
        ≤ 1/(L:ℝ)^2*((3*(((d*m)^24:ℕ):ℝ))/(11-p)) := mul_le_mul_of_nonneg_left h1 hw₂
      _ = (((d*m)^24:ℕ):ℝ)*((3/(11-p))/(L:ℝ)^2) := by ring
  have hrCS0 : 0 ≤ residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z :=
    residualCrossSum_nonneg _ (shortRangeKernel24_nonneg _ _) _ _
  have hcell0 : 0 ≤ cellPairSum (sphereGaussianKernel24
      (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel24_nonneg _ _ _
  have hCeq : (((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) =
      (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2)+
        (((d*m)^24:ℕ):ℝ)*((3/(11-p))/(L:ℝ)^2) := by
    unfold leechLogBlockConst24
    ring
  have hA0 : 0 ≤ 1/(L:ℝ)^2*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z := mul_nonneg hw₂ hrCS0
  have hsum3 : residualNeutralizedEnergy (sphereRestrictedProbability24 (⋃ j, C j))
        (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1) (fun _ => 0) z+
      1/(L:ℝ)^2*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z+
      cellPairSum (sphereGaussianKernel24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z ≤
      (((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) := by
    rw [hCeq]
    have e : 1/(L:ℝ)^2*(residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z-
        (2*((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(11-p)) =
        1/(L:ℝ)^2*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z-
        1/(L:ℝ)^2*((2*((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(11-p)) := by
      ring
    rw [e] at hjoint
    linarith
  have hcellN : cellPairSum (sphereGaussianKernel24
      (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z ≤
      (((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) := by linarith
  have hNE : residualNeutralizedEnergy (sphereRestrictedProbability24 (⋃ j, C j))
      (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1) (fun _ => 0) z ≤
      (((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) := by linarith
  have hrCS : 1*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z ≤
      (((d*m)^24:ℕ):ℝ)*leechLogBlockConst24 s p Bst := by
    have h1 : 1/(L:ℝ)^2*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z ≤
        (((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) := by linarith
    have hL2 : (0:ℝ) < (L:ℝ)^2 := pow_pos hL0 2
    have h2 := mul_le_mul_of_nonneg_left h1 hL2.le
    have e1 : (L:ℝ)^2*(1/(L:ℝ)^2*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z) =
        residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodesF24 P (a*m) hn) z := by
      rw [← mul_assoc, mul_one_div_cancel hL2.ne', one_mul]
    have e2 : (L:ℝ)^2*((((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2)) =
        (((d*m)^24:ℕ):ℝ)*leechLogBlockConst24 s p Bst := by
      rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hL2.ne']
    rw [e1, e2] at h2
    rw [one_mul]
    exact h2
  refine ⟨combinedConfiguration24 (leechFamilyNodesF24 P (a*m) hn) z hcard
    (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid, ?_, ?_, ?_⟩
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration24_fullScaled_le hNpos (leechFamilyNodesF24 P (a*m) hn) z
      hcard (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid hη.le hα hη
    rw [one_div_one_div] at hfull
    have hw := hwindow P hv₃ hε₃ hδ hsep a d m ha hd hm hratio hn α hαpos
    rw [← hMK] at hw
    have hθ : leechGaussianThetaReal24 (α*leechConservativeRowFactor24) ≤
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) :=
      leechGaussianThetaReal24_anti (mul_pos hη hκ) (mul_le_mul_of_nonneg_right hα hκ.le)
    have hθ0 : 0 ≤ leechGaussianThetaReal24 (α*leechConservativeRowFactor24) :=
      zero_le_one.trans (leechGaussianThetaReal24_ge_one (mul_pos hαpos hκ))
    have hA0 : 0 ≤ leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2) :=
      zero_le_one.trans (leechGaussianThetaReal24_ge_one (mul_pos hαpos (pow_pos hη0 2)))
    have h48 : (48:ℝ) ≤ ((a*m:ℕ):ℝ) := by exact_mod_cast hn
    have hn₀ : (0:ℝ) < ((a*m:ℕ):ℝ) := by linarith
    have hfr0 : 0 ≤ 1-(1-48/((a*m:ℕ):ℝ))^24 := by
      have h1 : 48/((a*m:ℕ):ℝ) ≤ 1 := (div_le_one hn₀).mpr h48
      have h2 : 0 ≤ 48/((a*m:ℕ):ℝ) := div_nonneg (by norm_num) hn₀.le
      have h3 : (1-48/((a*m:ℕ):ℝ))^24 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hR0 : 0 ≤ 2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (α*leechConservativeRowFactor24) :=
      mul_nonneg (mul_nonneg (by norm_num) hfr0) hθ0
    have hR : 2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (α*leechConservativeRowFactor24) ≤ 1/(L:ℝ) :=
      (mul_le_mul_of_nonneg_left hθ (mul_nonneg (by norm_num) hfr0)).trans he4
    have hscale : sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)) ≤
        sphereGaussianScale24 ((d*m)^24) α := by
      rw [sphereGaussianScale24_eq_factor, sphereGaussianScale24_eq_factor]
      exact mul_le_mul_of_nonneg_left hα hc0.le
    have hE : Real.exp (-(sphereGaussianScale24 ((d*m)^24) α*δ^2)) ≤
        Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hscale (sq_nonneg δ)))
    have hfg := leechBlock_window_arith hNR hM0 hMN hA0 hR0 hR (Real.exp_pos _).le hE he5 hw
    have hres : cellPairSum (sphereGaussianKernel24
        (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z/(((d*m)^24:ℕ):ℝ) ≤
        leechLogBlockConst24 s p Bst/(L:ℝ)^2 := by
      rw [div_le_iff₀ hNR]
      linarith
    have h2L : leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2*(1/(L:ℝ)) =
        leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ) := by rw [mul_one_div]
    rw [h2L] at hfg
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left hfg (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))
  · -- the macroscopic end
    intro w hw hw1
    have hPm := leechFamilyUnion24_measurable P
    have hσR : (sphereProbabilityD 24) (⋃ j, C j) =
        (n:ℝ≥0∞)*(((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
      rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
      simp [hCmass]
    have hRne : (sphereProbabilityD 24) (leechFamilyUnion24 P)ᶜ ≠ 0 := by
      rw [← hCu, hσR]
      exact mul_ne_zero (by exact_mod_cast hnpos.ne')
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    have hmassR : (n:ℝ) =
        (((d*m)^24:ℕ):ℝ)*(sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ := by
      rw [← hCu, Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_comm (n:ℝ), ← mul_assoc,
        mul_inv_cancel₀ hNR.ne', one_mul]
    obtain ⟨hgint, hgval⟩ := negMacro_poly_integral hp hw.le leechMacroConstA24
      (leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26))
    have hmain : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α
        (combinedConfiguration24 (leechFamilyNodesF24 P (a*m) hn) z hcard
          (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid)+1)) ≤
        2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(leechMacroConstA24*α^2+
          leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α))+
        2/(((d*m)^24:ℕ):ℝ)*residualNeutralizedEnergy
          (sphereRestrictedProbability24 (leechFamilyUnion24 P)ᶜ)
          (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1)
          (fun _ => 0) z :=
      combinedConfiguration24_macroEnd_le hs hs0 hNpos
        (leechFamilyNodesF24 P (a*m) hn) z hcard (leechFamilyNodesF24_injective P hdisj (a*m) hn)
        hz havoid hPm hRne hmassR hw1
        (fun α => leechMacroConstA24*α^2+
          leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α) hgint
        (fun α hα => hmacro P hv₁ hε₁ hdisj a d m hd hm hratio hn α
          ⟨hα.1, hα.2.trans (hw1.trans (by norm_num))⟩)
    rw [hgval, show s/2-1+3 = s/2+2 by ring, show s/2-1+2 = s/2+1 by ring, ← hCu] at hmain
    have hwq : 0 ≤ w^(s/2+1)/(s/2+1) := div_nonneg (Real.rpow_nonneg hw.le _) hp2.le
    have hB' : leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*(w^(s/2+1)/(s/2+1)) ≤
        1/(L:ℝ)*(w^(s/2+1)/(s/2+1)) := mul_le_mul_of_nonneg_right he6 hwq
    have h2N : 2/(((d*m)^24:ℕ):ℝ)*residualNeutralizedEnergy
        (sphereRestrictedProbability24 (⋃ j, C j))
        (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1) (fun _ => 0) z ≤
        2*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hNE (by positivity : (0:ℝ) ≤ 2/(((d*m)^24:ℕ):ℝ))
      have e : 2/(((d*m)^24:ℕ):ℝ)*((((d*m)^24:ℕ):ℝ)*(leechLogBlockConst24 s p Bst/(L:ℝ)^2)) =
          2*(leechLogBlockConst24 s p Bst/(L:ℝ)^2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
      rw [e] at h
      exact h
    linarith
  · -- the short-range cost
    have hsumT := combinedConfiguration24_sum (leechFamilyNodesF24 P (a*m) hn) z hcard
      (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid
      (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (shortRangeKernel24_symm _ _)
    have htailP := htail P hv₂ hε₂ hδ hsep a d m ha hd hm hratio hn p hT1
    rw [← hMK] at htailP
    have hTB0 : 0 ≤ leechGaussianTailBudget24
        (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) p :=
      leechGaussianTailBudget24_nonneg
        (leechCorrectedDensityBudgetScale24_pos leechUnitDensityRadius24_pos) hT1
    have hsep0 : 0 ≤ separatedShortRangeBound24
        (sphereGaussianDensityFactor24 ((d*m)^24)) p δ :=
      separatedShortRangeBound24_nonneg hc0 hT1 hδ
    unfold cellPairSum leechLogBlockTailConst24
    rw [hsumT]
    exact leechBlock_tail_arith hNR hM0 hMN hTB0 hsep0 he3 htailP hrCS le_rfl

/-- The separated short-range bound at the density scale is at most `1/N` for every sufficiently
large refinement. -/
theorem separatedShortRangeBound24_eventually {p : ℝ} (hp : -1 < p) (d : ℕ) (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, (((d*m)^24:ℕ):ℝ)*separatedShortRangeBound24
      (sphereGaussianDensityFactor24 ((d*m)^24)) p δ ≤ 1 := by
  have hΓ : 0 < Real.Gamma (p+1) := Real.Gamma_pos_of_pos (by linarith)
  have hδ2 : 0 < δ^2 := pow_pos hδ 2
  have hNt0 : Tendsto (fun m : ℕ => (d*m)^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  have hNt : Tendsto (fun m : ℕ => (d*(m+1))^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans
      ((Nat.le_mul_of_pos_left (m+1) hd).trans (Nat.le_self_pow (by norm_num) _))) tendsto_id
  have hNp : ∀ m : ℕ, 0 < (d*(m+1))^24 := fun m => by positivity
  have h3 : Tendsto (fun m : ℕ => (((d*m)^24:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/2)*δ^2))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (sphereGaussianScale24_separated_tendsto hNt hNp (by norm_num : (0:ℝ) < 1/2) hδ)
  have h3g : Tendsto (fun m : ℕ => (((d*m)^24:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/2)*δ^2))*Real.Gamma (p+1))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using h3.mul_const (Real.Gamma (p+1))
  have e3a := (tendsto_order.mp h3g).2 1 one_pos
  have e3b := (tendsto_atTop.mp
    (sphereGaussianScale24_tendsto hNt0 (by norm_num : (0:ℝ) < 1/2))) (1/δ^2)
  filter_upwards [e3a, e3b] with m hm3a hm3b
  have hx : sphereGaussianScale24 ((d*m)^24) (1/2)*δ^2 =
      sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2 := by
    rw [sphereGaussianScale24_eq_factor]
    ring
  have hx1 : 1 ≤ sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2 := by
    rw [← hx]
    exact (div_le_iff₀ hδ2).mp hm3b
  have hx0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2 := by linarith
  have hpow : (1/(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))^(p+1) ≤ 1 :=
    Real.rpow_le_one (one_div_nonneg.mpr hx0.le) ((div_le_one hx0).mpr hx1) (by linarith)
  rw [hx] at hm3a
  unfold separatedShortRangeBound24
  calc (((d*m)^24:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))*
        ((1/(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))^(p+1)*Real.Gamma (p+1)))
      ≤ (((d*m)^24:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))*
        (1*Real.Gamma (p+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hΓ.le) (Real.exp_pos _).le) (Nat.cast_nonneg _)
    _ = (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))*
        Real.Gamma (p+1) := by ring
    _ ≤ 1 := hm3a.le

/-- For every tolerance index there is a denominator `d` such that every sufficiently large
refinement carries a block configuration with the three controls. -/
theorem exists_leech_log_block24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {p : ℝ} (hp0 : 0 ≤ p)
    (hp11 : p < 11) {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : LeechResidualStratifiable24 Bst)
    {L : ℕ} (hL : 2 ≤ L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ X : ConfigurationD 24 ((d*m)^24),
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(leechLogBlockConst24 s p Bst/(L:ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
          2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
            2*(leechLogBlockConst24 s p Bst/(L:ℝ)^2)) ∧
      cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p) X/
        (((d*m)^24:ℕ):ℝ) ≤ leechLogBlockTailConst24 s p Bst := by
  obtain ⟨ρ, hρ, hblock⟩ := exists_leech_log_block_configuration24 hs hs0 hp0 hp11 hL hBst
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  obtain ⟨K, P, a, d, δ, ha, hd, hδ, hv, hε, hratio, hdisj, hsep, hmassP, hcov, hKad⟩ :=
    exists_leech_patch_family24 ρ (1/(L:ℝ)^14) hρ (one_div_pos.mpr (pow_pos hL0 14))
  obtain ⟨N₀, hN₀⟩ := hstrat P (1/(L:ℝ)^2) (one_div_pos.mpr (pow_pos hL0 2))
  refine ⟨d, hd, ?_⟩
  have hNt : Tendsto (fun m : ℕ => (d*m)^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  filter_upwards [leechNegBlock_conditions_eventually hL a d ha hd hδ,
    separatedShortRangeBound24_eventually (by linarith : (-1:ℝ) < p) d hd hδ,
    hNt.eventually (eventually_ge_atTop N₀)] with m hm he3 hmN
  obtain ⟨hm0, hn, he4, he5, he6⟩ := hm
  obtain ⟨n, hnpos, hcard, hfrac, hmass⟩ :=
    leechFamilyF_residual_count P a d hd hmassP hKad m hm0 hn
  obtain ⟨C, dm, hCm, hCd, hCu, hCmassA, hdiam, hsum⟩ := hN₀ ((d*m)^24) n hmN hnpos hmass
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (0:ℝ) < (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hNpos
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hσA : (sphereProbabilityD 24) (leechFamilyUnion24 P)ᶜ =
      (n:ℝ≥0∞)*(((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
    have hreal : (sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ =
        (n:ℝ)/(((d*m)^24:ℕ):ℝ) := by
      rw [eq_div_iff hNR.ne']
      linarith
    rw [← ofReal_measureReal (measure_ne_top (sphereProbabilityD 24) (leechFamilyUnion24 P)ᶜ),
      hreal, ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv]
  have hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
    intro i
    rw [hCmassA i, hσA, ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt,
      one_mul]
  have hnfrac : (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ) := by
    have h1 : (n:ℝ)/(((d*m)^24:ℕ):ℝ) < 1/(L:ℝ)^14 := by
      rw [hfrac]
      linarith
    exact ((div_lt_iff₀ hNR).mp h1).le
  exact hblock P a d ha hd hδ hv hε hratio hdisj hsep m hm0 hn he4 he5 he6 he3 hnpos hcard
    hnfrac C dm hCm hCd hCmass hCu hdiam hsum

end SphericalRiesz
end
end
