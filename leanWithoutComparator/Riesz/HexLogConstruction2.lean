import Riesz.HexNegSharp2
import Riesz.SphereLog2
import Riesz.EqualAreaHex2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Riesz.HexGaussianBridge2

/-! Sharp logarithmic energy asymptotics on the actual two-dimensional sphere.

Joint residual selection supplies one Gaussian window, a macroscopic budget and a short-range budget. Rational ceiling sizes and ordered-pair extraction give configurations at every sufficiently large size. The final two-sided theorem is unconditional and uses the actual continuous double integral and the continued triangular Epstein derivative coefficient. -/

section

/-! Block configurations on S² with three Gaussian controls (stage LOG of the S² chain).

The module has three parts.

* `HexUniversalJoint2`: one joint stratified choice of residual points for the subtracted
  macroscopic kernel, the short-range kernel with the foreground cross pairs, and one Gaussian
  window.
* `HexShortRangeF2`: the short-range cost of a separated family of fourteenth-order patch
  nodes.
* `HexLogBlock2`: for a tolerance index `L ≥ 2` and every large refinement, an actual
  configuration of `(d m)²` points with a Gaussian window, a small macroscopic end at a
  negative exponent and a bounded short-range cost.  The short-range kernel enters the joint
  choice with the weight `L⁻²`, so that its centering term of size `N` stays below `N C/L²`.

No energy statement is made here and no Gaussian certificate is used.  The stratification of the
residual regions is the hypothesis `HexResidualStratifiable2`, which is proved in
`Riesz.SphereStratification2`. -/

section

/-! One joint residual choice on S² for the subtracted macroscopic kernel, the short-range tail
and one Gaussian window.

The residual region is the union of measurable pairwise disjoint cells of probability `1/N` with
diameters `d_j`.  One point is chosen in every cell, injectively and away from the foreground
points, so that the weighted sum of three quantities is at most `n w₃ + c_N/(p'+2) Σ_j d_j²`:

* the neutralized energy of the subtracted macroscopic kernel `K'_{p'}` (which is nonnegative);
* the short-range kernel `T_p`, with the residual/foreground cross pairs, centered by the bound
  `(2M+n)/(-p)`;
* one Gaussian window among the residual points, centered by the bound `n N B(t₀)`.

The same choice therefore serves the macroscopic end, the tail and the window of a block.  No
foreground estimate, configuration or attaining sequence is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

/-- One joint residual choice for the subtracted macroscopic kernel, the short-range kernel and
one Gaussian window on S². -/
theorem exists_hex_universal_joint_residual2 {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {p' p t₀ w₂ w₃ : ℝ} (hp' : -2 < p') (hp0 : -1 ≤ p) (hp : p < 0) (ht₀ : 0 ≤ t₀)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    {ι : Type*} [Fintype ι] (X : ι → SphereD 2)
    (C : Fin n → Set (SphereD 2)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹)
    (dm : Fin n → ℝ) (hdm : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ z : Fin n → SphereD 2, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧
      (∀ j, z j ∉ range X) ∧
      0 ≤ residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
        (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1) (fun _ => 0) z ∧
      residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
          (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1) (fun _ => 0) z+
        w₂*(residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X z-
          (2*(Fintype.card ι:ℝ)+(n:ℝ))/(-p))+
        w₃*(cellPairSum (sphereGaussianKernel2 t₀) z-
          (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀)) ≤
      (n:ℝ)*w₃+sphereGaussianDensityFactor2 N/(p'+2)*∑ j, (dm j)^2 := by
  classical
  have hc : 0 < sphereGaussianDensityFactor2 N := sphereGaussianDensityFactor2_pos hN
  have hRm : MeasurableSet (⋃ j, C j) := MeasurableSet.iUnion hCm
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (N:ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h11 : 0 < -p := by linarith
  have hnne : (n:ℝ) ≠ 0 := hnR.ne'
  have hNne : (N:ℝ) ≠ 0 := hNR.ne'
  have hp2 : 0 < p'+2 := by linarith
  have hσR : (sphereProbabilityD 2) (⋃ j, C j) = (n:ℝ≥0∞)*(N:ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hR0 : (sphereProbabilityD 2) (⋃ j, C j) ≠ 0 := by
    rw [hσR]
    exact mul_ne_zero hn0 (ENNReal.inv_ne_zero.mpr hNt)
  have hinv : ((sphereProbabilityD 2) (⋃ j, C j))⁻¹ = (N:ℝ≥0∞)*(n:ℝ≥0∞)⁻¹ := by
    rw [hσR, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), inv_inv, mul_comm]
  have htoReal : (((sphereProbabilityD 2) (⋃ j, C j))⁻¹).toReal = (N:ℝ)/(n:ℝ) := by
    rw [hinv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  -- the residual probability measure, as a variable with its defining equation
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure (SphereD 2), μ = sphereRestrictedProbability2 (⋃ j, C j) :=
    ⟨_, rfl⟩
  have hμP : IsProbabilityMeasure μ := by
    rw [hμdef]
    exact sphereRestrictedProbability2_probability _ hR0
  have hμA : NullSingletonClass μ := by
    rw [hμdef]
    infer_instance
  have hμC : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹ := by
    intro j
    have hsub : C j ∩ ⋃ i, C i = C j := inter_eq_left.mpr (subset_iUnion C j)
    rw [hμdef]
    simp only [sphereRestrictedProbability2, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j), hsub, hCmass j, hinv, mul_comm (N:ℝ≥0∞) _, mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, mul_one]
  have hcover : μ (⋃ j, C j)ᶜ = 0 := by
    rw [hμdef]
    exact sphereRestrictedProbability2_compl _ hRm
  have hB : μ (range X) = 0 := (finite_range X).measure_zero μ
  have hint_eq : ∀ f : SphereD 2 → ℝ,
      (∫ y, f y ∂μ) = (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, f y ∂(sphereProbabilityD 2) := by
    intro f
    rw [hμdef]
    simp only [sphereRestrictedProbability2]
    rw [integral_smul_measure, smul_eq_mul, htoReal]
  have hmassR : (n:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real (⋃ j, C j) := by
    rw [Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast]
    field_simp
  -- integrability of the three kernels
  have hKprod : Integrable (Function.uncurry
      (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1)) (μ.prod μ) :=
    negMacroKernel2_integrable hc.le hp' zero_le_one (μ.prod μ)
  have hKk : ∀ x, Integrable (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x) μ :=
    fun x => negMacroKernel2_row_integrable hc.le hp' zero_le_one x μ
  have hKV : Integrable (residualRowPotential μ
      (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1)) μ := hKprod.integral_prod_left
  have hTk : ∀ x, Integrable (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x) μ := by
    intro x
    rw [hμdef]
    exact shortRangeKernel2_restricted_integrable hc hp _ x
  have hTV : Integrable (residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)) μ := by
    rw [hμdef]
    exact shortRangeKernel2_restricted_rowPotential_integrable hc hp _ hR0
  have hTprod : Integrable (Function.uncurry
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry
        (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)) (μ.prod μ) :=
      (shortRangeKernel2_measurable (sphereGaussianDensityFactor2 N) p).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).mpr ⟨Filter.Eventually.of_forall fun x => hTk x, ?_⟩
    refine hTV.congr (Filter.Eventually.of_forall fun x => ?_)
    unfold residualRowPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y =
      ‖shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y‖
    rw [Real.norm_eq_abs, abs_of_nonneg (shortRangeKernel2_nonneg _ _ _ _)]
  have hGprod : Integrable (Function.uncurry (sphereGaussianKernel2 t₀)) (μ.prod μ) :=
    sphereGaussianKernel2_integrable_finite ht₀ (μ.prod μ)
  have hGk : ∀ x, Integrable (sphereGaussianKernel2 t₀ x) μ :=
    fun x => sphereGaussianKernel2_row_integrable_finite ht₀ x μ
  have hGV : Integrable (residualRowPotential μ (sphereGaussianKernel2 t₀)) μ :=
    hGprod.integral_prod_left
  have hL₂ : Integrable (residualCrossLinear μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n) μ :=
    residualCrossLinear_integrable (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)
      (shortRangeKernel2_symm _ p) X hTk hTV n
  have hL₃ : Integrable (residualCrossLinear μ (sphereGaussianKernel2 t₀)
      (Fin.elim0 : Fin 0 → SphereD 2) n) μ :=
    residualCrossLinear_integrable (sphereGaussianKernel2 t₀) (sphereGaussianKernel2_comm t₀)
      (Fin.elim0 : Fin 0 → SphereD 2) hGk hGV n
  have hk₁₂ : ∀ x, Integrable (fun y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
      w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y) μ :=
    fun x => (hKk x).add ((hTk x).const_mul w₂)
  have hV₁₂ : Integrable (residualRowPotential μ
      (fun x y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
        w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y)) μ :=
    residualRowPotential_add_smul_integrable _ _ w₂ hKk hTk hKV hTV
  have hL₁₂ : Integrable (fun x => (0:ℝ)+w₂*residualCrossLinear μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n x) μ :=
    (integrable_zero _ _ _).add (hL₂.const_mul w₂)
  -- the joint choice
  obtain ⟨z, hinj, hzC, hzB, hne⟩ := exists_stratified_residualNeutralizedEnergy_le_diag μ
    (fun x y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
      w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y+
      w₃*sphereGaussianKernel2 t₀ x y)
    (fun x => (0:ℝ)+w₂*residualCrossLinear μ
        (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n x+
      w₃*residualCrossLinear μ (sphereGaussianKernel2 t₀)
        (Fin.elim0 : Fin 0 → SphereD 2) n x)
    (fun x y => show negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
        w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y+
        w₃*sphereGaussianKernel2 t₀ x y =
        negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 y x+
          w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p y x+
          w₃*sphereGaussianKernel2 t₀ y x by
      rw [negMacroKernel2_symm _ p' 1 x y, shortRangeKernel2_symm _ p x y,
        sphereGaussianKernel2_comm t₀ x y])
    (0+w₂*0+w₃*1)
    (fun x => show negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x x+
        w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x x+
        w₃*sphereGaussianKernel2 t₀ x x = 0+w₂*0+w₃*1 by
      rw [negMacroKernel2_self, shortRangeKernel2_self _ hp0, sphereGaussianKernel2_self])
    hn C hCm hCd hcover hμC
    (fun j => w₃+sphereGaussianDensityFactor2 N/(p'+2)*(dm j)^2)
    (fun j x hx y hy => show 0+w₂*0+w₃*1-
        (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
          w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y+
          w₃*sphereGaussianKernel2 t₀ x y) ≤
        w₃+sphereGaussianDensityFactor2 N/(p'+2)*(dm j)^2 by
      have hvar := negMacroKernel2_variance hc.le hp' zero_le_one x y
      rw [Real.one_rpow] at hvar
      have hd := hdm j x hx y hy
      have hd0 : 0 ≤ dist x y := dist_nonneg
      have hd2 : (dist x y)^2 ≤ (dm j)^2 := pow_le_pow_left₀ hd0 hd 2
      have hG := sphereGaussianKernel2_nonneg t₀ x y
      have hT := shortRangeKernel2_nonneg (sphereGaussianDensityFactor2 N) p x y
      have hcp : 0 ≤ sphereGaussianDensityFactor2 N/(p'+2) := div_nonneg hc.le hp2.le
      have h1 : sphereGaussianDensityFactor2 N*(dist x y)^2*(1/(p'+2)) ≤
          sphereGaussianDensityFactor2 N/(p'+2)*(dm j)^2 := by
        calc sphereGaussianDensityFactor2 N*(dist x y)^2*(1/(p'+2))
            = sphereGaussianDensityFactor2 N/(p'+2)*(dist x y)^2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hd2 hcp
      have h2 : 0 ≤ w₃*sphereGaussianKernel2 t₀ x y := mul_nonneg hw₃ hG
      have h3 : 0 ≤ w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y :=
        mul_nonneg hw₂ hT
      linarith)
    (fun x => (hk₁₂ x).add ((hGk x).const_mul w₃))
    (residualRowPotential_add_smul_integrable _ _ w₃ hk₁₂ hGk hV₁₂ hGV)
    ((hKprod.add (hTprod.const_mul w₂)).add (hGprod.const_mul w₃))
    (hL₁₂.add (hL₃.const_mul w₃)) (range X) hB
  have hKnonneg := negMacro2_residualNeutralizedEnergy_nonneg hc.le hp' zero_le_one z (⋃ j, C j)
    hR0 hmassR
  rw [← hμdef] at hKnonneg
  refine ⟨z, hinj, hzC, hzB, ?_, ?_⟩
  · rw [← hμdef]
    exact hKnonneg
  have hsplit₁ : residualNeutralizedEnergy μ
      (fun x y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
        w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y+
        w₃*sphereGaussianKernel2 t₀ x y)
      (fun x => (0:ℝ)+w₂*residualCrossLinear μ
          (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n x+
        w₃*residualCrossLinear μ (sphereGaussianKernel2 t₀)
          (Fin.elim0 : Fin 0 → SphereD 2) n x) z =
      residualNeutralizedEnergy μ
        (fun x y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
          w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y)
        (fun x => (0:ℝ)+w₂*residualCrossLinear μ
          (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n x) z+
      w₃*residualNeutralizedEnergy μ (sphereGaussianKernel2 t₀)
        (residualCrossLinear μ (sphereGaussianKernel2 t₀)
          (Fin.elim0 : Fin 0 → SphereD 2) n) z :=
    residualNeutralizedEnergy_add_smul
      (fun x y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
        w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y)
      (sphereGaussianKernel2 t₀)
      (fun x => (0:ℝ)+w₂*residualCrossLinear μ
        (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n x)
      (residualCrossLinear μ (sphereGaussianKernel2 t₀) (Fin.elim0 : Fin 0 → SphereD 2) n)
      w₃ hk₁₂ hGk hV₁₂ hGV hL₁₂ hL₃ z
  have hsplit₂ : residualNeutralizedEnergy μ
      (fun x y => negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1 x y+
        w₂*shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y)
      (fun x => (0:ℝ)+w₂*residualCrossLinear μ
        (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n x) z =
      residualNeutralizedEnergy μ (negMacroKernel2 (sphereGaussianDensityFactor2 N) p' 1)
        (fun _ => 0) z+
      w₂*residualNeutralizedEnergy μ (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p)
        (residualCrossLinear μ (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X n) z :=
    residualNeutralizedEnergy_add_smul _ _ (fun _ => (0:ℝ)) _ w₂ hKk hTk hKV hTV
      (integrable_zero _ _ _) hL₂ z
  have hcrossT := residualNeutralizedEnergy_crossLinear
    (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) (shortRangeKernel2_symm _ p) X
    hTk hTV z
  have hcrossG := residualNeutralizedEnergy_crossLinear (sphereGaussianKernel2 t₀)
    (sphereGaussianKernel2_comm t₀) (Fin.elim0 : Fin 0 → SphereD 2) hGk hGV z
  rw [hsplit₁, hsplit₂, hcrossT, hcrossG] at hne
  -- the short-range kernel: bounded smooth mean
  have hTrow : ∀ x, (n:ℝ)*residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) x ≤ 1/(-p) := by
    intro x
    have h := shortRangeKernel2_cell_rows_le hN hp C hCm hCd hCmass x
    rw [sphereRestrictedProbability2_sum_integral C hCm hCd hCmass
      (shortRangeKernel2_row_integrable (sphereGaussianScale2_pos hN zero_lt_one) hp x)] at h
    unfold residualRowPotential
    rw [hint_eq]
    calc (n:ℝ)*((N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y ∂(sphereProbabilityD 2))
        = (N:ℝ)*∫ y in ⋃ j, C j,
          shortRangeKernel2 (sphereGaussianDensityFactor2 N) p x y
            ∂(sphereProbabilityD 2) := by field_simp
      _ ≤ 1/(-p) := h
  have hTU : ∀ x, residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) x ≤ 1/((n:ℝ)*(-p)) := by
    intro x
    have h := hTrow x
    rw [le_div_iff₀ (mul_pos hnR h11)]
    calc _ = ((n:ℝ)*residualRowPotential μ
          (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) x)*(-p) := by ring
      _ ≤ 1/(-p)*(-p) := mul_le_mul_of_nonneg_right h h11.le
      _ = 1 := by field_simp [hp.ne]
  have hTbg : residualBackground μ (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) ≤
      1/((n:ℝ)*(-p)) := by
    unfold residualBackground
    calc _ ≤ ∫ _x, 1/((n:ℝ)*(-p)) ∂μ := integral_mono hTV (integrable_const _) hTU
      _ = _ := by simp
  have hTsum : (n:ℝ)*(∑ i, residualRowPotential μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) (X i)) ≤
      (Fintype.card ι:ℝ)/(-p) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _i : ι, 1/(-p) := Finset.sum_le_sum fun i _ => hTrow (X i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hTbgn : (n:ℝ)^2*residualBackground μ
      (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) ≤ (n:ℝ)/(-p) := by
    calc _ ≤ (n:ℝ)^2*(1/((n:ℝ)*(-p))) := mul_le_mul_of_nonneg_left hTbg (by positivity)
      _ = _ := by field_simp
  have hc₂ : residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X z-
      (2*(Fintype.card ι:ℝ)+(n:ℝ))/(-p) ≤
      residualCentered μ (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X z := by
    rw [residualCentered_eq_crossSumS2]
    have he : (2*(Fintype.card ι:ℝ)+(n:ℝ))/(-p) =
        2*((Fintype.card ι:ℝ)/(-p))+(n:ℝ)/(-p) := by ring
    rw [he]
    linarith
  -- the Gaussian window: bounded smooth mean
  have hGU : ∀ x, residualRowPotential μ (sphereGaussianKernel2 t₀) x ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ := by
    intro x
    unfold residualRowPotential
    rw [hint_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∫ y in ⋃ j, C j, sphereGaussianKernel2 t₀ x y ∂(sphereProbabilityD 2))
        ≤ ∫ y, sphereGaussianKernel2 t₀ x y ∂(sphereProbabilityD 2) :=
          setIntegral_le_integral (sphereGaussianKernel2_integrable ht₀ x)
            (Filter.Eventually.of_forall fun y => sphereGaussianKernel2_nonneg _ _ _)
      _ = sphereGaussianBackground2 t₀ := (sphereGaussianBackground2_eq_potential ht₀ x).symm
  have hGbg : residualBackground μ (sphereGaussianKernel2 t₀) ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ := by
    unfold residualBackground
    calc _ ≤ ∫ _x, (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ ∂μ :=
          integral_mono hGV (integrable_const _) hGU
      _ = _ := by simp
  have hc₃ : cellPairSum (sphereGaussianKernel2 t₀) z-
      (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀) ≤
      residualCentered μ (sphereGaussianKernel2 t₀) (Fin.elim0 : Fin 0 → SphereD 2) z := by
    have hbgn : (n:ℝ)^2*residualBackground μ (sphereGaussianKernel2 t₀) ≤
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀) := by
      calc _ ≤ (n:ℝ)^2*((N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀) :=
            mul_le_mul_of_nonneg_left hGbg (by positivity)
        _ = _ := by field_simp
    unfold residualCentered residualPairEnergy cellPairSum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero, sub_zero,
      add_zero]
    linarith
  have hm₂ := mul_le_mul_of_nonneg_left hc₂ hw₂
  have hm₃ := mul_le_mul_of_nonneg_left hc₃ hw₃
  have hsum : (∑ j, (w₃+sphereGaussianDensityFactor2 N/(p'+2)*(dm j)^2)) =
      (n:ℝ)*w₃+sphereGaussianDensityFactor2 N/(p'+2)*∑ j, (dm j)^2 := by
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

This is the order-fourteen counterpart of `hexPatchFamily_shortRange_le`.  The residual points
and the full configuration are not part of this statement. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Short-range cost of a separated fourteenth-order foreground family. -/
theorem hexPatchFamily_shortRange_leF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m) (p : ℝ), -1 < p →
      (∑ q, ∑ q', shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p
          (hexFamilyNodesF2 P (a*m) hn q) (hexFamilyNodesF2 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^2*
          hexGaussianTailBudget2
            (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) p+
        ((K:ℝ)*((a*m:ℕ):ℝ)^2)^2*
          separatedShortRangeBound2 (sphereGaussianDensityFactor2 ((d*m)^2)) p δ := by
  classical
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaHexFourteenth2_rational_density_budget
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn p hp
  have hc0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2) :=
    sphereGaussianDensityFactor2_pos (by positivity)
  set c := sphereGaussianDensityFactor2 ((d*m)^2) with hc
  set τ := separatedShortRangeBound2 c p δ with hτ
  have hτ0 : 0 ≤ τ := separatedShortRangeBound2_nonneg hc0 hp hδ
  set B := hexGaussianTailBudget2
    (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) p with hB
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hcardNodes : (Fintype.card (Fin 2 → FourteenNodeIndex (a*m)) : ℝ) = n^2 := by
    rw [fourteenCubeNode_card 2 (a*m) hn]
    exact Nat.cast_pow _ _
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, shortRangeKernel2 c p
      (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P i) (a*m) hn w)) ≤
      n^2*B := by
    intro i
    have h := hb (P i).g (P i).v (P i).c (hv i) (P i).c_mem (P i).ε (P i).ε_pos (hε i)
      (P i).small hexUnitDensityRadius2 p hexUnitDensityRadius2_pos hp a d m ha hd hm
      (hratio i) hn
    have h' := (div_le_iff₀ (pow_pos hn0 2)).mp h
    calc _ ≤ B*n^2 := h'
      _ = _ := mul_comm _ _
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, shortRangeKernel2 c p
      (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P j) (a*m) hn w) ≤ τ :=
    fun i j hij u w => shortRangeKernel2_le_of_separated hc0 hp hδ
      (hsep i j hij _ (smallHexPatchNodesF2_mem (P i) _ hn u) _
        (smallHexPatchNodesF2_mem (P j) _ hn w))
  have hrow : ∀ i u, (∑ j, ∑ w, shortRangeKernel2 c p
      (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P j) (a*m) hn w)) ≤
      (∑ w, shortRangeKernel2 c p (smallHexPatchNodesF2 (P i) (a*m) hn u)
        (smallHexPatchNodesF2 (P i) (a*m) hn w))+(K:ℝ)*(n^2*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, shortRangeKernel2 c p
        (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P j) (a*m) hn w)) ≤
        (if j = i then ∑ w, shortRangeKernel2 c p (smallHexPatchNodesF2 (P i) (a*m) hn u)
          (smallHexPatchNodesF2 (P i) (a*m) hn w) else 0)+n^2*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 2).le hτ0)
      · rw [ite_eq_right hji, zero_add]
        calc _ ≤ ∑ _w : Fin 2 → FourteenNodeIndex (a*m), τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = n^2*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, shortRangeKernel2 c p
            (smallHexPatchNodesF2 (P i) (a*m) hn u)
            (smallHexPatchNodesF2 (P i) (a*m) hn w) else 0)+n^2*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- all pairs
  have hsplit : (∑ q, ∑ q', shortRangeKernel2 c p
      (hexFamilyNodesF2 P (a*m) hn q) (hexFamilyNodesF2 P (a*m) hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, shortRangeKernel2 c p
        (smallHexPatchNodesF2 (P i) (a*m) hn u) (smallHexPatchNodesF2 (P j) (a*m) hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, shortRangeKernel2 c p (smallHexPatchNodesF2 (P i) (a*m) hn u)
          (smallHexPatchNodesF2 (P i) (a*m) hn w))+(K:ℝ)*(n^2*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, shortRangeKernel2 c p (smallHexPatchNodesF2 (P i) (a*m) hn u)
          (smallHexPatchNodesF2 (P i) (a*m) hn w))+(K:ℝ)*(n^2*((K:ℝ)*(n^2*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ ≤ (∑ _i : Fin K, n^2*B)+(K:ℝ)*(n^2*((K:ℝ)*(n^2*τ))) :=
      add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end SphericalRiesz
end
end

section

/-! Block configurations on S² with three Gaussian controls (stage LOG).

For a tolerance index `L ≥ 2` take a near-full rational Hex patch family of residual fraction
below `L⁻¹⁴`, the fourteenth-order nodes of a refinement `m`, and one residual point per cell of
an exact-mass stratification of the complement, chosen jointly for the subtracted macroscopic
kernel, the short-range kernel with weight `L⁻²` and one Gaussian window.  The resulting
configuration of `N = (d m)²` points satisfies

* the window `Full_α ≤ (1+1/L)(Θ(α(1-1/L)²)+2/L)+(1+L) C/L²` for every `α ≥ 1/L`,
* the macroscopic end `∫_{(0,w]} α^(s/2-1)(F+1) ≤ 2(A w^(s/2+2)/(s/2+2)+w^(s/2+1)/(L(s/2+1)))+2C/L²`
  for every cutoff `0 < w ≤ 1`,
* the short-range cost `Σ T_p/N ≤ D`,

with `A`, `C`, `D` independent of `L` and of the refinement.  The weight `L⁻²` keeps the centering
term `(2M+n)/(-p) = O(N)` of the short-range kernel below `N C/L²`, so that the window and the
macroscopic end stay as small as in the negative-exponent block, while the cost itself is at most
`N C`.  The stratification of the residual regions is the hypothesis
`HexResidualStratifiable2`.  No energy statement is made here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

/-- Residual constant of the logarithmic blocks. -/
def hexLogBlockConst2 (s p Bst : ℝ) : ℝ := hexNegBlockConst2 s Bst+3/(-p)

/-- Short-range constant of the logarithmic blocks. -/
def hexLogBlockTailConst2 (s p Bst : ℝ) : ℝ :=
  hexGaussianTailBudget2 (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) p+1+
    hexLogBlockConst2 s p Bst

/-- One block with three controls: explicit conditions on the family, the refinement and the
residual cells give an actual configuration with a Gaussian window, a small macroscopic end and
a bounded short-range cost. -/
theorem exists_hex_log_block_configuration2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {p : ℝ}
    (hp0 : -1 < p) (hp11 : p < 0) {L : ℕ} (hL : 2 ≤ L) {Bst : ℝ} (hBst : 0 ≤ Bst) :
    ∃ ρ > 0, ∀ {K : ℕ} (P : Fin K → SmallHexCubePatch2) (a d : ℕ) {δ : ℝ},
      0 < a → 0 < d → 0 < δ →
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ) →
      (∀ i, (P i).ε*(d:ℝ) = hexUnitDensityRadius2*(a:ℝ)) →
      Pairwise (fun i j => Disjoint (smallHexSpherePatch2 (P i))
        (smallHexSpherePatch2 (P j))) →
      (∀ i j, i ≠ j → ∀ x ∈ smallHexSpherePatch2 (P i),
        ∀ y ∈ smallHexSpherePatch2 (P j), δ ≤ dist x y) →
      ∀ m : ℕ, 0 < m → 48 ≤ a*m →
      2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) ≤ 1/(L:ℝ) →
      (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) →
      hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) ≤ 1/(L:ℝ) →
      (((d*m)^2:ℕ):ℝ)*separatedShortRangeBound2
        (sphereGaussianDensityFactor2 ((d*m)^2)) p δ ≤ 1 →
      ∀ {n : ℕ}, 0 < n →
      Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m)))+n = (d*m)^2 →
      (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^2:ℕ):ℝ) →
      ∀ (C : Fin n → Set (SphereD 2)) (dm : Fin n → ℝ), (∀ i, MeasurableSet (C i)) →
      Pairwise (fun i j => Disjoint (C i) (C j)) →
      (∀ i, (sphereProbabilityD 2) (C i) = (((d*m)^2:ℕ):ℝ≥0∞)⁻¹) →
      (⋃ j, C j) = (hexFamilyUnion2 P)ᶜ →
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) →
      (∑ j, sphereGaussianDensityFactor2 ((d*m)^2)*(dm j)^2) ≤
        Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) →
      ∃ X : ConfigurationD 2 ((d*m)^2),
        (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/(L:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
            (1+(L:ℝ))*(hexLogBlockConst2 s p Bst/(L:ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
            2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(hexLogBlockConst2 s p Bst/(L:ℝ)^2)) ∧
        cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p) X/
          (((d*m)^2:ℕ):ℝ) ≤ hexLogBlockTailConst2 s p Bst := by
  have hp : -2 < s/2-1 := by linarith
  have hp2 : 0 < s/2+1 := by linarith
  have hT1 : -1 < p := by linarith
  have hT0 : -1 ≤ p := by linarith
  have h11 : 0 < -p := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) < 1 := by
    rw [div_lt_one hL0]
    linarith
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hκ := hexConservativeRowFactor2_pos
  obtain ⟨ρ₁,hρ₁,_,hmacro⟩ := hexPatchFamily_mixed_defect_macroF
  obtain ⟨ρ₂,hρ₂,_,htail⟩ := hexPatchFamily_shortRange_leF
  obtain ⟨ρ₃,hρ₃,_,hwindow⟩ := hexPatchFamily_gaussianWindow_leF hη hη1
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), ?_⟩
  intro K P a d δ ha hd hδ hv hε hratio hdisj hsep m hm hn he4 he5 he6 he3 n hnpos hcard hnfrac
    C dm hCm hCd hCmass hCu hdiam hstrat
  have hv₁ : ∀ i, ‖(P i).v‖ ≤ ρ₁ := fun i => (hv i).trans (min_le_left _ _)
  have hv₂ : ∀ i, ‖(P i).v‖ ≤ ρ₂ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hv₃ : ∀ i, ‖(P i).v‖ ≤ ρ₃ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε₁ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₁ := fun i =>
    (hε i).trans (min_le_left _ _)
  have hε₂ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₂ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₃ : ∀ i, (P i).ε*equalAreaScaleRadius2 ≤ ρ₃ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (0:ℝ) < (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hNpos
  have hc0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2) := sphereGaussianDensityFactor2_pos hNpos
  have ht₀ : 0 ≤ sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)) :=
    (sphereGaussianScale2_pos hNpos hη).le
  have hw₂ : (0:ℝ) ≤ 1/(L:ℝ)^2 := one_div_nonneg.mpr (pow_pos hL0 2).le
  -- one joint residual choice for the macroscopic kernel, the tail and the window
  obtain ⟨z, hz, _, havoid, hK0, hjoint⟩ := exists_hex_universal_joint_residual2 hNpos hnpos
    hp hT0 hp11 ht₀ hw₂ (zero_le_one : (0:ℝ) ≤ 1) (hexFamilyNodesF2 P (a*m) hn) C hCm hCd
    hCmass dm hdiam
  rw [show s/2-1+2 = s/2+1 by ring] at hjoint
  -- cardinalities as real numbers
  have hM0 : (0:ℝ) ≤ ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hMn : ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hcard
  have hn0R : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hMN : ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) ≤
      (((d*m)^2:ℕ):ℝ) := by linarith
  have hMK : ((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) =
      (K:ℝ)*((a*m:ℕ):ℝ)^2 := by
    rw [Fintype.card_prod, Fintype.card_fin, fourteenCubeNode_card 2 (a*m) hn, Nat.cast_mul,
      Nat.cast_pow]
  -- the residual quantities are at most `N C/L²`
  have hBcap : (((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) ≤ (L:ℝ)^12 := by
    have h := sphereGaussianBackground2_scaled_cap hNpos hη
    have h' : (((d*m)^2:ℕ):ℝ)*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) ≤ (L:ℝ) := by
      simpa only [one_div,inv_inv] using h
    exact h'.trans (by simpa only [pow_one] using
      pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 12))
  have hNB0 : 0 ≤ (((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))) :=
    mul_nonneg hNR.le (sphereGaussianBackground2_nonneg _)
  have hsumdm : sphereGaussianDensityFactor2 ((d*m)^2)/(s/2+1)*∑ j, (dm j)^2 ≤
      (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ))/(s/2+1) := by
    rw [div_mul_eq_mul_div, Finset.mul_sum]
    exact div_le_div_of_nonneg_right hstrat hp2.le
  have hLpow : 1/(L:ℝ)^14 ≤ 1/(L:ℝ)^2 :=
    one_div_le_one_div_of_le (pow_pos hL0 2) (pow_le_pow_right₀ hL1 (by norm_num))
  have hn2 : (n:ℝ) ≤ 1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) :=
    hnfrac.trans (mul_le_mul_of_nonneg_right hLpow hNR.le)
  have hL14 : (L:ℝ)^14 = (L:ℝ)^2*(L:ℝ)^12 := by ring
  have hL12 : (0:ℝ) < (L:ℝ)^12 := pow_pos hL0 12
  have hc12 : 1/(L:ℝ)^14*(L:ℝ)^12 = 1/(L:ℝ)^2 := by
    rw [hL14, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hL12.ne', mul_one]
  have hnB : (n:ℝ)*((((d*m)^2:ℕ):ℝ)*
      sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) ≤
      1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) := by
    calc (n:ℝ)*((((d*m)^2:ℕ):ℝ)*
          sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))))
        ≤ (1/(L:ℝ)^14*(((d*m)^2:ℕ):ℝ))*(L:ℝ)^12 :=
          mul_le_mul hnfrac hBcap hNB0
            (mul_nonneg (one_div_nonneg.mpr (pow_pos hL0 14).le) hNR.le)
      _ = (1/(L:ℝ)^14*(L:ℝ)^12)*(((d*m)^2:ℕ):ℝ) := by ring
      _ = 1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) := by rw [hc12]
  have hRbound : (n:ℝ)+(Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ))/(s/2+1)+
      (n:ℝ)*((((d*m)^2:ℕ):ℝ)*
        sphereGaussianBackground2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) ≤
      (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2) := by
    have h1 : (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ))/(s/2+1) ≤
        ((Bst+1)*(1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ)))/(s/2+1) := by
      refine div_le_div_of_nonneg_right ?_ hp2.le
      have h := mul_le_mul_of_nonneg_left hn2 hBst
      linarith
    have e : (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2) =
        1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ)+((Bst+1)*(1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ)))/(s/2+1)+
          1/(L:ℝ)^2*(((d*m)^2:ℕ):ℝ) := by
      unfold hexNegBlockConst2
      ring
    rw [e]
    linarith
  -- the three residual quantities are at most `N C/L²`, the tail at most `N C`
  have hT3 : 1/(L:ℝ)^2*((2*((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(-p)) ≤
      (((d*m)^2:ℕ):ℝ)*((3/(-p))/(L:ℝ)^2) := by
    have h1 : (2*((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(-p) ≤
        (3*(((d*m)^2:ℕ):ℝ))/(-p) := div_le_div_of_nonneg_right (by linarith) h11.le
    calc 1/(L:ℝ)^2*((2*((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(-p))
        ≤ 1/(L:ℝ)^2*((3*(((d*m)^2:ℕ):ℝ))/(-p)) := mul_le_mul_of_nonneg_left h1 hw₂
      _ = (((d*m)^2:ℕ):ℝ)*((3/(-p))/(L:ℝ)^2) := by ring
  have hrCS0 : 0 ≤ residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z :=
    residualCrossSum_nonnegS2 _ (shortRangeKernel2_nonneg _ _) _ _
  have hcell0 : 0 ≤ cellPairSum (sphereGaussianKernel2
      (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel2_nonneg _ _ _
  have hCeq : (((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) =
      (((d*m)^2:ℕ):ℝ)*(hexNegBlockConst2 s Bst/(L:ℝ)^2)+
        (((d*m)^2:ℕ):ℝ)*((3/(-p))/(L:ℝ)^2) := by
    unfold hexLogBlockConst2
    ring
  have hA0 : 0 ≤ 1/(L:ℝ)^2*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z := mul_nonneg hw₂ hrCS0
  have hsum3 : residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
        (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1) (fun _ => 0) z+
      1/(L:ℝ)^2*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z+
      cellPairSum (sphereGaussianKernel2 (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z ≤
      (((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) := by
    rw [hCeq]
    have e : 1/(L:ℝ)^2*(residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z-
        (2*((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(-p)) =
        1/(L:ℝ)^2*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z-
        1/(L:ℝ)^2*((2*((Fintype.card (Fin K × (Fin 2 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ))/(-p)) := by
      ring
    rw [e] at hjoint
    linarith
  have hcellN : cellPairSum (sphereGaussianKernel2
      (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z ≤
      (((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) := by linarith
  have hNE : residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
      (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1) (fun _ => 0) z ≤
      (((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) := by linarith
  have hrCS : 1*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z ≤
      (((d*m)^2:ℕ):ℝ)*hexLogBlockConst2 s p Bst := by
    have h1 : 1/(L:ℝ)^2*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z ≤
        (((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) := by linarith
    have hL2 : (0:ℝ) < (L:ℝ)^2 := pow_pos hL0 2
    have h2 := mul_le_mul_of_nonneg_left h1 hL2.le
    have e1 : (L:ℝ)^2*(1/(L:ℝ)^2*residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z) =
        residualCrossSumS2 (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (hexFamilyNodesF2 P (a*m) hn) z := by
      rw [← mul_assoc, mul_one_div_cancel hL2.ne', one_mul]
    have e2 : (L:ℝ)^2*((((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2)) =
        (((d*m)^2:ℕ):ℝ)*hexLogBlockConst2 s p Bst := by
      rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hL2.ne']
    rw [e1, e2] at h2
    rw [one_mul]
    exact h2
  refine ⟨combinedConfiguration2 (hexFamilyNodesF2 P (a*m) hn) z hcard
    (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid, ?_, ?_, ?_⟩
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration2_fullScaled_le hNpos (hexFamilyNodesF2 P (a*m) hn) z
      hcard (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid hη.le hα hη
    rw [one_div_one_div] at hfull
    have hw := hwindow P hv₃ hε₃ hδ hsep a d m ha hd hm hratio hn α hαpos
    rw [← hMK] at hw
    have hθ : hexGaussianThetaReal2 (α*hexConservativeRowFactor2) ≤
        hexGaussianThetaReal2 (1/(L:ℝ)*hexConservativeRowFactor2) :=
      hexGaussianThetaReal2_anti (mul_pos hη hκ) (mul_le_mul_of_nonneg_right hα hκ.le)
    have hθ0 : 0 ≤ hexGaussianThetaReal2 (α*hexConservativeRowFactor2) :=
      zero_le_one.trans (hexGaussianThetaReal2_ge_one (mul_pos hαpos hκ))
    have hA0 : 0 ≤ hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2) :=
      zero_le_one.trans (hexGaussianThetaReal2_ge_one (mul_pos hαpos (pow_pos hη0 2)))
    have h48 : (48:ℝ) ≤ ((a*m:ℕ):ℝ) := by exact_mod_cast hn
    have hn₀ : (0:ℝ) < ((a*m:ℕ):ℝ) := by linarith
    have hfr0 : 0 ≤ 1-(1-48/((a*m:ℕ):ℝ))^2 := by
      have h1 : 48/((a*m:ℕ):ℝ) ≤ 1 := (div_le_one hn₀).mpr h48
      have h2 : 0 ≤ 48/((a*m:ℕ):ℝ) := div_nonneg (by norm_num) hn₀.le
      have h3 : (1-48/((a*m:ℕ):ℝ))^2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hR0 : 0 ≤ 2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (α*hexConservativeRowFactor2) :=
      mul_nonneg (mul_nonneg (by norm_num) hfr0) hθ0
    have hR : 2*(1-(1-48/((a*m:ℕ):ℝ))^2)*
        hexGaussianThetaReal2 (α*hexConservativeRowFactor2) ≤ 1/(L:ℝ) :=
      (mul_le_mul_of_nonneg_left hθ (mul_nonneg (by norm_num) hfr0)).trans he4
    have hscale : sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)) ≤
        sphereGaussianScale2 ((d*m)^2) α := by
      rw [sphereGaussianScale2_eq_factor, sphereGaussianScale2_eq_factor]
      exact mul_le_mul_of_nonneg_left hα hc0.le
    have hE : Real.exp (-(sphereGaussianScale2 ((d*m)^2) α*δ^2)) ≤
        Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ))*δ^2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hscale (sq_nonneg δ)))
    have hfg := hexBlock_window_arith hNR hM0 hMN hA0 hR0 hR (Real.exp_pos _).le hE he5 hw
    have hres : cellPairSum (sphereGaussianKernel2
        (sphereGaussianScale2 ((d*m)^2) (1/(L:ℝ)))) z/(((d*m)^2:ℕ):ℝ) ≤
        hexLogBlockConst2 s p Bst/(L:ℝ)^2 := by
      rw [div_le_iff₀ hNR]
      linarith
    have h2L : hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2*(1/(L:ℝ)) =
        hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ) := by rw [mul_one_div]
    rw [h2L] at hfg
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left hfg (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))
  · -- the macroscopic end
    intro w hw hw1
    have hPm := hexFamilyUnion2_measurable P
    have hσR : (sphereProbabilityD 2) (⋃ j, C j) =
        (n:ℝ≥0∞)*(((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
      rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
      simp [hCmass]
    have hRne : (sphereProbabilityD 2) (hexFamilyUnion2 P)ᶜ ≠ 0 := by
      rw [← hCu, hσR]
      exact mul_ne_zero (by exact_mod_cast hnpos.ne')
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    have hmassR : (n:ℝ) =
        (((d*m)^2:ℕ):ℝ)*(sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ := by
      rw [← hCu, Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_comm (n:ℝ), ← mul_assoc,
        mul_inv_cancel₀ hNR.ne', one_mul]
    obtain ⟨hgint, hgval⟩ := negMacro_poly_integralS2 hp hw.le hexMacroConstA2
      (hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26))
    have hmain : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 (hexFamilyNodesF2 P (a*m) hn) z hcard
          (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid)+1)) ≤
        2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(hexMacroConstA2*α^2+
          hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α))+
        2/(((d*m)^2:ℕ):ℝ)*residualNeutralizedEnergy
          (sphereRestrictedProbability2 (hexFamilyUnion2 P)ᶜ)
          (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1)
          (fun _ => 0) z :=
      combinedConfiguration2_macroEnd_le hs hs0 hNpos
        (hexFamilyNodesF2 P (a*m) hn) z hcard (hexFamilyNodesF2_injective P hdisj (a*m) hn)
        hz havoid hPm hRne hmassR hw1
        (fun α => hexMacroConstA2*α^2+
          hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α) hgint
        (fun α hα => hmacro P hv₁ hε₁ hdisj a d m hd hm hratio hn α
          ⟨hα.1, hα.2.trans (hw1.trans (by norm_num))⟩)
    rw [hgval, show s/2-1+3 = s/2+2 by ring, show s/2-1+2 = s/2+1 by ring, ← hCu] at hmain
    have hwq : 0 ≤ w^(s/2+1)/(s/2+1) := div_nonneg (Real.rpow_nonneg hw.le _) hp2.le
    have hB' : hexMacroConstB2*((((d*m)^2:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*(w^(s/2+1)/(s/2+1)) ≤
        1/(L:ℝ)*(w^(s/2+1)/(s/2+1)) := mul_le_mul_of_nonneg_right he6 hwq
    have h2N : 2/(((d*m)^2:ℕ):ℝ)*residualNeutralizedEnergy
        (sphereRestrictedProbability2 (⋃ j, C j))
        (negMacroKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) (s/2-1) 1) (fun _ => 0) z ≤
        2*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hNE (by positivity : (0:ℝ) ≤ 2/(((d*m)^2:ℕ):ℝ))
      have e : 2/(((d*m)^2:ℕ):ℝ)*((((d*m)^2:ℕ):ℝ)*(hexLogBlockConst2 s p Bst/(L:ℝ)^2)) =
          2*(hexLogBlockConst2 s p Bst/(L:ℝ)^2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
      rw [e] at h
      exact h
    linarith
  · -- the short-range cost
    have hsumT := combinedConfiguration2_sum (hexFamilyNodesF2 P (a*m) hn) z hcard
      (hexFamilyNodesF2_injective P hdisj (a*m) hn) hz havoid
      (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p)
      (shortRangeKernel2_symm _ _)
    have htailP := htail P hv₂ hε₂ hδ hsep a d m ha hd hm hratio hn p hT1
    rw [← hMK] at htailP
    have hTB0 : 0 ≤ hexGaussianTailBudget2
        (hexCorrectedDensityBudgetScale2 hexUnitDensityRadius2) p :=
      hexGaussianTailBudget2_nonneg
        (hexCorrectedDensityBudgetScale2_pos hexUnitDensityRadius2_pos) hT1
    have hsep0 : 0 ≤ separatedShortRangeBound2
        (sphereGaussianDensityFactor2 ((d*m)^2)) p δ :=
      separatedShortRangeBound2_nonneg hc0 hT1 hδ
    unfold cellPairSum hexLogBlockTailConst2
    rw [hsumT]
    exact hexBlock_tail_arith hNR hM0 hMN hTB0 hsep0 he3 htailP hrCS le_rfl

/-- The separated short-range bound at the density scale is at most `1/N` for every sufficiently
large refinement. -/
theorem separatedShortRangeBound2_eventually {p : ℝ} (hp : -1 < p) (d : ℕ) (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, (((d*m)^2:ℕ):ℝ)*separatedShortRangeBound2
      (sphereGaussianDensityFactor2 ((d*m)^2)) p δ ≤ 1 := by
  have hΓ : 0 < Real.Gamma (p+1) := Real.Gamma_pos_of_pos (by linarith)
  have hδ2 : 0 < δ^2 := pow_pos hδ 2
  have hNt0 : Tendsto (fun m : ℕ => (d*m)^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  have hNt : Tendsto (fun m : ℕ => (d*(m+1))^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans
      ((Nat.le_mul_of_pos_left (m+1) hd).trans (Nat.le_self_pow (by norm_num) _))) tendsto_id
  have hNp : ∀ m : ℕ, 0 < (d*(m+1))^2 := fun m => by positivity
  have h3 : Tendsto (fun m : ℕ => (((d*m)^2:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/2)*δ^2))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (sphereGaussianScale2_separated_tendsto hNt hNp (by norm_num : (0:ℝ) < 1/2) hδ)
  have h3g : Tendsto (fun m : ℕ => (((d*m)^2:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale2 ((d*m)^2) (1/2)*δ^2))*Real.Gamma (p+1))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using h3.mul_const (Real.Gamma (p+1))
  have e3a := (tendsto_order.mp h3g).2 1 one_pos
  have e3b := (tendsto_atTop.mp
    (sphereGaussianScale2_tendsto hNt0 (by norm_num : (0:ℝ) < 1/2))) (1/δ^2)
  filter_upwards [e3a, e3b] with m hm3a hm3b
  have hx : sphereGaussianScale2 ((d*m)^2) (1/2)*δ^2 =
      sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2 := by
    rw [sphereGaussianScale2_eq_factor]
    ring
  have hx1 : 1 ≤ sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2 := by
    rw [← hx]
    exact (div_le_iff₀ hδ2).mp hm3b
  have hx0 : 0 < sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2 := by linarith
  have hpow : (1/(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))^(p+1) ≤ 1 :=
    Real.rpow_le_one (one_div_nonneg.mpr hx0.le) ((div_le_one hx0).mpr hx1) (by linarith)
  rw [hx] at hm3a
  unfold separatedShortRangeBound2
  calc (((d*m)^2:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))*
        ((1/(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))^(p+1)*Real.Gamma (p+1)))
      ≤ (((d*m)^2:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))*
        (1*Real.Gamma (p+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hΓ.le) (Real.exp_pos _).le) (Nat.cast_nonneg _)
    _ = (((d*m)^2:ℕ):ℝ)*Real.exp (-(sphereGaussianDensityFactor2 ((d*m)^2)*δ^2/2))*
        Real.Gamma (p+1) := by ring
    _ ≤ 1 := hm3a.le

/-- For every tolerance index there is a denominator `d` such that every sufficiently large
refinement carries a block configuration with the three controls. -/
theorem exists_hex_log_block2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {p : ℝ} (hp0 : -1 < p)
    (hp11 : p < 0) {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : HexResidualStratifiable2 Bst)
    {L : ℕ} (hL : 2 ≤ L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ X : ConfigurationD 2 ((d*m)^2),
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
        (1+1/(L:ℝ))*(hexGaussianThetaReal2 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(hexLogBlockConst2 s p Bst/(L:ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
          2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
            2*(hexLogBlockConst2 s p Bst/(L:ℝ)^2)) ∧
      cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p) X/
        (((d*m)^2:ℕ):ℝ) ≤ hexLogBlockTailConst2 s p Bst := by
  obtain ⟨ρ, hρ, hblock⟩ := exists_hex_log_block_configuration2 hs hs0 hp0 hp11 hL hBst
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  obtain ⟨K, P, a, d, δ, ha, hd, hδ, hv, hε, hratio, hdisj, hsep, hmassP, hcov, hKad⟩ :=
    exists_hex_patch_family2 ρ (1/(L:ℝ)^14) hρ (one_div_pos.mpr (pow_pos hL0 14))
  obtain ⟨N₀, hN₀⟩ := hstrat P hdisj (1/(L:ℝ)^2) (one_div_pos.mpr (pow_pos hL0 2))
  refine ⟨d, hd, ?_⟩
  have hNt : Tendsto (fun m : ℕ => (d*m)^2) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  filter_upwards [hexNegBlock_conditions_eventually hL a d ha hd hδ,
    separatedShortRangeBound2_eventually (by linarith : (-1:ℝ) < p) d hd hδ,
    hNt.eventually (eventually_ge_atTop N₀)] with m hm he3 hmN
  obtain ⟨hm0, hn, he4, he5, he6⟩ := hm
  obtain ⟨n, hnpos, hcard, hfrac, hmass⟩ :=
    hexFamilyF_residual_count P a d hd hmassP hKad m hm0 hn
  obtain ⟨C, dm, hCm, hCd, hCu, hCmassA, hdiam, hsum⟩ := hN₀ ((d*m)^2) n hmN hnpos hmass
  have hNpos : 0 < (d*m)^2 := by positivity
  have hNR : (0:ℝ) < (((d*m)^2:ℕ):ℝ) := by exact_mod_cast hNpos
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hσA : (sphereProbabilityD 2) (hexFamilyUnion2 P)ᶜ =
      (n:ℝ≥0∞)*(((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
    have hreal : (sphereProbabilityD 2).real (hexFamilyUnion2 P)ᶜ =
        (n:ℝ)/(((d*m)^2:ℕ):ℝ) := by
      rw [eq_div_iff hNR.ne']
      linarith
    rw [← ofReal_measureReal (measure_ne_top (sphereProbabilityD 2) (hexFamilyUnion2 P)ᶜ),
      hreal, ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv]
  have hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (((d*m)^2:ℕ):ℝ≥0∞)⁻¹ := by
    intro i
    rw [hCmassA i, hσA, ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt,
      one_mul]
  have hnfrac : (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^2:ℕ):ℝ) := by
    have h1 : (n:ℝ)/(((d*m)^2:ℕ):ℝ) < 1/(L:ℝ)^14 := by
      rw [hfrac]
      linarith
    exact ((div_lt_iff₀ hNR).mp h1).le
  exact hblock P a d ha hd hδ hv hε hratio hdisj hsep m hm0 hn he4 he5 he6 he3 hnpos hcard
    hnfrac C dm hCm hCd hCmass hCu hdiam hsum

end SphericalRiesz
end
end
end

section

/-! The logarithmic energy on S²: sharp upper bound at every large `N` and the two-sided
asymptotics (stage LOG of the S² chain).

The module has three parts.

* `SphereLogBridge2`: the Gaussian-only bridge.  A macroscopic budget at a negative exponent, a
  bound of the full Gaussian profile at `α = 1/2`, a short-range cost and the pointwise window
  give an explicit integrable majorant of `α⁻¹ (F_N(α) + 1_{(0,1)}(α))`, and the reverse Fatou
  lemma bounds the normalized logarithmic energy by `C_log + η`.
* `RationalSizeLogGap2`: the gap of the rational size ceiling beats the logarithm,
  `(1 - (N-1)/(M-1))(1 + log M) → 0`, and the arithmetic of the normalized logarithmic energy of
  a subconfiguration.
* `SphereLogUpper2`: configurations of every large size with normalized logarithmic energy at
  most `C_log + η` (a block of the least rational size above `N` and a subconfiguration whose
  pair average does not increase), the form of the conjecture, and the two-sided statement.

The upper half uses no hypothesis.  The two-sided statement assumes all-scale Hex contact
certificates (stage G2, proved by the triangular Gaussian bridge) for its lower half. -/

section

/-! The Gaussian-only upper bridge for the logarithmic energy on S² (stage LOG).

With `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα` the normalized logarithmic energy is
`½ (J_N + κ - log π + (1/2) log A₂)`.  Three Gaussian controls of a sequence of configurations
give an integrable majorant of the integrand:

* a macroscopic budget `∫_{(0,1]} α^(s/2-1) (F+1) ≤ B` at a negative exponent `-2 < s < 0` gives
  `F(α)+1 ≤ C B α^(-s/2)` for `α ≤ 1/2` by the doubling of the positive semidefinite profile, so
  the integrand is at most `C B α^(-s/2-1)`, integrable at `0`;
* a bound `Full_{1/2} ≤ W` gives `F(α)+1 ≤ W` for `α ≥ 1/2`;
* a short-range cost `Σ T_p/N ≤ D`, `-1 < p < 0`, gives `F(α) ≤ 2 D α^(-(p+1))` for `α ≥ 2`, so
  the integrand is at most `2 D α^(-(p+2))`, integrable at infinity.

With the pointwise window `limsup Full_α ≤ Θ_Λ(α)` the reverse Fatou lemma gives
`limsup J_N ≤ ∫ α⁻¹ (Θ_Λ(α) - α⁻¹ - 1 + 1_{(0,1)}(α)) dα`, i.e. the normalized logarithmic
energy is eventually at most `C_log + η`.  No Gaussian certificate is used. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

/-- Doubling of the positive semidefinite profile turns a macroscopic Gaussian budget at a
negative exponent into a pointwise bound which decays at `0`. -/
theorem sphereGaussianCenteredScaled2_macro_budget_bound {N : ℕ} (hN : 0 < N) {s B : ℝ}
    (hs : -2 < s) (hs0 : s < 0) (X : ConfigurationD 2 N)
    (hB : (∫ β in Ioc (0:ℝ) 1, β^(s/2-1)*(sphereGaussianCenteredScaled2 β X+1)) ≤ B)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1/2) :
    sphereGaussianCenteredScaled2 α X+1 ≤
      (Real.sqrt 2^3*(s/2)/(2^(s/2)-1))*B*α^(-(s/2)) := by
  have hκ : 0 < Real.sqrt 2^3 := by positivity
  have hi : IntegrableOn (fun β : ℝ => β^(s/2-1)*(sphereGaussianCenteredScaled2 β X+1))
      (Ioc 0 1) :=
    (sphereGaussianCenteredScaled2_neg_integrable hs hs0 hN X).mono_set Ioc_subset_Ioi_self
  have hsub : Ioc α (2*α) ⊆ Ioc (0:ℝ) 1 := fun β hβ => ⟨hα.trans hβ.1, by linarith [hβ.2]⟩
  have h0 : (0:ℝ) ∉ Set.uIcc α (2*α) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hw : IntegrableOn (fun β : ℝ => β^(s/2-1)) (Ioc α (2*α)) :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).1
  have hq1 : s/2-1 ≠ -1 := ne_of_lt (by linarith)
  have hid : (∫ β in Ioc α (2*α), β^(s/2-1)) = α^(s/2)*(2^(s/2)-1)/(s/2) := by
    rw [← intervalIntegral.integral_of_le (by linarith), integral_rpow (Or.inr ⟨hq1, h0⟩),
      show s/2-1+1 = s/2 by ring, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hα.le]
    ring
  have hl : (sphereGaussianCenteredScaled2 α X+1)/Real.sqrt 2^3*
      (α^(s/2)*(2^(s/2)-1)/(s/2)) ≤ B := by
    calc (sphereGaussianCenteredScaled2 α X+1)/Real.sqrt 2^3*(α^(s/2)*(2^(s/2)-1)/(s/2))
        = ∫ β in Ioc α (2*α),
            ((sphereGaussianCenteredScaled2 α X+1)/Real.sqrt 2^3)*β^(s/2-1) := by
          rw [integral_const_mul, hid]
      _ ≤ ∫ β in Ioc α (2*α), β^(s/2-1)*(sphereGaussianCenteredScaled2 β X+1) := by
          apply setIntegral_mono_on (hw.const_mul _) (hi.mono_set hsub) measurableSet_Ioc
          intro β hβ
          have hd := sphereGaussianCenteredScaled2_doubling hN X hα hβ.1.le hβ.2
          have hd' : (sphereGaussianCenteredScaled2 α X+1)/Real.sqrt 2^3 ≤
              sphereGaussianCenteredScaled2 β X+1 := by
            rw [div_le_iff₀ hκ]
            linarith
          exact (mul_le_mul_of_nonneg_right hd'
            (Real.rpow_nonneg (hα.le.trans hβ.1.le) _)).trans_eq (mul_comm _ _)
      _ ≤ ∫ β in Ioc (0:ℝ) 1, β^(s/2-1)*(sphereGaussianCenteredScaled2 β X+1) := by
          apply setIntegral_mono_set hi
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
            exact mul_nonneg (Real.rpow_nonneg hβ.1.le _)
              (sphereGaussianCenteredScaled2_add_one_nonneg hN hβ.1.le X)
          · exact hsub.eventuallyLE
      _ ≤ B := hB
  have hq : s/2 < 0 := by linarith
  have hqne : s/2 ≠ 0 := hq.ne
  have h2 : (2:ℝ)^(s/2)-1 < 0 := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2) hq
    linarith
  have h2ne : (2:ℝ)^(s/2)-1 ≠ 0 := h2.ne
  have ha : 0 < α^(s/2) := Real.rpow_pos_of_pos hα _
  have hane : α^(s/2) ≠ 0 := ha.ne'
  have hκne : Real.sqrt 2^3 ≠ 0 := hκ.ne'
  have hcoef : 0 < Real.sqrt 2^3*(s/2)/(2^(s/2)-1) := by
    rw [mul_div_assoc]
    exact mul_pos hκ (div_pos_of_neg_of_neg hq h2)
  have hm := mul_le_mul_of_nonneg_right hl
    (mul_nonneg hcoef.le (inv_nonneg.mpr ha.le) :
      0 ≤ Real.sqrt 2^3*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹)
  have he : (sphereGaussianCenteredScaled2 α X+1)/Real.sqrt 2^3*
      (α^(s/2)*(2^(s/2)-1)/(s/2))*(Real.sqrt 2^3*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹) =
      sphereGaussianCenteredScaled2 α X+1 := by
    calc (sphereGaussianCenteredScaled2 α X+1)/Real.sqrt 2^3*
          (α^(s/2)*(2^(s/2)-1)/(s/2))*(Real.sqrt 2^3*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹)
        = (sphereGaussianCenteredScaled2 α X+1)*((Real.sqrt 2^3*(Real.sqrt 2^3)⁻¹)*
            (α^(s/2)*(α^(s/2))⁻¹)*(((2:ℝ)^(s/2)-1)*((2:ℝ)^(s/2)-1)⁻¹)*(s/2*(s/2)⁻¹)) := by
          ring
      _ = sphereGaussianCenteredScaled2 α X+1 := by
          rw [mul_inv_cancel₀ hκne, mul_inv_cancel₀ hane, mul_inv_cancel₀ h2ne,
            mul_inv_cancel₀ hqne]
          ring
  rw [he] at hm
  rw [Real.rpow_neg hα.le]
  calc sphereGaussianCenteredScaled2 α X+1
      ≤ B*(Real.sqrt 2^3*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹) := hm
    _ = Real.sqrt 2^3*(s/2)/(2^(s/2)-1)*B*(α^(s/2))⁻¹ := by ring

/-- The short-range cost controls the centered profile at large scales. -/
theorem sphereGaussianCenteredScaled2_le_shortRange {N : ℕ} (hN : 0 < N) {p D : ℝ}
    (hp : -1 < p) (hpneg : p < 0) (X : ConfigurationD 2 N)
    (hD : cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X/(N:ℝ) ≤ D)
    {α : ℝ} (hα : 2 ≤ α) :
    sphereGaussianCenteredScaled2 α X ≤ 2*α^(-(p+1))*D := by
  classical
  have hα0 : 0 < α := by linarith
  have hA : 0 ≤ (2:ℝ)*α^(-(p+1)) := by positivity
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hrow : (∑ i, ∑ j ∈ Finset.univ.erase i,
      sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j)) ≤
      (2:ℝ)*α^(-(p+1))*
        cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X := by
    unfold cellPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    calc
      _ ≤ (∑ j ∈ Finset.univ.erase i, (2:ℝ)*α^(-(p+1))*shortRangeKernel2
        (sphereGaussianDensityFactor2 N) p (X i) (X j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [sphereGaussianScale2_eq_factor]
        exact gaussian2_le_shortRange_pointwise (sphereGaussianDensityFactor2_pos hN) hp (by linarith) hα
          (X.injective.ne (Finset.mem_erase.mp hj).1.symm)
      _ ≤ (∑ j : Fin N, (2:ℝ)*α^(-(p+1))*shortRangeKernel2
          (sphereGaussianDensityFactor2 N) p (X i) (X j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ =>
          mul_nonneg hA (shortRangeKernel2_nonneg _ _ _ _))
  have hcenter : sphereGaussianCenteredScaled2 α X ≤
      (2:ℝ)*α^(-(p+1))*
        (cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X/(N:ℝ)) := by
    have hoff := sphereGaussianOffDiagonal2_eq_full_sub (sphereGaussianScale2 N α) X
    have hbg := sphereGaussianBackground2_nonneg (sphereGaussianScale2 N α)
    have he : sphereGaussianOffDiagonal2 (sphereGaussianScale2 N α) X/(N:ℝ) =
        (∑ i, ∑ j, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ)-1 := by
      rw [hoff, sub_div, div_self hNR.ne']
    calc
      _ ≤ sphereGaussianOffDiagonal2 (sphereGaussianScale2 N α) X/(N:ℝ) := by
        rw [he]
        unfold sphereGaussianCenteredScaled2
        nlinarith [mul_nonneg hNR.le hbg]
      _ ≤ ((2:ℝ)*α^(-(p+1))*
          cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X)/(N:ℝ) :=
        div_le_div_of_nonneg_right hrow hNR.le
      _ = _ := by ring
  exact hcenter.trans (mul_le_mul_of_nonneg_left hD hA)

/-- An explicit majorant of the logarithmic profile integrand, with actual Gaussian budgets as
its constants. -/
def sphereGaussianLogMajorant2 (s p B W D α : ℝ) : ℝ :=
  if α ≤ 1/2 then (Real.sqrt 2^3*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2)-1)
  else if α ≤ 2 then 2*|W|
  else 2*|D| *α^(-(p+2))

theorem sphereGaussianLogMajorant2_coef_pos {s : ℝ} (hs0 : s < 0) :
    0 < Real.sqrt 2^3*(s/2)/(2^(s/2)-1) := by
  have hκ : 0 < Real.sqrt 2^3 := by positivity
  have hq : s/2 < 0 := by linarith
  have h2 : (2:ℝ)^(s/2)-1 < 0 := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2) hq
    linarith
  rw [mul_div_assoc]
  exact mul_pos hκ (div_pos_of_neg_of_neg hq h2)

theorem sphereGaussianLogMajorant2_nonneg {s : ℝ} (hs0 : s < 0) (p B W D : ℝ) {α : ℝ}
    (hα : 0 < α) : 0 ≤ sphereGaussianLogMajorant2 s p B W D α := by
  have hc := sphereGaussianLogMajorant2_coef_pos hs0
  unfold sphereGaussianLogMajorant2
  split_ifs
  · exact mul_nonneg (mul_nonneg hc.le (abs_nonneg B)) (Real.rpow_nonneg hα.le _)
  · exact mul_nonneg (by norm_num) (abs_nonneg W)
  · exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg D))
      (Real.rpow_nonneg hα.le _)

theorem sphereGaussianLogMajorant2_integrable {s p : ℝ} (hs0 : s < 0) (hp : -1 < p)
    (B W D : ℝ) : IntegrableOn (sphereGaussianLogMajorant2 s p B W D) (Ioi 0) := by
  have hi0 : IntegrableOn (fun α : ℝ => α^(-(s/2)-1)) (Ioc 0 (1/2)) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -(s/2)-1)
      (a := 0) (b := 1/2)).1
  have hj0 : IntegrableOn (fun α : ℝ => α^(-(p+2))) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hi1 : IntegrableOn (fun α : ℝ =>
      (Real.sqrt 2^3*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2)-1)) (Ioc 0 (1/2)) := hi0.const_mul _
  have hm1 : IntegrableOn (fun _ : ℝ => 2*|W|) (Ioc (1/2) 2) :=
    integrableOn_const (by simp)
  have hj1 : IntegrableOn (fun α : ℝ => 2*|D| *α^(-(p+2))) (Ioi 2) := hj0.const_mul _
  have hi := hi1.integrable_indicator measurableSet_Ioc
  have hm := hm1.integrable_indicator measurableSet_Ioc
  have hj := hj1.integrable_indicator measurableSet_Ioi
  refine ((hi.add hm).add hj).integrableOn.congr_fun (fun α hα => ?_) measurableSet_Ioi
  have hα0 : (0:ℝ) < α := hα
  dsimp only [sphereGaussianLogMajorant2, Pi.add_apply]
  by_cases h1 : α ≤ 1/2
  · rw [ite_eq_left h1, indicator_of_mem (show α ∈ Ioc (0:ℝ) (1/2) from ⟨hα0, h1⟩),
      indicator_of_notMem (show α ∉ Ioc (1/2:ℝ) 2 from fun h => absurd h.1 (not_lt.mpr h1)),
      indicator_of_notMem (show α ∉ Ioi (2:ℝ) from fun h => by
        have : (2:ℝ) < α := h
        linarith), add_zero, add_zero]
  · have h1' : 1/2 < α := lt_of_not_ge h1
    by_cases h2 : α ≤ 2
    · rw [ite_eq_right h1, ite_eq_left h2,
        indicator_of_notMem (show α ∉ Ioc (0:ℝ) (1/2) from fun h => h1 h.2),
        indicator_of_mem (show α ∈ Ioc (1/2:ℝ) 2 from ⟨h1', h2⟩),
        indicator_of_notMem (show α ∉ Ioi (2:ℝ) from fun h => absurd h (not_lt.mpr h2)),
        zero_add, add_zero]
    · have h2' : 2 < α := lt_of_not_ge h2
      rw [ite_eq_right h1, ite_eq_right h2,
        indicator_of_notMem (show α ∉ Ioc (0:ℝ) (1/2) from fun h => h1 h.2),
        indicator_of_notMem (show α ∉ Ioc (1/2:ℝ) 2 from fun h => h2 h.2),
        indicator_of_mem (show α ∈ Ioi (2:ℝ) from h2'), zero_add, zero_add]

/-- The three Gaussian budgets bound the logarithmic profile integrand by the majorant. -/
theorem sphereGaussianCenteredScaled2_log_le_majorant {N : ℕ} (hN : 0 < N) {s p B W D : ℝ}
    (hs : -2 < s) (hs0 : s < 0) (hp : -1 < p) (hpneg : p < 0) (X : ConfigurationD 2 N)
    (hB : (∫ β in Ioc (0:ℝ) 1, β^(s/2-1)*(sphereGaussianCenteredScaled2 β X+1)) ≤ B)
    (hW : sphereGaussianFullScaled2 (1/2) X ≤ W)
    (hD : cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) p) X/(N:ℝ) ≤ D)
    {α : ℝ} (hα : 0 < α) :
    α⁻¹*(sphereGaussianCenteredScaled2 α X+(Ioo (0:ℝ) 1).indicator 1 α) ≤
      sphereGaussianLogMajorant2 s p B W D α := by
  have hinv : 0 < α⁻¹ := inv_pos.mpr hα
  have hc := sphereGaussianLogMajorant2_coef_pos hs0
  unfold sphereGaussianLogMajorant2
  by_cases h1 : α ≤ 1/2
  · rw [ite_eq_left h1, indicator_of_mem (show α ∈ Ioo (0:ℝ) 1 from ⟨hα, by linarith⟩),
      Pi.one_apply]
    have hb := sphereGaussianCenteredScaled2_macro_budget_bound hN hs hs0 X hB hα h1
    have hpow : 0 ≤ α^(-(s/2)) := Real.rpow_nonneg hα.le _
    have hb' : sphereGaussianCenteredScaled2 α X+1 ≤
        (Real.sqrt 2^3*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2)) :=
      hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self B) hc.le) hpow)
    have hsplit : α^(-(s/2)-1) = α^(-(s/2))*α⁻¹ := by
      rw [Real.rpow_sub_one hα.ne', div_eq_mul_inv]
    rw [hsplit]
    calc α⁻¹*(sphereGaussianCenteredScaled2 α X+1)
        ≤ α⁻¹*((Real.sqrt 2^3*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2))) :=
          mul_le_mul_of_nonneg_left hb' hinv.le
      _ = (Real.sqrt 2^3*(s/2)/(2^(s/2)-1))*|B| *(α^(-(s/2))*α⁻¹) := by ring
  · have h1' : 1/2 < α := lt_of_not_ge h1
    rw [ite_eq_right h1]
    have hind : (Ioo (0:ℝ) 1).indicator (1 : ℝ → ℝ) α ≤ 1 := by
      by_cases hm : α ∈ Ioo (0:ℝ) 1
      · rw [indicator_of_mem hm, Pi.one_apply]
      · rw [indicator_of_notMem hm]
        exact zero_le_one
    by_cases h2 : α ≤ 2
    · rw [ite_eq_left h2]
      have hfull := (sphereGaussianCenteredScaled2_add_one_le_full α X).trans
        ((sphereGaussianFullScaled2_anti hN X h1'.le).trans hW)
      have hval : sphereGaussianCenteredScaled2 α X+(Ioo (0:ℝ) 1).indicator 1 α ≤ |W| := by
        have := le_abs_self W
        linarith
      have hinv2 : α⁻¹ ≤ 2 :=
        inv_le_of_inv_le₀ (by norm_num) (by rw [inv_eq_one_div]; exact h1'.le)
      calc α⁻¹*(sphereGaussianCenteredScaled2 α X+(Ioo (0:ℝ) 1).indicator 1 α)
          ≤ α⁻¹*|W| := mul_le_mul_of_nonneg_left hval hinv.le
        _ ≤ 2*|W| := mul_le_mul_of_nonneg_right hinv2 (abs_nonneg W)
    · have h2' : 2 < α := lt_of_not_ge h2
      rw [ite_eq_right h2, indicator_of_notMem (show α ∉ Ioo (0:ℝ) 1 from fun h => by
        have : α < 1 := h.2
        linarith), add_zero]
      have hb := sphereGaussianCenteredScaled2_le_shortRange hN hp hpneg X hD h2'.le
      have hA : 0 ≤ (2:ℝ)*α^(-(p+1)) := by positivity
      have hb' : sphereGaussianCenteredScaled2 α X ≤ 2*α^(-(p+1))*|D| :=
        hb.trans (mul_le_mul_of_nonneg_left (le_abs_self D) hA)
      have hsplit : α^(-(p+2)) = α^(-(p+1))*α⁻¹ := by
        rw [show -(p+2) = -(p+1)-1 by ring, Real.rpow_sub_one hα.ne', div_eq_mul_inv]
      rw [hsplit]
      calc α⁻¹*sphereGaussianCenteredScaled2 α X
          ≤ α⁻¹*(2*α^(-(p+1))*|D|) := mul_le_mul_of_nonneg_left hb' hinv.le
        _ = 2*|D| *(α^(-(p+1))*α⁻¹) := by ring

/-- The pointwise window gives the pointwise upper limit of the logarithmic profile integrand. -/
theorem sphereGaussianCenteredScaled2_log_profile_upper_eventually
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, ConfigurationD 2 (N k)) {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (X k) ≤ hexGaussianThetaReal2 α+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α⁻¹*(sphereGaussianCenteredScaled2 α (X k)+(Ioo (0:ℝ) 1).indicator 1 α) ≤
        hexGaussianLogProfile2 α+ε := by
  intro ε hε
  have he : α^((0:ℝ)/2-1) = α⁻¹ := by
    rw [show (0:ℝ)/2-1 = -1 by norm_num, Real.rpow_neg_one]
  filter_upwards [sphereGaussianCenteredScaled2_weighted_profile_upper_eventually 0 hNt hN X hα
    hp ε hε] with k hk
  unfold hexGaussianRieszProfileRpow2 at hk
  rw [he] at hk
  unfold hexGaussianLogProfile2
  simp only [pow_one]
  linarith [mul_add α⁻¹ (sphereGaussianCenteredScaled2 α (X k)) ((Ioo (0:ℝ) 1).indicator 1 α),
    mul_add α⁻¹ (hexGaussianThetaReal2 α-α⁻¹-1) ((Ioo (0:ℝ) 1).indicator 1 α)]

/-- The Gaussian-only upper bridge for the logarithmic energy: a macroscopic budget at a
negative exponent, a bound of the full profile at `α = 1/2`, a short-range cost and the
pointwise window give `limsup normalizedEnergyLog2 ≤ C_log`. -/
theorem sphere2_log_upper_of_gaussian_budgets {s p : ℝ} (hs : -2 < s) (hs0 : s < 0)
    (hp : -1 < p) (hpneg : p < 0) {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, ConfigurationD 2 (N k)) (B W D : ℝ)
    (hB : ∀ k, (∫ β in Ioc (0:ℝ) 1,
      β^(s/2-1)*(sphereGaussianCenteredScaled2 β (X k)+1)) ≤ B)
    (hW : ∀ k, sphereGaussianFullScaled2 (1/2) (X k) ≤ W)
    (hD : ∀ k, cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 (N k)) p)
      (X k)/(N k:ℝ) ≤ D)
    (hprof : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (X k) ≤ hexGaussianThetaReal2 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      normalizedEnergyLog2 (X k) ≤ sphereLogCoefficient2+η := by
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hJ : ∀ n, (∫ α : ℝ in Ioi 0, hexGaussianLogProfile2 α)+2*η ≤
      ∫ α : ℝ in Ioi 0, α⁻¹*(sphereGaussianCenteredScaled2 α (X (φ n))+
        (Ioo (0:ℝ) 1).indicator 1 α) := by
    intro n
    have h1 := normalizedEnergyLog2_gaussian_mellin (hN (φ n)) (X (φ n))
    have h2 := lt_of_not_ge (hbad n)
    unfold sphereLogCoefficient2 at h2
    rw [h1] at h2
    unfold sphereLogProfileIntegral2 at h2
    linarith
  have h := integral_ge_of_eventual_upper_profile2
    (μ := volume.restrict (Ioi (0:ℝ))) (g := hexGaussianLogProfile2)
    (G := sphereGaussianLogMajorant2 s p B W D)
    (f := fun n α => α⁻¹*(sphereGaussianCenteredScaled2 α (X (φ n))+
      (Ioo (0:ℝ) 1).indicator 1 α))
    hexGaussianLogProfile2_integrable
    (fun n => sphereGaussianCenteredScaled2_log_integrable (hN (φ n)) (X (φ n)))
    (sphereGaussianLogMajorant2_integrable hs0 hp B W D)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianLogMajorant2_nonneg hs0 p B W D hα)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled2_log_le_majorant (hN (φ n)) hs hs0 hp hpneg (X (φ n))
        (hB (φ n)) (hW (φ n)) (hD (φ n)) hα)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact fun ε hε => hφt.eventually
        (sphereGaussianCenteredScaled2_log_profile_upper_eventually hNt hN X hα
          (hprof α hα) ε hε))
    hJ
  linarith

end SphericalRiesz
end
end

section

/-! The gap of the rational size ceiling with a logarithmic factor, and the arithmetic of the
normalized logarithmic energy of a subconfiguration.

For `M = (d m)²`, the least rational size above `N`, the relative gap satisfies
`(M - N) N^(1/2) ≤ 2 d M` (Bernoulli's inequality), hence
`(1 - (N-1)/(M-1)) (1 + log M) → 0`: the gap beats the logarithm.  This is the size condition
under which the normalized logarithmic energy `(E_log - W N² + (N/2) log N)/N` passes from a
configuration of `M` points to a subconfiguration of `N` points: if the pair average does not
increase, then

`nE(Y) ≤ θ nE(X) + (1-θ)(-W) + (1/2)(log N - θ log M)`,  `θ = (N-1)/(M-1)`,

and the right side is at most `c + (|c|+|W|+1)(1-θ)(1+log M)` when `nE(X) ≤ c`.  Only real
arithmetic and the size ceiling are used; no sphere, energy or configuration appears. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SphericalRiesz

/-- Arithmetic of the normalized logarithmic energy of a subconfiguration: `a`, `b` are the
energies of the configurations of `M` and `N` points. -/
theorem logSubconfiguration_arithS2 {a b W lN lM N M : ℝ} (hN : 1 < N) (hNM : N ≤ M)
    (he : b/(N*(N-1)) ≤ a/(M*(M-1))) :
    (b-W*N^2+N/2*lN)/N ≤
      (N-1)/(M-1)*((a-W*M^2+M/2*lM)/M)+(1-(N-1)/(M-1))*(-W)+
        (1/2)*(lN-(N-1)/(M-1)*lM) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hM1 : 0 < M-1 := by linarith
  have hM0' : M ≠ 0 := hM0.ne'
  have hM1' : M-1 ≠ 0 := hM1.ne'
  have hb : b ≤ a/(M*(M-1))*(N*(N-1)) := (div_le_iff₀ (mul_pos hN0 hN1)).mp he
  rw [div_le_iff₀ hN0]
  have hθ : (N-1)/(M-1)*(M-1) = N-1 := div_mul_cancel₀ _ hM1'
  have hA : a/(M*(M-1))*(M*(M-1)) = a := div_mul_cancel₀ _ (mul_ne_zero hM0' hM1')
  have hE : (a-W*M^2+M/2*lM)/M*M = a-W*M^2+M/2*lM := div_mul_cancel₀ _ hM0'
  have key : ((N-1)/(M-1)*((a-W*M^2+M/2*lM)/M)+(1-(N-1)/(M-1))*(-W)+
      (1/2)*(lN-(N-1)/(M-1)*lM))*N = a/(M*(M-1))*(N*(N-1))-W*N^2+N/2*lN := by
    apply mul_right_cancel₀ hM0'
    linear_combination ((N-1)/(M-1)*N)*hE-((N-1)/(M-1)*N)*hA+
      (a/(M*(M-1))*N*M-W*N*M)*hθ
  rw [key]
  linarith

/-- From the three-term bound of a subconfiguration to a bound with one error term. -/
theorem logSubconfiguration_boundS2 {x y c W lN lM θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hl : lN ≤ lM) (hlM : 0 ≤ lM) (hx : x ≤ c)
    (hy : y ≤ θ*x+(1-θ)*(-W)+(1/2)*(lN-θ*lM)) :
    y ≤ c+(|c|+|W|+1)*((1-θ)*(1+lM)) := by
  have h1θ : 0 ≤ 1-θ := sub_nonneg.mpr hθ1
  have h1 : θ*x ≤ θ*c := mul_le_mul_of_nonneg_left hx hθ0
  have h2 : θ*c ≤ c+(1-θ)*|c| := by
    have h := mul_nonneg h1θ (by linarith [neg_abs_le c] : 0 ≤ c+|c|)
    nlinarith [h]
  have h3 : (1-θ)*(-W) ≤ (1-θ)*|W| := mul_le_mul_of_nonneg_left (neg_le_abs W) h1θ
  have h4 : (1/2)*(lN-θ*lM) ≤ (1-θ)*lM := by
    have h := mul_nonneg h1θ hlM
    nlinarith [h]
  have h5 : 0 ≤ (|c|+|W|)*((1-θ)*lM) :=
    mul_nonneg (add_nonneg (abs_nonneg c) (abs_nonneg W)) (mul_nonneg h1θ hlM)
  nlinarith [h1, h2, h3, h4, h5, h1θ]

/-- The gap of the rational size ceiling: `(M - N) N^(1/2) ≤ 2 d M`. -/
theorem rationalSizeCeiling2_gap_le (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    ((rationalSizeCeiling2 d N:ℝ)-(N:ℝ))*(N:ℝ)^(1/2:ℝ) ≤
      2*(d:ℝ)*(rationalSizeCeiling2 d N:ℝ) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (N:ℝ)^(1/2:ℝ) := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [hadef]
    exact Real.rpow_pos_of_pos hNR _
  have hNa : (N:ℝ) = a^2 := by
    rw [hadef]
    exact (real_second_root_pow N).symm
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (d:ℝ)*(rationalSizeIndex2 d N:ℝ) := ⟨_, rfl⟩
  have hceil1 : a/(d:ℝ) ≤ (rationalSizeIndex2 d N:ℝ) := by
    rw [hadef]
    exact Nat.le_ceil _
  have hceil2 : (rationalSizeIndex2 d N:ℝ) < a/(d:ℝ)+1 := by
    rw [hadef]
    exact Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hNR.le _) hdR.le)
  have hab : a ≤ b := by
    rw [hbdef]
    have h := (div_le_iff₀ hdR).mp hceil1
    linarith [mul_comm (d:ℝ) (rationalSizeIndex2 d N:ℝ)]
  have hbd : b ≤ a+d := by
    rw [hbdef]
    have h := mul_lt_mul_of_pos_left hceil2 hdR
    have e : (d:ℝ)*(a/(d:ℝ)+1) = a+d := by
      rw [mul_add, mul_div_cancel₀ _ hdR.ne', mul_one]
    linarith
  have hb : 0 < b := ha.trans_le hab
  have hMb : (rationalSizeCeiling2 d N:ℝ) = b^2 := by
    rw [hbdef]
    unfold rationalSizeCeiling2
    rw [Nat.cast_pow, Nat.cast_mul]
  have hb2 : 0 < b^2 := pow_pos hb 2
  have hB := one_add_mul_sub_le_pow (a := a/b) (by linarith [div_nonneg ha.le hb.le]) 2
  have h1 : b^2-a^2 ≤ 2*(1-a/b)*b^2 := by
    have h := mul_le_mul_of_nonneg_right hB hb2.le
    rw [div_pow, div_mul_cancel₀ _ hb2.ne'] at h
    push_cast at h
    nlinarith [h]
  have hr : 1-a/b ≤ (d:ℝ)/b := by
    rw [one_sub_div hb.ne']
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  have hab1 : a/b ≤ 1 := (div_le_one hb).mpr hab
  rw [← hadef, hMb, hNa]
  calc (b^2-a^2)*a ≤ (2*(1-a/b)*b^2)*a := mul_le_mul_of_nonneg_right h1 ha.le
    _ ≤ (2*((d:ℝ)/b)*b^2)*a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (by norm_num)) hb2.le) ha.le
    _ = 2*(d:ℝ)*b^2*(a/b) := by ring
    _ ≤ 2*(d:ℝ)*b^2*1 := mul_le_mul_of_nonneg_left hab1 (by positivity)
    _ = 2*(d:ℝ)*b^2 := mul_one _

/-- The relative gap of the rational size ceiling beats the logarithm:
`(1 - (N-1)/(M-1)) (1 + log M) → 0` for `M = rationalSizeCeiling2 d N`. -/
theorem rationalSizeCeiling2_log_gap_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (1-((N:ℝ)-1)/((rationalSizeCeiling2 d N:ℝ)-1))*
      (1+Real.log (rationalSizeCeiling2 d N:ℝ))) atTop (𝓝 0) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hcast : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => (N:ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp hcast
  have h2 : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)^(1/2:ℝ)) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero).comp hcast
  have hU : Tendsto (fun N : ℕ => 48*(d:ℝ)*((1+Real.log 2)*(N:ℝ)^(-(1/2:ℝ))+
      Real.log (N:ℝ)/(N:ℝ)^(1/2:ℝ))) atTop (𝓝 0) := by
    have h := ((h1.const_mul (1+Real.log 2)).add h2).const_mul (48*(d:ℝ))
    simpa only [mul_zero, add_zero] using h
  have hratio := (tendsto_order.mp (rationalSizeCeiling2_ratio_tendsto d hd)).2 2 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hMN : (N:ℝ) ≤ (rationalSizeCeiling2 d N:ℝ) := by
      exact_mod_cast rationalSizeCeiling2_ge d N hd
    have hM1 : 0 < (rationalSizeCeiling2 d N:ℝ)-1 := by linarith
    have hθ : ((N:ℝ)-1)/((rationalSizeCeiling2 d N:ℝ)-1) ≤ 1 :=
      (div_le_one hM1).mpr (by linarith)
    have hlog : 0 ≤ Real.log (rationalSizeCeiling2 d N:ℝ) := Real.log_nonneg (by linarith)
    exact mul_nonneg (by linarith) (by linarith)
  · filter_upwards [eventually_ge_atTop 2, hratio] with N hN hr
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0:ℝ) < N := by linarith
    have hMN : (N:ℝ) ≤ (rationalSizeCeiling2 d N:ℝ) := by
      exact_mod_cast rationalSizeCeiling2_ge d N hd
    have hM0 : (0:ℝ) < (rationalSizeCeiling2 d N:ℝ) := by linarith
    have hM1 : 0 < (rationalSizeCeiling2 d N:ℝ)-1 := by linarith
    have hM2N : (rationalSizeCeiling2 d N:ℝ) < 2*(N:ℝ) := (div_lt_iff₀ hN0).mp hr
    have ha : 0 < (N:ℝ)^(1/2:ℝ) := Real.rpow_pos_of_pos hN0 _
    have hgap := rationalSizeCeiling2_gap_le d N hd (by omega)
    have ht : 1-((N:ℝ)-1)/((rationalSizeCeiling2 d N:ℝ)-1) =
        ((rationalSizeCeiling2 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling2 d N:ℝ)-1) := by
      rw [one_sub_div hM1.ne']
      congr 1
      ring
    have ht0 : 0 ≤ ((rationalSizeCeiling2 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling2 d N:ℝ)-1) :=
      div_nonneg (by linarith) hM1.le
    have ht' : ((rationalSizeCeiling2 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling2 d N:ℝ)-1) ≤
        48*(d:ℝ)/(N:ℝ)^(1/2:ℝ) := by
      rw [div_le_div_iff₀ hM1 ha]
      have h48 : 2*(d:ℝ)*(rationalSizeCeiling2 d N:ℝ) ≤
          48*(d:ℝ)*((rationalSizeCeiling2 d N:ℝ)-1) := by
        nlinarith [mul_nonneg hdR.le (by linarith : (0:ℝ) ≤ (rationalSizeCeiling2 d N:ℝ)-2)]
      linarith
    have hlogM : Real.log (rationalSizeCeiling2 d N:ℝ) ≤ Real.log 2+Real.log (N:ℝ) := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log hM0 hM2N.le
    have hlog0 : 0 ≤ Real.log (rationalSizeCeiling2 d N:ℝ) := Real.log_nonneg (by linarith)
    have hc0 : 0 ≤ 48*(d:ℝ)/(N:ℝ)^(1/2:ℝ) := by positivity
    rw [ht, Real.rpow_neg hN0.le]
    calc ((rationalSizeCeiling2 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling2 d N:ℝ)-1)*
          (1+Real.log (rationalSizeCeiling2 d N:ℝ))
        ≤ 48*(d:ℝ)/(N:ℝ)^(1/2:ℝ)*(1+Real.log 2+Real.log (N:ℝ)) :=
          mul_le_mul ht' (by linarith) (by linarith) hc0
      _ = 48*(d:ℝ)*((1+Real.log 2)*((N:ℝ)^(1/2:ℝ))⁻¹+
          Real.log (N:ℝ)/(N:ℝ)^(1/2:ℝ)) := by ring

end SphericalRiesz
end
end

section

/-! The logarithmic energy on S²: sharp upper bound at every large `N` and the two-sided
asymptotics (stage LOG).

For every tolerance index the block construction gives configurations at all rational sizes
`(d m)²` with a Gaussian window, a macroscopic budget at the exponent `s = -1` and a bounded
short-range cost.  A diagonal choice over the tolerance index gives one configuration of size
`M(N) ≥ N` for every large `N`, with `(1 - (N-1)/(M-1))(1 + log M) → 0`; the Gaussian-only
bridge bounds its normalized logarithmic energy by `C_log + η/2`.  A subconfiguration of `N`
points whose pair average of `-log |x_i - x_j|` does not exceed that of the whole configuration
(no sign condition is needed) has normalized logarithmic energy at most

`θ nE(X) + (1-θ)(-W) + (1/2)(log N - θ log M)`,  `θ = (N-1)/(M-1)`,

which is at most `C_log + η` for large `N`.  The upper half uses no Gaussian certificate; the
stratification of the residual regions is proved in `Riesz.SphereStratification2`.  The
two-sided statement assumes all-scale Hex contact certificates (stage G2) for its lower
half. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

/-- The ordered off-diagonal logarithmic energy as a full pair sum with zero diagonal. -/
theorem energyLogD_eq_orderedPairS2 {d N : ℕ} (X : ConfigurationD d N) :
    energyLogD X = finiteOrderedPair
      (fun i j : Fin N => if i = j then (0:ℝ) else -Real.log (dist (X i) (X j))) := by
  unfold energyLogD finiteOrderedPair
  refine Finset.sum_congr rfl fun i _ => ?_
  show (∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j))) =
    ∑ j : Fin N, (if i = j then (0:ℝ) else -Real.log (dist (X i) (X j)))
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin N => if i = j then (0:ℝ) else -Real.log (dist (X i) (X j)))
    (Finset.mem_univ i), ite_eq_left rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj).symm]

/-- A subconfiguration of `N` points whose pair average of the logarithmic energy is at most
that of the whole configuration. -/
theorem energyLogD_exists_subconfigurationS2 {d : ℕ} (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : ConfigurationD d M) :
    ∃ e : Fin N ↪ Fin M,
      energyLogD (e.trans X)/((N:ℝ)*(N-1)) ≤ energyLogD X/((M:ℝ)*(M-1)) := by
  obtain ⟨e, he⟩ := finiteOrderedPair_exists_subembedding N M hN hNM
    (fun i j : Fin M => if i = j then (0:ℝ) else -Real.log (dist (X i) (X j)))
    (fun i j => by
      show (if i = j then (0:ℝ) else -Real.log (dist (X i) (X j))) =
        if j = i then (0:ℝ) else -Real.log (dist (X j) (X i))
      by_cases h : i = j
      · subst h
        rfl
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h), dist_comm])
    (fun i => ite_eq_left rfl)
  refine ⟨e, ?_⟩
  have hX := energyLogD_eq_orderedPairS2 X
  have hY : energyLogD (e.trans X) = finiteOrderedPair (fun i j : Fin N =>
      if e i = e j then (0:ℝ) else -Real.log (dist (X (e i)) (X (e j)))) := by
    rw [energyLogD_eq_orderedPairS2]
    unfold finiteOrderedPair
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show (if i = j then (0:ℝ) else -Real.log (dist ((e.trans X) i) ((e.trans X) j))) =
      if e i = e j then (0:ℝ) else -Real.log (dist (X (e i)) (X (e j)))
    by_cases h : i = j
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · have h' : e i ≠ e j := fun he' => h (e.injective he')
      rw [ite_eq_right h, ite_eq_right h']
      rfl
  rw [hY, hX]
  exact he

/-- A subconfiguration of `N` points keeps the normalized logarithmic energy on S² up to the
gap terms, `θ = (N-1)/(M-1)`. -/
theorem normalizedEnergyLog2_exists_subconfiguration (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : ConfigurationD 2 M) :
    ∃ Y : ConfigurationD 2 N, normalizedEnergyLog2 Y ≤
      ((N:ℝ)-1)/((M:ℝ)-1)*normalizedEnergyLog2 X+
        (1-((N:ℝ)-1)/((M:ℝ)-1))*(-sphereLogConst2)+
        (1/2)*(Real.log N-((N:ℝ)-1)/((M:ℝ)-1)*Real.log M) := by
  obtain ⟨e, he⟩ := energyLogD_exists_subconfigurationS2 N M hN hNM X
  refine ⟨e.trans X, ?_⟩
  have hNR : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNM' : (N:ℝ) ≤ M := by exact_mod_cast hNM
  unfold normalizedEnergyLog2
  exact logSubconfiguration_arithS2 hNR hNM' he

/-- The residual constant of the logarithmic blocks is nonnegative. -/
theorem hexLogBlockConst2_nonneg {s p Bst : ℝ} (hs : -2 < s) (hp11 : p < 0)
    (hBst : 0 ≤ Bst) : 0 ≤ hexLogBlockConst2 s p Bst := by
  have hp2 : 0 < s/2+1 := by linarith
  have h11 : 0 < -p := by linarith
  unfold hexLogBlockConst2 hexNegBlockConst2
  positivity

/-- The macroscopic budget of a block at the cutoff `w = 1` is bounded uniformly in the
tolerance index. -/
theorem hexLogBlock_macro_uniform {s A C L : ℝ} (hs : -2 < s) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    2*(A*((1:ℝ)^(s/2+2)/(s/2+2))+1/L*((1:ℝ)^(s/2+1)/(s/2+1)))+2*(C/L^2) ≤
      2*(A/(s/2+2)+1/(s/2+1))+2*C := by
  have hp2 : 0 < s/2+1 := by linarith
  have hL0 : 0 < L := by linarith
  have h1L : 1/L ≤ 1 := (div_le_one hL0).mpr hL
  have h2 : 1/L*(1/(s/2+1)) ≤ 1/(s/2+1) := by
    calc 1/L*(1/(s/2+1)) ≤ 1*(1/(s/2+1)) :=
          mul_le_mul_of_nonneg_right h1L (one_div_pos.mpr hp2).le
      _ = 1/(s/2+1) := one_mul _
  have h3 : C/L^2 ≤ C := div_le_self hC (one_le_pow₀ hL)
  have e1 : A*(1/(s/2+2)) = A/(s/2+2) := mul_one_div _ _
  rw [Real.one_rpow, Real.one_rpow]
  linarith

/-- The window of a block at `α = 1/2` is bounded uniformly in the tolerance index. -/
theorem hexLogBlock_window_uniform {C L : ℝ} (hC : 0 ≤ C) (hL : 2 ≤ L) :
    (1+1/L)*(hexGaussianThetaReal2 (1/2*(1-1/L)^2)+2/L)+(1+L)*(C/L^2) ≤
      2*(hexGaussianThetaReal2 (1/8)+1)+C := by
  have hL0 : 0 < L := by linarith
  have h1L : 1/L ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hL
  have h1L0 : 0 < 1/L := one_div_pos.mpr hL0
  have h2L : 2/L ≤ 1 := (div_le_one hL0).mpr hL
  have h2L0 : 0 ≤ 2/L := div_nonneg (by norm_num) hL0.le
  have hge : (1/2:ℝ) ≤ 1-1/L := by linarith
  have hsq : (1/2:ℝ)^2 ≤ (1-1/L)^2 := pow_le_pow_left₀ (by norm_num) hge 2
  have harg : (1/8:ℝ) ≤ 1/2*(1-1/L)^2 := by nlinarith [hsq]
  have hθ := hexGaussianThetaReal2_anti (by norm_num : (0:ℝ) < 1/8) harg
  have hθ1 := hexGaussianThetaReal2_ge_one (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/8) harg)
  have hfirst : (1+1/L)*(hexGaussianThetaReal2 (1/2*(1-1/L)^2)+2/L) ≤
      2*(hexGaussianThetaReal2 (1/8)+1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hL2 : 0 < L^2 := pow_pos hL0 2
  have hpoly : 1+L ≤ L^2 := by nlinarith [sq_nonneg (L-2)]
  have hsecond : (1+L)*(C/L^2) ≤ C := by
    calc (1+L)*(C/L^2) = C*((1+L)/L^2) := by ring
      _ ≤ C*1 := mul_le_mul_of_nonneg_left ((div_le_one hL2).mpr hpoly) hC
      _ = C := mul_one C
  linarith

/-- Configurations of every large size with normalized logarithmic energy at most `C_log + η`,
for one choice of the auxiliary exponents and given the stratification of the residual
regions. -/
theorem sphere2_log_upper_allN_of_block {s p : ℝ} (hs : -2 < s) (hs0 : s < 0) (hp0 : -1 < p)
    (hp11 : p < 0) {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : HexResidualStratifiable2 Bst) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      normalizedEnergyLog2 Y ≤ sphereLogCoefficient2+η := by
  intro η hη
  have hC0 := hexLogBlockConst2_nonneg (p := p) hs hp11 hBst
  -- blocks for every tolerance index
  have hblocks : ∀ j : ℕ, ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ X : ConfigurationD 2 ((d*m)^2),
        (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(hexGaussianThetaReal2 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(hexLogBlockConst2 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
            2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+
              1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(hexLogBlockConst2 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 ((d*m)^2)) p) X/
          (((d*m)^2:ℕ):ℝ) ≤ hexLogBlockTailConst2 s p Bst :=
    fun j => exists_hex_log_block2 hs hs0 hp0 hp11 hBst hstrat (L := j+2) (by omega)
  choose d hd hev using hblocks
  -- every tolerance index reaches every large N
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop,
      (1-((N:ℝ)-1)/((rationalSizeCeiling2 (d j) N:ℝ)-1))*
        (1+Real.log (rationalSizeCeiling2 (d j) N:ℝ)) ≤ 1/((j:ℝ)+1) ∧
      ∃ X : ConfigurationD 2 (rationalSizeCeiling2 (d j) N),
        (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled2 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(hexGaussianThetaReal2 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(hexLogBlockConst2 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) ≤
            2*(hexMacroConstA2*(w^(s/2+2)/(s/2+2))+
              1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(hexLogBlockConst2 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        cellPairSum (shortRangeKernel2
          (sphereGaussianDensityFactor2 (rationalSizeCeiling2 (d j) N)) p) X/
          ((rationalSizeCeiling2 (d j) N:ℕ):ℝ) ≤ hexLogBlockTailConst2 s p Bst := by
    intro j
    have h1 := (rationalSizeIndex2_tendsto (d j) (hd j)).eventually (hev j)
    have hgap : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
    have h2 := (tendsto_order.mp (rationalSizeCeiling2_log_gap_tendsto (d j) (hd j))).2 _ hgap
    filter_upwards [h1, h2] with N hN1 hN2
    exact ⟨hN2.le, hN1⟩
  obtain ⟨J, hJt, hJ⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hJ
  obtain ⟨N₂, hN₂1, hN₂2⟩ : ∃ N₂ : ℕ, N₁ ≤ N₂ ∧ 2 ≤ N₂ :=
    ⟨max N₁ 2, le_max_left _ _, le_max_right _ _⟩
  -- one configuration for every index k, of size M k ≥ N₂ + k
  have hQ := fun k : ℕ => hN₁ (N₂+k) (hN₂1.trans (Nat.le_add_right N₂ k))
  choose hgapk Z hZW hZM hZT using hQ
  have hge : ∀ k : ℕ, N₂+k ≤ rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k) := fun k =>
    rationalSizeCeiling2_ge _ _ (hd _)
  have hMt : Tendsto (fun k : ℕ => rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k)) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_add_left k N₂).trans (hge k)) tendsto_id
  have hMpos : ∀ k : ℕ, 0 < rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k) := fun k =>
    lt_of_lt_of_le (by omega) (hge k)
  have hidx : Tendsto (fun k : ℕ => N₂+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₂) tendsto_id
  have hLt : Tendsto (fun k : ℕ => J (N₂+k)+2) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (J (N₂+k)) 2) (hJt.comp hidx)
  have hL2 : ∀ k : ℕ, (2:ℝ) ≤ ((J (N₂+k)+2:ℕ):ℝ) := fun k => by
    exact_mod_cast Nat.le_add_left 2 (J (N₂+k))
  -- the pointwise window
  have hprofile : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (Z k) ≤ hexGaussianThetaReal2 α+ε := by
    intro α hα ε hε
    have hΦ := hexBlockWindowBound_tendsto (B := hexLogBlockConst2 s p Bst) hα hLt
    have e1 := (tendsto_order.mp hΦ).2 (hexGaussianThetaReal2 α+ε) (by linarith)
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hu : Tendsto (fun k : ℕ => 1/((J (N₂+k)+2:ℕ):ℝ)) atTop (𝓝 0) :=
      hone.div_atTop (tendsto_natCast_atTop_atTop.comp hLt)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with k hk1 hk2
    exact (hZW k α hk2.le).trans hk1.le
  -- the three uniform budgets
  have hBk : ∀ k : ℕ, (∫ β in Ioc (0:ℝ) 1,
      β^(s/2-1)*(sphereGaussianCenteredScaled2 β (Z k)+1)) ≤
      2*(hexMacroConstA2/(s/2+2)+1/(s/2+1))+2*hexLogBlockConst2 s p Bst := fun k =>
    (hZM k 1 one_pos le_rfl).trans
      (hexLogBlock_macro_uniform hs hC0 (by linarith [hL2 k]))
  have hWk : ∀ k : ℕ, sphereGaussianFullScaled2 (1/2) (Z k) ≤
      2*(hexGaussianThetaReal2 (1/8)+1)+hexLogBlockConst2 s p Bst := fun k =>
    (hZW k (1/2) (one_div_le_one_div_of_le (by norm_num) (hL2 k))).trans
      (hexLogBlock_window_uniform hC0 (hL2 k))
  have hfin := sphere2_log_upper_of_gaussian_budgets hs hs0 hp0 hp11 hMt hMpos Z
    (2*(hexMacroConstA2/(s/2+2)+1/(s/2+1))+2*hexLogBlockConst2 s p Bst)
    (2*(hexGaussianThetaReal2 (1/8)+1)+hexLogBlockConst2 s p Bst)
    (hexLogBlockTailConst2 s p Bst) hBk hWk hZT hprofile (η/2) (half_pos hη)
  -- the gap terms tend to zero
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ,
      Kc = |sphereLogCoefficient2+η/2|+|sphereLogConst2|+1 := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    positivity
  have hJR : Tendsto (fun k : ℕ => (J (N₂+k):ℝ)+1) atTop atTop :=
    tendsto_atTop_mono
      (fun k => (le_add_of_nonneg_right zero_le_one : (J (N₂+k):ℝ) ≤ (J (N₂+k):ℝ)+1))
      (tendsto_natCast_atTop_atTop.comp (hJt.comp hidx))
  have hsmall : Tendsto (fun k : ℕ => Kc*(1/((J (N₂+k):ℝ)+1))) atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hone.div_atTop hJR).const_mul Kc
    rw [mul_zero] at h
    exact h
  have e3 := (tendsto_order.mp hsmall).2 (η/2) (half_pos hη)
  -- subconfigurations of every large size
  have hall : ∀ᶠ k : ℕ in atTop, ∃ Y : ConfigurationD 2 (N₂+k),
      normalizedEnergyLog2 Y ≤ sphereLogCoefficient2+η := by
    filter_upwards [hfin, e3] with k hk1 hk3
    obtain ⟨Y, hY⟩ := normalizedEnergyLog2_exists_subconfiguration (N₂+k)
      (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k)) (by omega) (hge k) (Z k)
    refine ⟨Y, ?_⟩
    have hNk : (2:ℝ) ≤ ((N₂+k:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ N₂+k by omega)
    have hNM : ((N₂+k:ℕ):ℝ) ≤ (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ) := by
      exact_mod_cast hge k
    have hM1 : 0 < (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ)-1 := by linarith
    have hθ0 : 0 ≤ (((N₂+k:ℕ):ℝ)-1)/((rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ)-1) :=
      div_nonneg (by linarith) hM1.le
    have hθ1 : (((N₂+k:ℕ):ℝ)-1)/((rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ)-1) ≤ 1 :=
      (div_le_one hM1).mpr (by linarith)
    have hl : Real.log ((N₂+k:ℕ):ℝ) ≤
        Real.log (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ) :=
      Real.log_le_log (by linarith) hNM
    have hlM : 0 ≤ Real.log (rationalSizeCeiling2 (d (J (N₂+k))) (N₂+k):ℝ) :=
      Real.log_nonneg (by linarith)
    have hb := logSubconfiguration_boundS2 hθ0 hθ1 hl hlM hk1 hY
    rw [← hKcdef] at hb
    have hg := mul_le_mul_of_nonneg_left (hgapk k) hKc0
    linarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hall
  refine ⟨N₂+k₀, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = N₂+k := Nat.exists_eq_add_of_le (by omega)
  exact hk₀ k (by omega)

/-- Sharp upper bound for the logarithmic energy on S² at every large `N`: configurations with
normalized logarithmic energy at most `C_log + η`.  No hypothesis is used. -/
theorem sphere2_log_upper_allN :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      normalizedEnergyLog2 Y ≤ sphereLogCoefficient2+η := by
  obtain ⟨B, hB, hneg, _⟩ := sphere2_stratification_hypotheses
  exact sphere2_log_upper_allN_of_block (s := -1) (p := -1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hB (hexResidualStratifiable2_of_neg hneg)

/-- The sharp upper bound for the logarithmic energy on S² in the form of the conjecture:
actual double integral of `-log |x - y|`, the `-(N/2) log N` term and the coefficient
`½ Re Z'(0) + (1/2) log A₂` (`Z(u) = ζ_Λ(2u)` the continued Hex Epstein zeta function).  No
hypothesis is used. -/
theorem sphere2_log_upper_conjecture_form :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyLogD Y-(∫ p : SphereD 2 × SphereD 2, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2+
            (N:ℝ)/2*Real.log N)/(N:ℝ) ≤
        (1/2)*(deriv hexEpsteinZetaCont 0).re+
          (1/2)*Real.log ((sphereAreaD 2).real univ)+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere2_log_upper_allN η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rw [← sphereLogConst2_eq_pair_integral, ← sphereLogCoefficient2_eq_epstein]
  exact hY

/-- The two-sided logarithmic asymptotics on S² in the form of the conjecture:
`(E_log - W N² + (N/2) log N)/N → ½ Re Z'(0) + (1/2) log A₂` (all configurations above, some
configuration below, every large `N`).  The lower half assumes all-scale Hex contact
certificates (stage G2); the upper half is unconditional. -/
theorem sphere2_log_sharp_asymptotic
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (1/2)*(deriv hexEpsteinZetaCont 0).re+
          (1/2)*Real.log ((sphereAreaD 2).real univ)-η ≤
        (energyLogD X-(∫ p : SphereD 2 × SphereD 2, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2+
            (N:ℝ)/2*Real.log N)/(N:ℝ)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyLogD Y-(∫ p : SphereD 2 × SphereD 2, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2+
            (N:ℝ)/2*Real.log N)/(N:ℝ) ≤
        (1/2)*(deriv hexEpsteinZetaCont 0).re+
          (1/2)*Real.log ((sphereAreaD 2).real univ)+η) :=
  ⟨sphere2_log_lower_conjecture_form hG2, sphere2_log_upper_conjecture_form⟩

theorem sphere2_log_sharp_asymptotic_unconditional :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (1/2)*(deriv hexEpsteinZetaCont 0).re+
          (1/2)*Real.log ((sphereAreaD 2).real univ)-η ≤
        (energyLogD X-(∫ p : SphereD 2 × SphereD 2, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2+
            (N:ℝ)/2*Real.log N)/(N:ℝ)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 2 N,
      (energyLogD Y-(∫ p : SphereD 2 × SphereD 2, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2+
            (N:ℝ)/2*Real.log N)/(N:ℝ) ≤
        (1/2)*(deriv hexEpsteinZetaCont 0).re+
          (1/2)*Real.log ((sphereAreaD 2).real univ)+η) :=
  sphere2_log_sharp_asymptotic hexGaussianContact_all

end SphericalRiesz
end
end
end
