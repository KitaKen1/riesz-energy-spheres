import Riesz.SphereShortRangeTail8

/-! Short-range energy of density-scale separated families.

If `c·|x-y|² ≥ δ²`, then `k_φ(x,y) ≤ K_δ · e^{-(c/2)|x-y|²}` with
`K_δ = ∫_{α>1} α^p e^{-δ²(α-1/2)} dα`.  Summing over a separated family bounds its short-range
energy by the off-diagonal Gaussian sum at half the scale, which for a sub-family of a
configuration is at most the configuration's own off-diagonal sum, controlled by the normalized
`s = 4` energy. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

/-- The separation constant `K_δ = ∫_{α>1} α^p e^{-δ²(α-1/2)} dα`. -/
def separatedShortRangeConst8 (p δ : ℝ) : ℝ :=
  ∫ α in Ioi (1:ℝ), α^p*Real.exp (-(δ^2*(α-1/2)))

theorem separatedShortRangeConst8_integrable {p δ : ℝ} (hp : -1 < p) (hδ : 0 < δ) :
    IntegrableOn (fun α : ℝ => α^p*Real.exp (-(δ^2*(α-1/2)))) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := p) (p := 1) (b := δ^2) hp one_pos
    (by positivity)
  apply (IntegrableOn.mono_set (h.const_mul (Real.exp (δ^2/2))) (Ioi_subset_Ioi zero_le_one)).congr_fun _
    measurableSet_Ioi
  intro α _
  simp only [Real.rpow_one]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem separatedShortRangeConst8_nonneg (p δ : ℝ) : 0 ≤ separatedShortRangeConst8 p δ :=
  setIntegral_nonneg measurableSet_Ioi fun _α hα =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _) (Real.exp_pos _).le

theorem shortRangeKernel8_le_of_separated {c p δ : ℝ} (hc : 0 < c) (hp : -1 < p) (hδ : 0 < δ)
    {x y : Sphere8} (hsep : δ^2 ≤ c*dist x y^2) :
    shortRangeKernel8 c p x y ≤ separatedShortRangeConst8 p δ*sphereGaussianKernel8 (c/2) x y := by
  have hi := separatedShortRangeConst8_integrable hp hδ
  have hpt : ∀ α ∈ Ioi (1:ℝ), α^p*sphereGaussianKernel8 (c*α) x y ≤
      sphereGaussianKernel8 (c/2) x y*(α^p*Real.exp (-(δ^2*(α-1/2)))) := by
    intro α hα
    have hα1 : (1:ℝ) < α := hα
    have hp0 : 0 ≤ α^p := Real.rpow_nonneg (by linarith) _
    unfold sphereGaussianKernel8
    rw [mul_left_comm, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hp0
    apply Real.exp_le_exp.mpr
    have h1 : δ^2*(α-1/2) ≤ c*dist x y^2*(α-1/2) :=
      mul_le_mul_of_nonneg_right hsep (by linarith)
    nlinarith
  have hli : IntegrableOn (fun α : ℝ => α^p*sphereGaussianKernel8 (c*α) x y) (Ioi 1) := by
    apply (hi.const_mul (sphereGaussianKernel8 (c/2) x y)).mono' (by
      apply Measurable.aestronglyMeasurable
      unfold sphereGaussianKernel8
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _) (sphereGaussianKernel8_nonneg _ _ _))]
    exact hpt α hα
  unfold shortRangeKernel8 separatedShortRangeConst8
  rw [mul_comm, ← integral_const_mul]
  exact setIntegral_mono_on hli (hi.const_mul _) measurableSet_Ioi hpt

/-- Pair-sum form: a separated injective family has short-range energy at most `K_δ` times its
off-diagonal Gaussian sum at half the scale. -/
theorem finitePairSum_shortRange_le_of_separated {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c p δ : ℝ} (hc : 0 < c) (hp : -1 < p) (hδ : 0 < δ) (X : ι → Sphere8)
    (hsep : ∀ i j, i ≠ j → δ^2 ≤ c*dist (X i) (X j)^2) :
    finitePairSum (shortRangeKernel8 c p) X ≤
      separatedShortRangeConst8 p δ*(finitePairSum (sphereGaussianKernel8 (c/2)) X-Fintype.card ι) := by
  have hK := separatedShortRangeConst8_nonneg p δ
  have hrow : ∀ i, ∑ j, shortRangeKernel8 c p (X i) (X j) ≤
      separatedShortRangeConst8 p δ*((∑ j, sphereGaussianKernel8 (c/2) (X i) (X j))-1) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      shortRangeKernel8_self c hp.le (X i), sphereGaussianKernel8_self, zero_add, add_sub_cancel_left,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact shortRangeKernel8_le_of_separated hc hp hδ (hsep i j (Finset.mem_erase.mp hj).1.symm)
  unfold finitePairSum
  calc ∑ i, ∑ j, shortRangeKernel8 c p (X i) (X j)
      ≤ ∑ i, separatedShortRangeConst8 p δ*((∑ j, sphereGaussianKernel8 (c/2) (X i) (X j))-1) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
        simp

/-- A sub-family has a smaller off-diagonal Gaussian sum. -/
theorem finitePairSum_gaussian_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ℝ)
    (X : ι → Sphere8) (Z : κ → Sphere8) :
    finitePairSum (sphereGaussianKernel8 t) X-Fintype.card ι ≤
      finitePairSum (sphereGaussianKernel8 t) (Sum.elim X Z)-(Fintype.card ι+Fintype.card κ) := by
  have hs : ∀ x y, sphereGaussianKernel8 t x y = sphereGaussianKernel8 t y x := by
    intro x y
    unfold sphereGaussianKernel8
    rw [dist_comm]
  rw [finitePairSum_sum_elim _ hs]
  have hZ : (Fintype.card κ:ℝ) ≤ finitePairSum (sphereGaussianKernel8 t) Z := by
    unfold finitePairSum
    calc (Fintype.card κ:ℝ) = ∑ j : κ, sphereGaussianKernel8 t (Z j) (Z j) := by simp
      _ ≤ ∑ i, ∑ j, sphereGaussianKernel8 t (Z i) (Z j) := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.single_le_sum (fun j _ => sphereGaussianKernel8_nonneg t (Z i) (Z j))
            (Finset.mem_univ i)
  have hc : 0 ≤ ∑ j, ∑ i, sphereGaussianKernel8 t (X i) (Z j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sphereGaussianKernel8_nonneg _ _ _
  linarith

/-- For a configuration, the off-diagonal Gaussian sum at the half density scale is controlled by
the normalized `s = 4` energy. -/
theorem finitePairSum_gaussian_half_le {N : ℕ} (hN : 0 < N) (Y : Configuration N) {E₀ : ℝ}
    (hE : normalizedEnergy Y ≤ E₀) :
    finitePairSum (sphereGaussianKernel8 (sphereGaussianDensityFactor8 N/2)) (fun i => Y i)-N ≤
      (N:ℝ)*(Real.sqrt 2^9+Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))*4+16) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hscale : sphereGaussianScale8 N (1/2) = sphereGaussianDensityFactor8 N/2 := by
    rw [sphereGaussianScale8_eq_factor]
    ring
  have hF := sphereGaussianCenteredScaled8_le_of_energy_bound hN Y hE (by norm_num : (0:ℝ) < 1/2)
  have hcap := sphereGaussianBackground8_scaled_cap hN (by norm_num : (0:ℝ) < 1/2)
  have hsq : (((1:ℝ)/2)^2)⁻¹ = 4 := by norm_num
  have h4 : (((1:ℝ)/2)^4)⁻¹ = 16 := by norm_num
  rw [hsq] at hF
  rw [h4] at hcap
  unfold sphereGaussianCenteredScaled8 at hF
  rw [hscale] at hF hcap
  have hfull : finitePairSum (sphereGaussianKernel8 (sphereGaussianDensityFactor8 N/2)) (fun i => Y i) =
      ∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 (sphereGaussianDensityFactor8 N/2) (Y i) (Y j) := rfl
  rw [hfull]
  set S := ∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 (sphereGaussianDensityFactor8 N/2) (Y i) (Y j)
  have hdiv : S/(N:ℝ) ≤ Real.sqrt 2^9+Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))*4+16+1 := by
    linarith
  rw [div_le_iff₀ hNR] at hdiv
  nlinarith

end SphericalRiesz
