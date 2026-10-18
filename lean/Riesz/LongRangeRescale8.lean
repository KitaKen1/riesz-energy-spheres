import Riesz.SphereMassSplitAssembly8
import Riesz.GaussianBlockBounds8

/-! Raising the density factor in the long-range block.

For a configuration `Y` of `N` points, `c = c_N` and `λ ≥ 1`, substituting `β = λα` gives
`block_{λc} = λ^{-(p+1)} (block_c + ∫_1^λ β^p D(cβ) dβ)`, and for `β ≥ 1` the Gaussian block
`D(cβ) = N (F(β)+1)` is at most `N K_E` by the `s = 4` energy bound.  Hence
`block_{λc} ≤ block_c + N K_E/(p+1)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz
open Boundary

/-- The `β ≥ 1` constant of the Gaussian profile from the `s = 4` energy. -/
def profileConstE (E : ℝ) : ℝ := Real.sqrt 2^9*(1+|(2/3)*((8/Real.sqrt 210)*E+1)|)

theorem gaussianBlock_config_le {N : ℕ} (hN : 0 < N) (Y : Configuration N) {β : ℝ} (hβ : 1 ≤ β) :
    kernelBlock8 (sphereGaussianKernel8 (sphereGaussianDensityFactor8 N*β)) (fun i => Y i) univ N ≤
      N*profileConstE (normalizedEnergy Y) := by
  have hβ0 : 0 < β := by linarith
  rw [← sphereGaussianScale8_eq_factor, gaussianKernelBlock8_config hN hβ0.le]
  have h := sphereGaussianCenteredScaled8_le_inv_sq hN Y hβ0
  have hNR : (0:ℝ) ≤ N := Nat.cast_nonneg N
  apply mul_le_mul_of_nonneg_left _ hNR
  refine h.trans ?_
  unfold profileConstE
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb2 : 1 ≤ β^2 := one_le_pow₀ hβ
  have h1 : (2/3)*((8/Real.sqrt 210)*normalizedEnergy Y+1)/β^2 ≤
      |(2/3)*((8/Real.sqrt 210)*normalizedEnergy Y+1)| := by
    calc (2/3)*((8/Real.sqrt 210)*normalizedEnergy Y+1)/β^2
        ≤ |(2/3)*((8/Real.sqrt 210)*normalizedEnergy Y+1)|/β^2 :=
          div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |(2/3)*((8/Real.sqrt 210)*normalizedEnergy Y+1)| :=
          div_le_self (abs_nonneg _) hb2
  linarith

/-- Change of variables `β = λα` on `Ioc`. -/
theorem setIntegral_Ioc_comp_mul {h : ℝ → ℝ} {l : ℝ} (hl : 0 < l) :
    ∫ α in Ioc (0:ℝ) 1, h (l*α) = l⁻¹*∫ β in Ioc (0:ℝ) l, h β := by
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  have hind : (Ioc (0:ℝ) 1).indicator (fun α => h (l*α)) =
      fun α => (Ioc (0:ℝ) l).indicator h (l*α) := by
    funext α
    by_cases hα : α ∈ Ioc (0:ℝ) 1
    · have hm : l*α ∈ Ioc (0:ℝ) l := ⟨mul_pos hl hα.1, by nlinarith [hα.2]⟩
      rw [Set.indicator_of_mem hα, Set.indicator_of_mem hm]
    · have hm : l*α ∉ Ioc (0:ℝ) l := by
        intro hm
        apply hα
        constructor
        · by_contra h0
          push_neg at h0
          have := hm.1
          nlinarith
        · by_contra h1
          push_neg at h1
          have := hm.2
          nlinarith
      rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hm]
  rw [hind, Measure.integral_comp_mul_left (fun β => (Ioc (0:ℝ) l).indicator h β) l,
    abs_of_pos (inv_pos.mpr hl), smul_eq_mul]

/-- The long-range block at a larger density factor. -/
theorem longRangeBlock8_rescale_le {N : ℕ} (hN : 0 < N) (Y : Configuration N) {l p : ℝ}
    (hl : 1 ≤ l) (hp : -1 < p) :
    kernelBlock8 (longRangeKernel8 (l*sphereGaussianDensityFactor8 N) p) (fun i => Y i) univ N ≤
      kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => Y i) univ N+
        N*profileConstE (normalizedEnergy Y)/(p+1) := by
  set c := sphereGaussianDensityFactor8 N with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
  have hl0 : 0 < l := by linarith
  have hp1 : 0 < p+1 := by linarith
  set D : ℝ → ℝ := fun β => kernelBlock8 (sphereGaussianKernel8 (c*β)) (fun i => Y i) univ N
    with hDdef
  have hDm : StronglyMeasurable D := gaussianBlock_alpha_measurable c (fun i => Y i) univ N
  set Bd := (Fintype.card (Fin N):ℝ)^2 + 2 * |(N:ℝ)| * (Fintype.card (Fin N):ℝ) + (N:ℝ)^2 with hBd
  have hDb : ∀ β, 0 ≤ β → |D β| ≤ Bd := fun β hβ =>
    gaussianBlock_abs_le (mul_nonneg hc.le hβ) (fun i => Y i) univ N
  set KE := profileConstE (normalizedEnergy Y) with hKE
  have hKE0 : 0 ≤ KE := by rw [hKE, profileConstE]; positivity
  have hDK : ∀ β, 1 ≤ β → D β ≤ N*KE := fun β hβ => gaussianBlock_config_le hN Y hβ
  -- representation of both blocks
  rw [longRangeBlock8_eq (mul_nonneg hl0.le hc.le) hp, longRangeBlock8_eq hc.le hp]
  have hcomp : ∀ α ∈ Ioc (0:ℝ) 1, α^p*kernelBlock8 (sphereGaussianKernel8 (l*c*α))
      (fun i => Y i) univ N = (fun β => (β/l)^p*D β) (l*α) := by
    intro α hα
    simp only [hDdef]
    rw [show l*α/l = α by field_simp, show c*(l*α) = l*c*α by ring]
  rw [setIntegral_congr_fun measurableSet_Ioc hcomp,
    setIntegral_Ioc_comp_mul (h := fun β => (β/l)^p*D β) hl0]
  have hsplit : ∫ β in Ioc (0:ℝ) l, (β/l)^p*D β =
      l^(-p)*((∫ β in Ioc (0:ℝ) 1, β^p*D β)+∫ β in Ioc (1:ℝ) l, β^p*D β) := by
    have hpt : ∀ β ∈ Ioc (0:ℝ) l, (β/l)^p*D β = l^(-p)*(β^p*D β) := by
      intro β hβ
      rw [Real.div_rpow hβ.1.le hl0.le, Real.rpow_neg hl0.le]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul]
    congr 1
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hl]
    have hi1 := weighted_bounded_integrable_Ioc hp zero_le_one hDm (fun β hβ => hDb β hβ.1.le)
    have hi2 : IntegrableOn (fun β : ℝ => β^p*D β) (Ioc 1 l) :=
      (weighted_bounded_integrable_Ioc hp hl0.le hDm (fun β hβ => hDb β hβ.1.le)).mono_set
        (Ioc_subset_Ioc_left zero_le_one)
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi1 hi2
  rw [hsplit]
  have htail : ∫ β in Ioc (1:ℝ) l, β^p*D β ≤ N*KE*(l^(p+1)/(p+1)) := by
    have hw : IntegrableOn (fun β : ℝ => β^p) (Ioc 0 l) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hl0.le).mp
        (intervalIntegral.intervalIntegrable_rpow' hp)
    have hi2 : IntegrableOn (fun β : ℝ => β^p*D β) (Ioc 1 l) :=
      (weighted_bounded_integrable_Ioc hp hl0.le hDm (fun β hβ => hDb β hβ.1.le)).mono_set
        (Ioc_subset_Ioc_left zero_le_one)
    calc ∫ β in Ioc (1:ℝ) l, β^p*D β ≤ ∫ β in Ioc (1:ℝ) l, (N*KE)*β^p := by
          apply setIntegral_mono_on hi2 ((hw.mono_set (Ioc_subset_Ioc_left zero_le_one)).const_mul _)
            measurableSet_Ioc
          intro β hβ
          have h0 : 0 ≤ β^p := Real.rpow_nonneg (by linarith [hβ.1]) _
          rw [mul_comm (N*KE)]
          exact mul_le_mul_of_nonneg_left (hDK β hβ.1.le) h0
      _ ≤ ∫ β in Ioc (0:ℝ) l, (N*KE)*β^p := by
          apply setIntegral_mono_set (hw.const_mul _)
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
            exact mul_nonneg (by positivity) (Real.rpow_nonneg hβ.1.le _)
          · exact Eventually.of_forall (Ioc_subset_Ioc_left zero_le_one)
      _ = N*KE*(l^(p+1)/(p+1)) := by rw [integral_const_mul, weight_integral_Ioc hp hl0.le]
  have hbase : 0 ≤ ∫ β in Ioc (0:ℝ) 1, β^p*D β :=
    setIntegral_nonneg measurableSet_Ioc fun β hβ =>
      mul_nonneg (Real.rpow_nonneg hβ.1.le _) (gaussianKernelBlock8_nonneg
        (mul_nonneg hc.le hβ.1.le) _ _ _)
  have hlp : l⁻¹*l^(-p) = l^(-(p+1)) := by
    rw [Real.rpow_neg hl0.le, Real.rpow_neg hl0.le, Real.rpow_add hl0, Real.rpow_one]
    field_simp
  have hle1 : l^(-(p+1)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hl (by linarith)
  have hcancel : l^(-(p+1))*l^(p+1) = 1 := by
    rw [← Real.rpow_add hl0]; simp
  have hpos : 0 ≤ l^(-(p+1)) := Real.rpow_nonneg hl0.le _
  calc l⁻¹*(l^(-p)*((∫ β in Ioc (0:ℝ) 1, β^p*D β)+∫ β in Ioc (1:ℝ) l, β^p*D β))
      = l^(-(p+1))*(∫ β in Ioc (0:ℝ) 1, β^p*D β)+l^(-(p+1))*(∫ β in Ioc (1:ℝ) l, β^p*D β) := by
        rw [← hlp]; ring
    _ ≤ 1*(∫ β in Ioc (0:ℝ) 1, β^p*D β)+l^(-(p+1))*(N*KE*(l^(p+1)/(p+1))) := by
        gcongr
    _ = (∫ β in Ioc (0:ℝ) 1, β^p*D β)+N*KE/(p+1) := by
        rw [one_mul]
        congr 1
        calc l^(-(p+1))*(N*KE*(l^(p+1)/(p+1))) = N*KE/(p+1)*(l^(-(p+1))*l^(p+1)) := by ring
          _ = N*KE/(p+1) := by rw [hcancel, mul_one]

end SphericalRiesz
