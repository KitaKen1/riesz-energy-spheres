import Riesz.PatchLongRangeBound8
import Riesz.PatchGaussianDefectSmall8
import Riesz.SphereNegMacroBlock8

/-! The patch part of the negative-exponent macroscopic end (stage NEG).

With `c ε² = π n²` the patch scale parameter at `t = cα` is `τ = 2π n² α`. For `τ ≤ 1` the small-`τ`
patch defect gives `block_G(cα) ≤ N C₃ α/(n² δ)` (linear in `α`), and for `α ≤ 1` the earlier
bound gives `N (C₁ α² + C₂/(n⁴ δ))`. Integrating against `α^p`, `-2 < p < -1`, over `(0, w]`:
`block_{K'} ≤ N (C₁ w^(p+3)/(p+3) + (C₃/(p+2) + C₂/(-(p+1))) (2π)^(-(p+1)) n^(-2p-6)/δ)`
(using `α₀ = 1/(2π n²)`), small for small `w` and large `n`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The pointwise patch Gaussian defect at `t = cα` for `2π n² α ≤ 1`: linear in `α`. -/
theorem rationalPatchDefect_alpha_small_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C₃ : ℝ, 0 ≤ C₃ ∧
      ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m),
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d)) →
      (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      ∀ α : ℝ, 0 < α → 2*Real.pi*((a*m:ℕ):ℝ)^2*α ≤ 1 →
      kernelBlock8 (sphereGaussianKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)*α))
          (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ) ≤
        (((d*m)^8:ℕ):ℝ)*(C₃*α/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)) := by
  obtain ⟨ρ, hρ, hρ1, hdef⟩ := rationalPatchDefect_le_small
  set Kb := bumpErrorConstSmall patchChartUpper8 patchChartLower8 with hKbdef
  have hKb : 0 ≤ Kb := by
    rw [hKbdef, bumpErrorConstSmall, sixthConstSmall]
    positivity
  refine ⟨ρ, hρ, hρ1, (8:ℝ)^((9:ℝ)/2)*Kb^2*(2*Real.pi), by positivity, ?_⟩
  intro K P hdis hsmall a d m ha hd hm hε hdens α hα hτ1
  have hm0 : 0 < m := by omega
  have hN : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd hm0) 8
  obtain ⟨c, hcdef⟩ : ∃ c, c = sphereGaussianDensityFactor8 ((d*m)^8) := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ sphereGaussianDensityFactor8_pos hN
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ((a:ℝ)/d)^8 := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (((d*m)^8:ℕ):ℝ) := ⟨_, rfl⟩
  rw [← hcdef, ← hndef, ← hδdef, ← hNdef]
  rw [← hndef] at hτ1
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm0
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hNn : N*δ = n^8 := by
    rw [hNdef, hδdef, hndef]; push_cast; field_simp
  have hcε : c*ε^2 = Real.pi*n^2 := by
    rw [hcdef, hεdef, hndef]; exact densityFactor_scale_sq a d m ha hd hm0
  have ht : 0 < c*α := mul_pos hc hα
  have hτ : 2*(c*α)*ε^2 = 2*Real.pi*n^2*α := by
    rw [show 2*(c*α)*ε^2 = 2*α*(c*ε^2) by ring, hcε]; ring
  have hτ1' : 2*(c*α)*ε^2 ≤ 1 := by rw [hτ]; exact hτ1
  have hβ : 2*(c*α)*ε^2*patchChartLower8^2/128 ≤ ((a*m:ℕ):ℝ)^2 := by
    have hC0 := patchChartLower8_le_half
    have hC0pos := patchChartLower8_pos
    have hC0' : patchChartLower8^2 ≤ 1/4 := by nlinarith
    rw [← hndef]
    have hτ0 : 0 ≤ 2*(c*α)*ε^2 := by positivity
    have h1 : 2*(c*α)*ε^2*patchChartLower8^2/128 ≤ 1 := by
      have : 2*(c*α)*ε^2*patchChartLower8^2 ≤ 1*1 :=
        mul_le_mul hτ1' (hC0'.trans (by norm_num)) (sq_nonneg _) zero_le_one
      linarith
    have hn1 : 1 ≤ n := by
      rw [hndef]
      have : 1 ≤ a*m := Nat.mul_pos ha hm0
      exact_mod_cast this
    nlinarith
  have hD := hdef P hdis hsmall a d m ha hd hm (ε := ε) (fun i => (hε i).trans hεdef.symm) hdens
    (c*α) ht hτ1' hβ
  rw [← hNdef, ← hndef, ← hδdef] at hD
  rw [gaussianKernelBlock8_eq ht.le]
  refine hD.trans ?_
  have hB1 : sphereGaussianBackground8 (c*α/8) ≤ 1 :=
    sphereGaussianBackground8_le_one (by positivity)
  have hB0 : 0 ≤ sphereGaussianBackground8 (c*α/8) := sphereGaussianBackground8_nonneg _
  have hsq : Real.sqrt (2*(c*α)*ε^2)^2 = 2*Real.pi*n^2*α := by
    rw [Real.sq_sqrt (by positivity), hτ]
  have h8 : (0:ℝ) ≤ (8:ℝ)^((9:ℝ)/2) := by positivity
  calc (8:ℝ)^((9:ℝ)/2)*(Kb*n^2*Real.sqrt (2*(c*α)*ε^2)/δ)^2*sphereGaussianBackground8 (c*α/8)
      ≤ (8:ℝ)^((9:ℝ)/2)*(Kb*n^2*Real.sqrt (2*(c*α)*ε^2)/δ)^2*1 :=
        mul_le_mul_of_nonneg_left hB1 (by positivity)
    _ = (8:ℝ)^((9:ℝ)/2)*Kb^2*n^4*(Real.sqrt (2*(c*α)*ε^2))^2/δ^2 := by ring
    _ = (8:ℝ)^((9:ℝ)/2)*Kb^2*n^4*(2*Real.pi*n^2*α)/δ^2 := by rw [hsq]
    _ = N*((8:ℝ)^((9:ℝ)/2)*Kb^2*(2*Real.pi)*α/(n^2*δ)) := by
        have hNe : N = n^8/δ := by rw [eq_div_iff hδ.ne']; exact hNn
        rw [hNe]
        field_simp

/-- The patch part of the negative-exponent macroscopic end: for `p > -2` and `0 < w ≤ 1`,
`∫_{(0,w]} α^p block_G(cα) ≤ N (C₁ w^(p+3)/(p+3) + C₄ w^(p+2)/((p+2) n² δ))`. -/
theorem rationalPatch_negMacroIntegral_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C₁ C₄ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₄ ∧
      ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m),
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d)) →
      (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      ∀ {p w : ℝ}, -2 < p → 0 < w → w ≤ 1 →
      (∫ α in Ioc 0 w, α^p*kernelBlock8 (sphereGaussianKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)*α))
          (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)) ≤
        (((d*m)^8:ℕ):ℝ)*(C₁*(w^(p+3)/(p+3))+
          C₄/(((a*m:ℕ):ℝ)^2*((a:ℝ)/d)^8)*(w^(p+2)/(p+2))) := by
  obtain ⟨ρ₁, hρ₁, hρ₁1, C₁, C₂, hC₁, hC₂, hbig⟩ := rationalPatchDefect_alpha_le
  obtain ⟨ρ₂, hρ₂, hρ₂1, C₃, hC₃, hsmallb⟩ := rationalPatchDefect_alpha_small_le
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁1, C₁, C₃+2*Real.pi*C₂, hC₁,
    by positivity, ?_⟩
  intro K P hdis hsmall a d m ha hd hm hε hdens p w hp hw hw1
  have hsm1 : ∀ i, ‖(P i).v‖ ≤ ρ₁ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ₁ := fun i =>
    ⟨(hsmall i).1.trans (min_le_left _ _), (hsmall i).2.trans (min_le_left _ _)⟩
  have hsm2 : ∀ i, ‖(P i).v‖ ≤ ρ₂ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ₂ := fun i =>
    ⟨(hsmall i).1.trans (min_le_right _ _), (hsmall i).2.trans (min_le_right _ _)⟩
  have hm0 : 0 < m := by omega
  have hN : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd hm0) 8
  set c := sphereGaussianDensityFactor8 ((d*m)^8) with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
  set N : ℝ := (((d*m)^8:ℕ):ℝ) with hNdef
  have hN0 : 0 ≤ N := by positivity
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm0
  set δ : ℝ := ((a:ℝ)/d)^8 with hδdef
  have hδ : 0 < δ := by
    have : (0:ℝ) < a := by exact_mod_cast ha
    have : (0:ℝ) < d := by exact_mod_cast hd
    positivity
  set C₄ := C₃+2*Real.pi*C₂ with hC₄def
  set X := rationalCubePatchNodes8 P a m ha hm with hXdef
  set S := ⋃ i, smallE8CubeSet8 (P i) with hSdef
  -- the pointwise majorant on (0, 1]
  have hpt : ∀ α ∈ Ioc (0:ℝ) 1, kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N ≤
      N*(C₁*α^2+C₄*α/(n^2*δ)) := by
    intro α hα
    have hnδ : 0 < n^2*δ := by positivity
    by_cases hτ : 2*Real.pi*n^2*α ≤ 1
    · have h := hsmallb P hdis hsm2 a d m ha hd hm hε hdens α hα.1 hτ
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ hN0
      have h1 : C₃*α/(n^2*δ) ≤ C₄*α/(n^2*δ) := by
        apply div_le_div_of_nonneg_right _ hnδ.le
        apply mul_le_mul_of_nonneg_right _ hα.1.le
        rw [hC₄def]; have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le) hC₂
        linarith
      have h2 : 0 ≤ C₁*α^2 := by positivity
      linarith
    · have h := hbig P hdis hsm1 a d m ha hd hm hε hdens α hα
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ hN0
      replace hτ : 1 < 2*Real.pi*n^2*α := lt_of_not_ge hτ
      have hq : C₂/(n^4*δ) ≤ 2*Real.pi*C₂*α/(n^2*δ) := by
        have he : 2*Real.pi*C₂*α/(n^2*δ) = C₂*(2*Real.pi*n^2*α)/(n^4*δ) := by
          field_simp
        rw [he]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact le_mul_of_one_le_right hC₂ hτ.le
      have hC4 : C₃*α/(n^2*δ) ≥ 0 := div_nonneg (mul_nonneg hC₃ hα.1.le) (by positivity)
      have : C₄*α/(n^2*δ) = C₃*α/(n^2*δ)+2*Real.pi*C₂*α/(n^2*δ) := by
        rw [hC₄def]; ring
      rw [this]
      linarith
  have hw0 : (0:ℝ) ≤ w := hw.le
  have hwp2 : IntegrableOn (fun α : ℝ => α^(p+2)) (Ioc 0 w) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hw0).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hwp1 : IntegrableOn (fun α : ℝ => α^(p+1)) (Ioc 0 w) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hw0).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hrhs : IntegrableOn (fun α : ℝ => N*C₁*α^(p+2)+N*(C₄/(n^2*δ))*α^(p+1)) (Ioc 0 w) :=
    (hwp2.const_mul _).add (hwp1.const_mul _)
  have hptw : ∀ α ∈ Ioc (0:ℝ) w, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N ≤
      N*C₁*α^(p+2)+N*(C₄/(n^2*δ))*α^(p+1) := by
    intro α hα
    have hα1 : α ∈ Ioc (0:ℝ) 1 := ⟨hα.1, hα.2.trans hw1⟩
    have h0 : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
    have hp2 : α^(p+2) = α^p*α^2 := by rw [Real.rpow_add hα.1, Real.rpow_two]
    have hp1 : α^(p+1) = α^p*α := by rw [Real.rpow_add_one hα.1.ne']
    calc α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N ≤ α^p*(N*(C₁*α^2+C₄*α/(n^2*δ))) :=
          mul_le_mul_of_nonneg_left (hpt α hα1) h0
      _ = N*C₁*α^(p+2)+N*(C₄/(n^2*δ))*α^(p+1) := by rw [hp2, hp1]; ring
  have hint : IntegrableOn (fun α : ℝ => α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N)
      (Ioc 0 w) := by
    have hmeas : AEStronglyMeasurable (fun α : ℝ => α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N)
        (volume.restrict (Ioc 0 w)) :=
      ((measurable_id.pow_const p).mul (gaussianBlock_alpha_measurable c X S N).measurable).aestronglyMeasurable
    refine Integrable.mono' hrhs hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
    have hpos : 0 ≤ α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N :=
      mul_nonneg (Real.rpow_nonneg hα.1.le _) (gaussianKernelBlock8_nonneg (mul_nonneg hc.le hα.1.le) _ _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact hptw α hα
  calc (∫ α in Ioc 0 w, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) X S N)
      ≤ ∫ α in Ioc 0 w, (N*C₁*α^(p+2)+N*(C₄/(n^2*δ))*α^(p+1)) :=
        setIntegral_mono_on hint hrhs measurableSet_Ioc hptw
    _ = N*C₁*(w^(p+3)/(p+3))+N*(C₄/(n^2*δ))*(w^(p+2)/(p+2)) := by
        rw [integral_add (hwp2.const_mul _) (hwp1.const_mul _), integral_const_mul,
          integral_const_mul, ← intervalIntegral.integral_of_le hw0,
          ← intervalIntegral.integral_of_le hw0,
          integral_rpow (Or.inl (by linarith : -1 < p+2)),
          integral_rpow (Or.inl (by linarith : -1 < p+1)),
          Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
        ring_nf
    _ = N*(C₁*(w^(p+3)/(p+3))+C₄/(n^2*δ)*(w^(p+2)/(p+2))) := by ring

#print axioms rationalPatchDefect_alpha_small_le
#print axioms rationalPatch_negMacroIntegral_le

end SphericalRiesz
