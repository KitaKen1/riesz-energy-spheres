import Riesz.GaussianBlockBounds8

/-! The long-range block of the rational patch nodes is `O(N)`.

With `c = c_N` the density factor, `ε = A^{1/8} a/d` the patch scale and `n = a m`, one has
`c ε² = π n²`.  The patch Gaussian defect bound at `t = cα` then reads, uniformly in the patch
family and in `0 < α ≤ 1`,

  `D_P(cα) ≤ N (C₁ α² + C₂/(n⁴ δ))`,   `δ = (a/d)⁸`,

and the `α^p`-average gives the long-range block bound `N (C₁/(p+3) + C₂/((p+1) n⁴ δ))`.  The
second term depends on the family but tends to zero as `m → ∞`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

theorem patchChartLower8_le_half : patchChartLower8 ≤ 1/2 := by
  unfold patchChartLower8
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [norm_nonneg e8InverseMap]

/-- `c_N ε² = π n²` for the rational scales. -/
theorem densityFactor_scale_sq (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 0 < m) :
    sphereGaussianDensityFactor8 ((d*m)^8)*(equalAreaE8NormalizedScale8 ((a:ℝ)/d))^2 =
      Real.pi*((a*m:ℕ):ℝ)^2 := by
  have hN : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd hm) 8
  have hc := sphereGaussianDensityFactor8_pos hN
  have hc4 := sphereGaussianDensityFactor8_pow_four hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have h4 : (sphereGaussianDensityFactor8 ((d*m)^8)*(equalAreaE8NormalizedScale8 ((a:ℝ)/d))^2)^4 =
      (Real.pi*((a*m:ℕ):ℝ)^2)^4 := by
    unfold equalAreaE8NormalizedScale8
    rw [show (sphereGaussianDensityFactor8 ((d*m)^8)*(sphereAreaRoot8*((a:ℝ)/d))^2)^4 =
      sphereGaussianDensityFactor8 ((d*m)^8)^4*sphereAreaRoot8^8*((a:ℝ)/d)^8 by ring,
      hc4, sphereAreaRoot8_pow]
    push_cast
    field_simp
  have h0 : 0 ≤ sphereGaussianDensityFactor8 ((d*m)^8)*(equalAreaE8NormalizedScale8 ((a:ℝ)/d))^2 :=
    by positivity
  have h1 : 0 ≤ Real.pi*((a*m:ℕ):ℝ)^2 := by positivity
  exact (pow_left_inj₀ h0 h1 (by norm_num : (4:ℕ) ≠ 0)).mp h4

/-- The pointwise patch Gaussian defect at `t = c α`. -/
theorem rationalPatchDefect_alpha_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m),
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d)) →
      (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      ∀ α ∈ Ioc (0:ℝ) 1,
      kernelBlock8 (sphereGaussianKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)*α))
          (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ) ≤
        (((d*m)^8:ℕ):ℝ)*(C₁*α^2+C₂/(((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8)) := by
  obtain ⟨ρ, hρ, hρ1, hdef⟩ := rationalPatchDefect_le
  set Kb := bumpErrorConst patchChartUpper8 patchChartLower8 with hKbdef
  have hKb : 0 ≤ Kb := by
    rw [hKbdef, bumpErrorConst, sixthConst]
    positivity
  set A := sphereArea8.real univ with hAdef
  have hA : 0 < A := by rw [hAdef, sphereArea8_mass_real]; positivity
  refine ⟨ρ, hρ, hρ1, 2*(8:ℝ)^((9:ℝ)/2)*Kb^2*((105/32)*4096*64*Real.pi^2*A),
    2*(8:ℝ)^((9:ℝ)/2)*Kb^2, by positivity, by positivity, ?_⟩
  intro K P hdis hsmall a d m ha hd hm hε hdens α hα
  have hm0 : 0 < m := by omega
  have hN : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd hm0) 8
  obtain ⟨c, hcdef⟩ : ∃ c, c = sphereGaussianDensityFactor8 ((d*m)^8) := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ sphereGaussianDensityFactor8_pos hN
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ((a:ℝ)/d)^8 := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (((d*m)^8:ℕ):ℝ) := ⟨_, rfl⟩
  rw [← hcdef, ← hndef, ← hδdef, ← hNdef]
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm0
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hNn : N*δ = n^8 := by
    rw [hNdef, hδdef, hndef]; push_cast; field_simp
  have hcε : c*ε^2 = Real.pi*n^2 := by
    rw [hcdef, hεdef, hndef]; exact densityFactor_scale_sq a d m ha hd hm0
  have hc4 : c^4*δ*A = Real.pi^4*n^8 := by
    have h := sphereGaussianDensityFactor8_pow_four hN
    rw [← hcdef, ← hAdef] at h
    rw [h, ← hNn, hNdef]
    field_simp
  have ht : 0 < c*α := mul_pos hc hα.1
  -- the β-condition
  have hβ : 2*(c*α)*ε^2*patchChartLower8^2/128 ≤ ((a*m:ℕ):ℝ)^2 := by
    have hC0 := patchChartLower8_le_half
    have hC0pos := patchChartLower8_pos
    have hC0' : patchChartLower8^2 ≤ 1/4 := by nlinarith
    rw [← hndef]
    have h1 : 2*(c*α)*ε^2 = 2*Real.pi*n^2*α := by
      rw [show 2*(c*α)*ε^2 = 2*α*(c*ε^2) by ring, hcε]; ring
    rw [h1]
    have hpa : Real.pi*α ≤ 4 := by
      have := Real.pi_le_four
      nlinarith [Real.pi_pos, hα.1, hα.2]
    have hpa0 : 0 ≤ Real.pi*α := by nlinarith [Real.pi_pos, hα.1]
    have h3 : Real.pi*α*patchChartLower8^2 ≤ 1 := by
      calc Real.pi*α*patchChartLower8^2 ≤ 4*(1/4) :=
            mul_le_mul hpa hC0' (sq_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hn2 : 0 ≤ n^2 := by positivity
    have h4 : 2*Real.pi*n^2*α*patchChartLower8^2/128 = n^2*(Real.pi*α*patchChartLower8^2)/64 := by
      ring
    rw [h4, div_le_iff₀ (by norm_num)]
    nlinarith
  have hD := hdef P hdis hsmall a d m ha hd hm (ε := ε) (fun i => (hε i).trans hεdef.symm) hdens
    (c*α) ht hβ
  rw [← hNdef, ← hndef, ← hδdef] at hD
  rw [gaussianKernelBlock8_eq ht.le]
  refine hD.trans ?_
  -- the scalar estimate
  set τ := 2*(c*α)*ε^2 with hτdef
  have hτ : τ = 2*Real.pi*n^2*α := by
    rw [hτdef, show 2*(c*α)*ε^2 = 2*α*(c*ε^2) by ring, hcε]; ring
  have hB := sphereGaussianBackground8_min_bound (by positivity : 0 < c*α/8)
  have hB1 : sphereGaussianBackground8 (c*α/8) ≤ 1 := hB.trans (min_le_left _ _)
  have hB2 : sphereGaussianBackground8 (c*α/8) ≤ (105/32:ℝ)/(c*α/8)^4 := hB.trans (min_le_right _ _)
  have hB0 : 0 ≤ sphereGaussianBackground8 (c*α/8) := sphereGaussianBackground8_nonneg _
  have hsq : (1+τ^3)^2 ≤ 2+2*τ^6 := by nlinarith [sq_nonneg (1-τ^3)]
  have h8 : (0:ℝ) < (8:ℝ)^((9:ℝ)/2) := by positivity
  have hτB : τ^6*sphereGaussianBackground8 (c*α/8) ≤ (105/32)*4096*64*Real.pi^2*A*δ*n^4*α^2 := by
    have hτ0 : 0 ≤ τ^6 := by positivity
    calc τ^6*sphereGaussianBackground8 (c*α/8) ≤ τ^6*((105/32:ℝ)/(c*α/8)^4) :=
          mul_le_mul_of_nonneg_left hB2 hτ0
      _ = (105/32)*4096*64*Real.pi^2*A*δ*n^4*α^2 := by
          rw [hτ]
          have hα0 : 0 < α := hα.1
          field_simp
          have : c^4 = Real.pi^4*n^8/(δ*A) := by
            field_simp
            linarith [hc4]
          rw [this]
          field_simp
          ring
  calc (8:ℝ)^((9:ℝ)/2)*(Kb*n^2*(1+(2*(c*α)*ε^2)^3)/δ)^2*sphereGaussianBackground8 (c*α/8)
      = (8:ℝ)^((9:ℝ)/2)*Kb^2*n^4/δ^2*((1+τ^3)^2*sphereGaussianBackground8 (c*α/8)) := by
        rw [hτdef]; ring
    _ ≤ (8:ℝ)^((9:ℝ)/2)*Kb^2*n^4/δ^2*((2+2*τ^6)*sphereGaussianBackground8 (c*α/8)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsq hB0
    _ = (8:ℝ)^((9:ℝ)/2)*Kb^2*n^4/δ^2*(2*sphereGaussianBackground8 (c*α/8)+
          2*(τ^6*sphereGaussianBackground8 (c*α/8))) := by ring
    _ ≤ (8:ℝ)^((9:ℝ)/2)*Kb^2*n^4/δ^2*(2*1+2*((105/32)*4096*64*Real.pi^2*A*δ*n^4*α^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = N*(2*(8:ℝ)^((9:ℝ)/2)*Kb^2*((105/32)*4096*64*Real.pi^2*A)*α^2+
          2*(8:ℝ)^((9:ℝ)/2)*Kb^2/(n^4*δ)) := by
        have hNe : N = n^8/δ := by rw [eq_div_iff hδ.ne']; exact hNn
        rw [hNe]
        field_simp
        ring

/-- The long-range block of the rational patch nodes. -/
theorem rationalPatch_longRangeBlock_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m),
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d)) →
      (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      ∀ {p : ℝ}, -1 < p →
      kernelBlock8 (longRangeKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p)
          (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ) ≤
        (((d*m)^8:ℕ):ℝ)*(C₁/(p+3)+C₂/((p+1)*(((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8))) := by
  obtain ⟨ρ, hρ, hρ1, C₁, C₂, hC₁, hC₂, h⟩ := rationalPatchDefect_alpha_le
  refine ⟨ρ, hρ, hρ1, C₁, C₂, hC₁, hC₂, ?_⟩
  intro K P hdis hsmall a d m ha hd hm hε hdens p hp
  have hm0 : 0 < m := by omega
  have hN : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd hm0) 8
  set c := sphereGaussianDensityFactor8 ((d*m)^8) with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
  set N : ℝ := (((d*m)^8:ℕ):ℝ) with hNdef
  set Q : ℝ := C₂/(((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8) with hQdef
  have hQ : 0 ≤ Q := by rw [hQdef]; positivity
  rw [longRangeBlock8_eq hc.le hp]
  have hp3 : -1 < p+2 := by linarith
  have hw := longRange_weight_integrable hp
  have hw2 := longRange_weight_integrable hp3
  have hpt : ∀ α ∈ Ioc (0:ℝ) 1, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α))
      (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) N ≤
      N*C₁*α^(p+2)+N*Q*α^p := by
    intro α hα
    have h0 : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
    have hb := h P hdis hsmall a d m ha hd hm hε hdens α hα
    have hpow : α^(p+2) = α^p*α^2 := by
      rw [Real.rpow_add hα.1, Real.rpow_two]
    calc α^p*kernelBlock8 (sphereGaussianKernel8 (c*α)) (rationalCubePatchNodes8 P a m ha hm)
          (⋃ i, smallE8CubeSet8 (P i)) N ≤ α^p*(N*(C₁*α^2+Q)) := mul_le_mul_of_nonneg_left hb h0
      _ = N*C₁*α^(p+2)+N*Q*α^p := by rw [hpow]; ring
  have hint : IntegrableOn (fun α : ℝ => α^p*kernelBlock8 (sphereGaussianKernel8 (c*α))
      (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) N) (Ioc 0 1) :=
    weighted_bounded_integrable hp
      (gaussianBlock_alpha_measurable c (rationalCubePatchNodes8 P a m ha hm) _ N)
      (fun α hα => gaussianBlock_abs_le (mul_nonneg hc.le hα.1.le) _ _ N)
  have hrhs : IntegrableOn (fun α : ℝ => N*C₁*α^(p+2)+N*Q*α^p) (Ioc 0 1) :=
    (hw2.const_mul (N*C₁)).add (hw.const_mul (N*Q))
  calc ∫ α in Ioc (0:ℝ) 1, α^p*kernelBlock8 (sphereGaussianKernel8 (c*α))
        (rationalCubePatchNodes8 P a m ha hm) (⋃ i, smallE8CubeSet8 (P i)) N
      ≤ ∫ α in Ioc (0:ℝ) 1, (N*C₁*α^(p+2)+N*Q*α^p) :=
        setIntegral_mono_on hint hrhs measurableSet_Ioc hpt
    _ = N*C₁*(1/(p+2+1))+N*Q*(1/(p+1)) := by
        rw [integral_add (hw2.const_mul (N*C₁)) (hw.const_mul (N*Q)), integral_const_mul,
          integral_const_mul, longRange_weight_integral hp3, longRange_weight_integral hp]
    _ = N*(C₁/(p+3)+C₂/((p+1)*(((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8))) := by
        rw [hQdef, show p+2+1 = p+3 by ring]
        have hp1 : p+1 ≠ 0 := by linarith
        have hp3' : p+3 ≠ 0 := by linarith
        have hX : ((a*m:ℕ):ℝ)^4*((a:ℝ)/d)^8 ≠ 0 := by
          have : (0:ℝ) < ((a*m:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos ha (by omega)
          positivity
        field_simp

end SphericalRiesz
