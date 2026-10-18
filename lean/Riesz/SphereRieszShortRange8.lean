import Riesz.SphereRieszTransfer8

/-! The short-range end of the all-exponent transfer as a pair functional.

The positive part of the centered profile is below the off-diagonal Gaussian sum, so the
short-range end needed for `4 < s < 8` follows from the tail of the off-diagonal Mellin integral,
a sum over pairs of a decreasing function of the pair distance (ready for first-moment
selection of residual points).  For configurations that are separated at the density scale the
tail is exponentially small, uniformly. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem sphereGaussianCenteredScaled8_le_offDiagonal {N : ℕ} (hN : 0 < N) (α : ℝ)
    (X : Configuration N) :
    sphereGaussianCenteredScaled8 α X ≤
      sphereGaussianOffDiagonal8 (sphereGaussianScale8 N α) X/(N:ℝ) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ (N:ℝ)*sphereGaussianBackground8 (sphereGaussianScale8 N α) :=
    mul_nonneg hNR.le (sphereGaussianBackground8_nonneg _)
  rw [sphereGaussianOffDiagonal8_eq_full_sub, sub_div, div_self hNR.ne']
  unfold sphereGaussianCenteredScaled8
  linarith

theorem sphereGaussianOffDiagonalScaled8_weighted_integrable {s : ℝ} (hs : 0 < s) {N : ℕ}
    (hN : 0 < N) (X : Configuration N) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*
      (sphereGaussianOffDiagonal8 (sphereGaussianScale8 N α) X/(N:ℝ))) (Ioi 0) := by
  set c := sphereGaussianDensityFactor8 N with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
  set g : ℝ → ℝ := fun t => t^(s/2-1)*sphereGaussianOffDiagonal8 t X with hg
  have hgi : IntegrableOn g (Ioi 0) := sphereGaussianOffDiagonal8_weighted_integrable_rpow hs X
  have hgc : IntegrableOn (fun α : ℝ => g (c*α)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr
    simpa only [mul_zero] using hgi
  have hcp : 0 < c^(s/2-1) := Real.rpow_pos_of_pos hc _
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hh : IntegrableOn (fun α : ℝ => ((N:ℝ)*c^(s/2-1))⁻¹*g (c*α)) (Ioi 0) := hgc.const_mul _
  apply hh.congr_fun _ measurableSet_Ioi
  intro α hα
  have hα0 : (0:ℝ) < α := hα
  simp only [hg]
  rw [sphereGaussianScale8_eq_factor, ← hcdef, Real.mul_rpow hc.le hα0.le]
  field_simp

/-- The short-range end from the tail of the off-diagonal Mellin integral. -/
theorem large_tail_of_offDiagonal_tail {s : ℝ} (hs : 0 < s)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ)) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      max (α^(s/2-1)*sphereGaussianCenteredScaled8 α (X k)) 0 ≤ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := htail ε hε
  refine ⟨n₀, ?_⟩
  filter_upwards [hn₀] with k hk
  have hi := (sphereGaussianOffDiagonalScaled8_weighted_integrable hs (hN k) (X k)).mono_set
    (Ioi_subset_Ioi (by positivity : (0:ℝ) ≤ (n₀:ℝ)+1))
  refine le_trans ?_ hk
  apply integral_mono_of_nonneg (Eventually.of_forall fun α => le_max_right _ _) hi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  have hα0 : 0 < α := lt_of_le_of_lt (by positivity) hα
  have hw := Real.rpow_pos_of_pos hα0 (s/2-1)
  have hNR : (0:ℝ) < N k := by exact_mod_cast hN k
  apply max_le
  · exact mul_le_mul_of_nonneg_left (sphereGaussianCenteredScaled8_le_offDiagonal (hN k) α (X k)) hw.le
  · exact mul_nonneg hw.le (div_nonneg (sphereGaussianOffDiagonal8_nonneg _ _) hNR.le)

/-- The off-diagonal tail as a sum over ordered pairs. -/
theorem offDiagonal_tail_eq_pair_sum {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (X : Configuration N) (R : ℝ) (hR : 0 ≤ R) :
    ∫ α in Ioi R, α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 N α) X/(N:ℝ)) =
      (N:ℝ)⁻¹*∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j) := by
  have hpair : ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i, IntegrableOn
      (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j))
      (Ioi R) := by
    intro i j hj
    have hd : 0 < dist (X i) (X j) := dist_pos.mpr (X.injective.ne (Finset.mem_erase.mp hj).1.symm)
    set c := sphereGaussianDensityFactor8 N
    have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
    have hb : 0 < c*dist (X i) (X j)^2 := by positivity
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1) (p := 1) (b := c*dist (X i) (X j)^2)
      (by linarith) one_pos hb
    apply (h.mono_set (Ioi_subset_Ioi hR)).congr_fun _ measurableSet_Ioi
    intro α hα
    have hα0 : 0 < α := lt_of_le_of_lt hR hα
    simp only [sphereGaussianKernel8, sphereGaussianScale8_eq_factor, Real.rpow_one]
    congr 2
    ring
  have hrow : ∀ i : Fin N, IntegrableOn (fun α : ℝ => ∑ j ∈ Finset.univ.erase i,
      α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j)) (Ioi R) :=
    fun i => integrable_finsetSum _ (hpair i)
  have hfun : (fun α : ℝ => α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 N α) X/(N:ℝ))) =
      fun α => (N:ℝ)⁻¹*∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (X i) (X j) := by
    funext α
    unfold sphereGaussianOffDiagonal8
    simp only [Finset.mul_sum, div_eq_inv_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, integral_const_mul, integral_finsetSum _ (fun i _ => hrow i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (hpair i)

/-- Density-scale separated sequences with bounded `s = 4` energy have a uniformly small
short-range end. -/
theorem offDiagonal_tail_of_separated {s : ℝ} (hs : 0 < s)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k)) {E₀ δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ k, normalizedEnergy (X k) ≤ E₀)
    (hsep : ∀ k, ∀ i j, i ≠ j →
      δ^2 ≤ sphereGaussianDensityFactor8 (N k)*dist (X k i) (X k j)^2) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ)) ≤ ε := by
  intro ε hε
  set K : ℝ := Real.sqrt 2^9+max (Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))) 0+1 with hKdef
  have hK : 0 ≤ K := by positivity
  set g : ℝ → ℝ := fun α => K*(Real.exp (δ^2)*(α^(s/2-1)*Real.exp (-(δ^2)*α^(1:ℝ)))) with hgdef
  have hgi : IntegrableOn g (Ioi 1) :=
    IntegrableOn.mono_set (((integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1) (p := 1) (b := δ^2)
      (by linarith) one_pos (by positivity)).const_mul (Real.exp (δ^2))).const_mul K)
      (Ioi_subset_Ioi zero_le_one)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp (tendsto_setIntegral_Ioi_nat hgi)) ε hε)
  refine ⟨n₀, Eventually.of_forall fun k => ?_⟩
  have hI := hn₀ n₀ le_rfl
  rw [Real.dist_eq, sub_zero] at hI
  have hsub : Ioi ((n₀:ℝ)+1) ⊆ Ioi 1 := by
    apply Ioi_subset_Ioi
    have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
    linarith
  have hNR : (0:ℝ) < N k := by exact_mod_cast hN k
  set c := sphereGaussianDensityFactor8 (N k) with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos (hN k)
  -- the value at α = 1 is bounded by K
  have h1 : sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) 1) (X k)/(N k:ℝ) ≤ K := by
    have hF := sphereGaussianCenteredScaled8_le_of_energy_bound (hN k) (X k) (hE k) one_pos
    have hcap := sphereGaussianBackground8_scaled_cap (hN k) (one_pos : (0:ℝ) < 1)
    rw [sphereGaussianOffDiagonal8_eq_full_sub, sub_div, div_self hNR.ne']
    unfold sphereGaussianCenteredScaled8 at hF
    have hm : Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))*((1:ℝ)^2)⁻¹ ≤
        max (Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₀+1))) 0 := by
      rw [one_pow, inv_one, mul_one]
      exact le_max_left _ _
    simp only [one_pow, inv_one] at hcap
    rw [hKdef]
    linarith
  -- pointwise decay for α ≥ 1
  have hdecay : ∀ α : ℝ, 1 ≤ α →
      sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k) ≤
        Real.exp (-(δ^2*(α-1)))*sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) 1) (X k) := by
    intro α hα
    unfold sphereGaussianOffDiagonal8
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hsepij := hsep k i j hij
    unfold sphereGaussianKernel8
    rw [← Real.exp_add, sphereGaussianScale8_eq_factor, sphereGaussianScale8_eq_factor, ← hcdef]
    apply Real.exp_le_exp.mpr
    have hd2 := sq_nonneg (dist (X k i) (X k j))
    nlinarith [mul_le_mul_of_nonneg_right hsepij (by linarith : (0:ℝ) ≤ α-1)]
  calc ∫ α in Ioi ((n₀:ℝ)+1),
        α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ))
      ≤ ∫ α in Ioi ((n₀:ℝ)+1), g α := by
        have hnn : 0 ≤ᵐ[volume.restrict (Ioi ((n₀:ℝ)+1))] (fun α : ℝ =>
            α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ))) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
          have hα0 : 0 < α := lt_of_le_of_lt (by positivity) hα
          exact mul_nonneg (Real.rpow_nonneg hα0.le _)
            (div_nonneg (sphereGaussianOffDiagonal8_nonneg _ _) hNR.le)
        have hle : (fun α : ℝ =>
            α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ)))
            ≤ᵐ[volume.restrict (Ioi ((n₀:ℝ)+1))] g := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
          have hα1 : 1 ≤ α := by
            have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
            have : (n₀:ℝ)+1 < α := hα
            linarith
          have hα0 : 0 < α := by linarith
          have hw := Real.rpow_pos_of_pos hα0 (s/2-1)
          have hd := hdecay α hα1
          have he : Real.exp (-(δ^2*(α-1))) = Real.exp (δ^2)*Real.exp (-(δ^2)*α^(1:ℝ)) := by
            rw [Real.rpow_one, ← Real.exp_add]
            congr 1
            ring
          have hq : sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ) ≤
              Real.exp (-(δ^2*(α-1)))*K := by
            rw [div_le_iff₀ hNR]
            calc sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)
                ≤ Real.exp (-(δ^2*(α-1)))*sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) 1)
                    (X k) := hd
              _ = Real.exp (-(δ^2*(α-1)))*((sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) 1)
                    (X k)/(N k:ℝ))*(N k:ℝ)) := by field_simp
              _ ≤ Real.exp (-(δ^2*(α-1)))*(K*(N k:ℝ)) := by
                    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                    exact mul_le_mul_of_nonneg_right h1 hNR.le
              _ = Real.exp (-(δ^2*(α-1)))*K*(N k:ℝ) := by ring
          calc α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ))
              ≤ α^(s/2-1)*(Real.exp (-(δ^2*(α-1)))*K) := mul_le_mul_of_nonneg_left hq hw.le
            _ = g α := by
                simp only [hgdef]
                rw [he]
                ring
        exact integral_mono_of_nonneg hnn (hgi.mono_set hsub) hle
    _ ≤ ε := (le_abs_self _).trans hI.le

end SphericalRiesz
