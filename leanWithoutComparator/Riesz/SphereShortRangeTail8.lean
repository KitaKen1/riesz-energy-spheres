import Riesz.SphereShortRangeResidual8

/-! From the weighted short-range energy to the short-range end of the Mellin transfer.

For a configuration `Y` of `N` points and `R ≥ 1`, every pair tail is dominated by the weighted
short-range kernel, so the off-diagonal Mellin tail beyond `R` is at most
`R^(-γ) · (Σ_{i≠j} k_φ(Y i, Y j))/N`.  A uniform bound on the normalized short-range energy
therefore gives the short-range end required by the all-exponent upper bound for `4 < s < 8`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- Ordered pair sum of a kernel over a finite family. -/
def finitePairSum {ι : Type*} [Fintype ι] (k : Sphere8 → Sphere8 → ℝ) (X : ι → Sphere8) : ℝ :=
  ∑ i, ∑ j, k (X i) (X j)

theorem finitePairSum_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (k : Sphere8 → Sphere8 → ℝ)
    (e : ι ≃ κ) (X : κ → Sphere8) : finitePairSum k (X ∘ e) = finitePairSum k X := by
  have hi (x : Sphere8) : (∑ j, k x (X (e j))) = ∑ j, k x (X j) := e.sum_comp (fun j => k x (X j))
  unfold finitePairSum
  simp only [Function.comp_apply]
  simp_rw [hi]
  exact e.sum_comp (fun i => ∑ j, k (X i) (X j))

theorem finitePairSum_sum_elim {ι κ : Type*} [Fintype ι] [Fintype κ] (k : Sphere8 → Sphere8 → ℝ)
    (hs : ∀ x y, k x y = k y x) (X : ι → Sphere8) (Z : κ → Sphere8) :
    finitePairSum k (Sum.elim X Z) = finitePairSum k X+finitePairSum k Z+
      2*(∑ j, ∑ i, k (X i) (Z j)) := by
  have hcross : (∑ i, ∑ j, k (X i) (Z j)) = ∑ j, ∑ i, k (X i) (Z j) := Finset.sum_comm
  have hrev : (∑ j, ∑ i, k (Z j) (X i)) = ∑ j, ∑ i, k (X i) (Z j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun i _ => hs (Z j) (X i))
  unfold finitePairSum
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
  rw [hcross, hrev]
  ring

theorem finitePairSum_sum_elim_shortRange {p r : ℕ} (c q : ℝ) (X : Fin p → Sphere8)
    (Z : Fin r → Sphere8) :
    finitePairSum (shortRangeKernel8 c q) (Sum.elim X Z) = finitePairSum (shortRangeKernel8 c q) X+
      (residualPairEnergy (shortRangeKernel8 c q) Z+∑ j, shortRangeCrossRow8 c q X (Z j)) := by
  rw [finitePairSum_sum_elim _ (shortRangeKernel8_symm c q)]
  unfold shortRangeCrossRow8 residualPairEnergy finitePairSum
  rw [← Finset.mul_sum]
  ring

/-- The off-diagonal Mellin tail is at most `R^(-γ)` times the normalized short-range energy. -/
theorem offDiagonal_tail_le_shortRange {s γ R : ℝ} (hs : 0 < s) (hγ : 0 ≤ γ) (hR : 1 ≤ R)
    {N : ℕ} (hN : 0 < N) (Y : Configuration N) :
    ∫ α in Ioi R, α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 N α) Y/(N:ℝ)) ≤
      R^(-γ)*(finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 N) (s/2-1+γ))
        (fun i => Y i)/(N:ℝ)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  set c := sphereGaussianDensityFactor8 N with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
  rw [offDiagonal_tail_eq_pair_sum hs hN Y R (zero_le_one.trans hR)]
  have hpair : ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i,
      ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (Y i) (Y j) ≤
        R^(-γ)*shortRangeKernel8 c (s/2-1+γ) (Y i) (Y j) := by
    intro i j hj
    have hij : Y i ≠ Y j := Y.injective.ne (Finset.mem_erase.mp hj).1.symm
    have he : (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (Y i) (Y j)) =
        fun α => α^(s/2-1)*sphereGaussianKernel8 (c*α) (Y i) (Y j) := by
      funext α
      rw [sphereGaussianScale8_eq_factor]
    rw [he]
    exact tail_le_shortRangeKernel8 hc hs hγ hR hij
  have hdiag : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, shortRangeKernel8 c (s/2-1+γ) (Y i) (Y j) =
      ∑ j, shortRangeKernel8 c (s/2-1+γ) (Y i) (Y j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), shortRangeKernel8_self c (by linarith) (Y i),
      zero_add]
  calc (N:ℝ)⁻¹*∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel8 (sphereGaussianScale8 N α) (Y i) (Y j)
      ≤ (N:ℝ)⁻¹*∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
          R^(-γ)*shortRangeKernel8 c (s/2-1+γ) (Y i) (Y j) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNR.le)
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpair i j hj
    _ = R^(-γ)*(finitePairSum (shortRangeKernel8 c (s/2-1+γ)) (fun i => Y i)/(N:ℝ)) := by
        have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, R^(-γ)*shortRangeKernel8 c (s/2-1+γ) (Y i) (Y j) =
            R^(-γ)*∑ j, shortRangeKernel8 c (s/2-1+γ) (Y i) (Y j) := by
          intro i
          rw [← Finset.mul_sum, hdiag i]
        simp_rw [h1]
        unfold finitePairSum
        beta_reduce
        rw [← Finset.mul_sum, div_eq_inv_mul]
        ring

/-- A uniform bound on the normalized short-range energy gives the short-range end. -/
theorem large_tail_of_shortRange_bound {s γ C : ℝ} (hs : 0 < s) (hγ : 0 < γ)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hSR : ∀ᶠ k in atTop, finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 (N k))
      (s/2-1+γ)) (fun i => X k i)/(N k:ℝ) ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ᶠ k in atTop, ∫ α in Ioi ((n₀:ℝ)+1),
      α^(s/2-1)*(sphereGaussianOffDiagonal8 (sphereGaussianScale8 (N k) α) (X k)/(N k:ℝ)) ≤ ε := by
  intro ε hε
  have hC : Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-γ)*max C 0) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop hγ).comp h1
    simpa using h2.mul_const (max C 0)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hC.eventually (ge_mem_nhds hε))
  refine ⟨n₀, ?_⟩
  filter_upwards [hSR] with k hk
  have hR : (1:ℝ) ≤ (n₀:ℝ)+1 := by
    have := (Nat.cast_nonneg n₀ : (0:ℝ) ≤ n₀)
    linarith
  have h := offDiagonal_tail_le_shortRange hs hγ.le hR (hN k) (X k)
  have hpos : 0 ≤ ((n₀:ℝ)+1)^(-γ) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ ((n₀:ℝ)+1)^(-γ)*(finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 (N k))
        (s/2-1+γ)) (fun i => X k i)/(N k:ℝ)) := h
    _ ≤ ((n₀:ℝ)+1)^(-γ)*max C 0 := mul_le_mul_of_nonneg_left (hk.trans (le_max_left _ _)) hpos
    _ ≤ ε := hn₀ n₀ le_rfl

end SphericalRiesz
