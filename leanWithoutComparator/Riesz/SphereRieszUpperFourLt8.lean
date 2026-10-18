import Riesz.SphereJointUpperSubsequence8

/-! The sharp upper bound for `4 < s < 8` along a sequence, under the CKMRV contract.

Diagonal choice over `η_j = 1/(j+1)` in the joint `s = 4` construction gives configurations with
`N_j → ∞`, normalized `s = 4` energy tending to the sharp coefficient and a uniformly bounded
weighted short-range energy (exponent weight `γ = (8-s)/4`).  The short-range bound gives the
short-range end, and the known-answer transfer gives
`limsup normalizedEnergyRpow s X_j ≤ C_s`. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem sphere8_lower4_of_laplaceSineData (D : E8LaplaceSineData8) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := sphere8_riesz_sharp_lower_of_laplaceSineData D (s := 4) (by norm_num)
    (by norm_num) ε hε
  refine ⟨N₀, fun N hN X => ?_⟩
  have h := hN₀ N hN X
  rwa [sphereRieszCoefficient8_four, normalizedEnergyRpow_four] at h

/-- A diagonal sequence: sharp for `s = 4` with a uniformly bounded short-range energy. -/
theorem sphere8_joint_sharp_sequence (D : E8LaplaceSineData8) {p : ℝ} (hp1 : -1 < p) (hp : p < 3) :
    ∃ C : ℝ, ∃ N : ℕ → ℕ, (∀ j, max j 1 ≤ N j) ∧ ∃ X : ∀ j, Configuration (N j),
      (∀ j, normalizedEnergy (X j) < predictedCoefficient+1/((j:ℝ)+1)) ∧
      (∀ j, finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 (N j)) p)
        (fun i => X j i)/(N j:ℝ) ≤ C) := by
  obtain ⟨C, hC⟩ := sphere8_joint_sharp_upper_subsequence (sphere8_lower4_of_laplaceSineData D) hp1 hp
  have hstep : ∀ j : ℕ, ∃ n : ℕ, max j 1 ≤ n ∧ ∃ Y : Configuration n,
      normalizedEnergy Y < predictedCoefficient+1/((j:ℝ)+1) ∧
      finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 n) p) (fun i => Y i)/(n:ℝ) ≤ C := by
    intro j
    have hη : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
    have hη1 : 1/((j:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
      linarith
    obtain ⟨d, hd, hev⟩ := hC _ hη hη1
    obtain ⟨m, hm, hmj⟩ := (hev.and (eventually_ge_atTop (max j 1))).exists
    obtain ⟨Y, hE, hS⟩ := hm
    refine ⟨(d*m)^8, ?_, Y, ?_, hS⟩
    · have h2 : m ≤ d*m := Nat.le_mul_of_pos_left m hd
      have h3 : d*m ≤ (d*m)^8 := Nat.le_self_pow (by norm_num) _
      omega
    · rw [normalizedEnergy_power_eight]
      exact hE
  choose N hN X hX using hstep
  exact ⟨C, N, hN, X, fun j => (hX j).1, fun j => (hX j).2⟩

/-- The sharp upper bound for `4 < s < 8` along a sequence `N_j → ∞`, under the CKMRV contract. -/
theorem sphere8_riesz_upper_four_lt_sequence (D : E8LaplaceSineData8) {s : ℝ} (hs4 : 4 < s)
    (hs8 : s < 8) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧ ∃ X : ∀ j, Configuration (N j),
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, normalizedEnergyRpow s (X j) ≤ sphereRieszCoefficient8 s+η := by
  have hs : 0 < s := by linarith
  set γ := (8-s)/4 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hp1 : -1 < s/2-1+γ := by rw [hγ]; linarith
  have hp3 : s/2-1+γ < 3 := by rw [hγ]; linarith
  obtain ⟨C, N, hNj, X, hE, hSR⟩ := sphere8_joint_sharp_sequence D hp1 hp3
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => (le_max_left _ _).trans (hNj j)) tendsto_id
  have hNpos : ∀ j, 0 < N j := fun j => lt_of_lt_of_le one_pos ((le_max_right _ _).trans (hNj j))
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, 1/((j:ℝ)+1) ≤ ε := fun ε hε =>
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε)
  refine ⟨N, hNt, X, ?_⟩
  apply sphere8_riesz_upper_four_lt_of_laplaceSineData D hs4 hs8 hNt hNpos X
    (E₀ := predictedCoefficient+1)
  · intro ε hε
    filter_upwards [hsmall ε hε] with j hj
    linarith [hE j]
  · intro j
    have h1 : 1/((j:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
      linarith
    linarith [hE j]
  · exact large_tail_of_offDiagonal_tail hs hNpos X
      (large_tail_of_shortRange_bound hs hγ0 hNpos X (Eventually.of_forall hSR))

end SphericalRiesz
