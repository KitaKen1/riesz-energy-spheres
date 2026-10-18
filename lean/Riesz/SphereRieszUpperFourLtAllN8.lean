import Riesz.SphereRieszUpperFourLt8
import Riesz.SphereSharpUpperAllN8

/-! The sharp upper bound for `4 < s < 8` for every large `N`, under the CKMRV contract.

Subconfigurations of the rational-size configurations keep the normalized `s = 4` energy (up to
the factor `√(N/M) → 1`) and only lose pairs.  The density factor changes by
`λ = (N/M)^(1/4) ∈ [2^(-1/4), 1]`; the weighted short-range kernel rescales as
`k(λc) ≤ λ^(-(p+1)) (k(c) + K_r e^{-(c/2)|x-y|²})`, and the half-scale Gaussian sum is
controlled by the energy.  A diagonal choice over `η_j = 1/(j+1)` gives one configuration for
every large `N`, and the known-answer transfer gives the sharp upper bound. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz

/-- Diagonal extraction from countably many eventual properties. -/
theorem exists_diagonal_eventually {P : ℕ → ℕ → Prop} (h : ∀ j, ∀ᶠ N in atTop, P j N) :
    ∃ J : ℕ → ℕ, Tendsto J atTop atTop ∧ ∀ᶠ N in atTop, P (J N) N := by
  classical
  choose T hT using fun j => eventually_atTop.mp (h j)
  let U : ℕ → ℕ := fun j => (Finset.range (j+1)).sup T
  have hTU : ∀ j, T j ≤ U j := fun j => Finset.le_sup (Finset.self_mem_range_succ j)
  have hUmono : Monotone U := by
    intro i j hij
    apply Finset.sup_mono
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  let J : ℕ → ℕ := fun N => Nat.findGreatest (fun j => U j ≤ N) N
  refine ⟨J, ?_, ?_⟩
  · apply tendsto_atTop_atTop.mpr
    intro j₀
    refine ⟨max (U j₀) j₀, fun N hN => ?_⟩
    exact Nat.le_findGreatest ((le_max_right _ _).trans hN) ((le_max_left _ _).trans hN)
  · filter_upwards [eventually_ge_atTop (U 0)] with N hN
    have hspec : U (J N) ≤ N := Nat.findGreatest_spec (P := fun j => U j ≤ N) (Nat.zero_le N) hN
    exact hT (J N) N ((hTU (J N)).trans hspec)

theorem finitePairSum_embedding_le {N M : ℕ} (k : Sphere8 → Sphere8 → ℝ)
    (hk : ∀ x y, 0 ≤ k x y) (e : Fin N ↪ Fin M) (X : Fin M → Sphere8) :
    finitePairSum k (fun i => X (e i)) ≤ finitePairSum k X := by
  classical
  unfold finitePairSum
  have h1 : ∀ a : Fin M, ∑ j : Fin N, k (X a) (X (e j)) ≤ ∑ b, k (X a) (X b) := by
    intro a
    rw [← Finset.sum_map Finset.univ e (fun b => k (X a) (X b))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hk _ _)
  calc ∑ i : Fin N, ∑ j : Fin N, k (X (e i)) (X (e j))
      ≤ ∑ i : Fin N, ∑ b, k (X (e i)) (X b) := Finset.sum_le_sum fun i _ => h1 (e i)
    _ ≤ ∑ a, ∑ b, k (X a) (X b) := by
        rw [← Finset.sum_map Finset.univ e (fun a => ∑ b, k (X a) (X b))]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun a _ _ => Finset.sum_nonneg fun b _ => hk _ _)

/-- The rescaling constant `K_r = ∫_{1/2}^{1} β^p dβ`. -/
def shortRangeRescaleConst8 (p : ℝ) : ℝ := ∫ β in Ioc (1/2:ℝ) 1, β^p

theorem shortRangeRescaleConst8_nonneg (p : ℝ) : 0 ≤ shortRangeRescaleConst8 p :=
  setIntegral_nonneg measurableSet_Ioc fun β hβ =>
    Real.rpow_nonneg (le_trans (by norm_num) (le_of_lt hβ.1)) _

/-- Rescaling the density factor down by `λ ∈ [1/2, 1]`. -/
theorem shortRangeKernel8_rescale_le {c l p : ℝ} (hc : 0 < c) (hl : 1/2 ≤ l) (hl1 : l ≤ 1)
    (hp : -1 < p) (x y : Sphere8) :
    shortRangeKernel8 (l*c) p x y ≤
      l^(-(p+1))*(shortRangeKernel8 c p x y+shortRangeRescaleConst8 p*sphereGaussianKernel8 (c/2) x y) := by
  have hl0 : 0 < l := by linarith
  have hlp : 0 < l^(-(p+1)) := Real.rpow_pos_of_pos hl0 _
  by_cases hxy : x = y
  · subst hxy
    rw [shortRangeKernel8_self (l*c) hp.le x]
    exact mul_nonneg hlp.le (add_nonneg (shortRangeKernel8_nonneg c p x x)
      (mul_nonneg (shortRangeRescaleConst8_nonneg p) (sphereGaussianKernel8_nonneg _ _ _)))
  have hd : 0 < dist x y := dist_pos.mpr hxy
  set g : ℝ → ℝ := fun β => β^p*sphereGaussianKernel8 (c*β) x y with hg
  have hgi : IntegrableOn g (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := p) (p := 1) (b := c*dist x y^2) hp one_pos
      (by positivity)
    apply h.congr_fun _ measurableSet_Ioi
    intro β _
    simp only [hg, sphereGaussianKernel8, Real.rpow_one]
    congr 2
    ring
  -- change of variables β = l α
  have hcv : shortRangeKernel8 (l*c) p x y = l^(-(p+1))*∫ β in Ioi l, g β := by
    unfold shortRangeKernel8
    have h1 : ∀ α ∈ Ioi (1:ℝ), α^p*sphereGaussianKernel8 (l*c*α) x y = l^(-p)*g (l*α) := by
      intro α hα
      have hα0 : 0 < α := zero_lt_one.trans hα
      simp only [hg]
      rw [Real.mul_rpow hl0.le hα0.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hl0,
        show -p+p = 0 by ring, Real.rpow_zero, one_mul]
      congr 2
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
      integral_comp_mul_left_Ioi g 1 hl0, mul_one, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [Real.rpow_neg hl0.le, Real.rpow_neg hl0.le, Real.rpow_add hl0, Real.rpow_one, mul_inv]
  rw [hcv]
  apply mul_le_mul_of_nonneg_left _ hlp.le
  have hsplit : ∫ β in Ioi l, g β = (∫ β in Ioc l 1, g β)+∫ β in Ioi 1, g β := by
    have hU : Ioi l = Ioc l 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi hl1).symm
    rw [hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hgi.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hl0.le)))
      (hgi.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hk : ∫ β in Ioi (1:ℝ), g β = shortRangeKernel8 c p x y := rfl
  have hfirst : ∫ β in Ioc l 1, g β ≤ shortRangeRescaleConst8 p*sphereGaussianKernel8 (c/2) x y := by
    have hb : ∀ β ∈ Ioc l 1, g β ≤ sphereGaussianKernel8 (c/2) x y*β^p := by
      intro β hβ
      have hβ0 : 0 < β := hl0.trans hβ.1
      simp only [hg]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hβ0.le _)
      unfold sphereGaussianKernel8
      apply Real.exp_le_exp.mpr
      have h2 : c/2 ≤ c*β := by nlinarith [hβ.1]
      nlinarith [sq_nonneg (dist x y), mul_le_mul_of_nonneg_right h2 (sq_nonneg (dist x y))]
    have hrp : IntegrableOn (fun β : ℝ => β^p) (Ioc (1/2:ℝ) 1) := by
      apply (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hp).1.mono_set
      intro β hβ
      exact ⟨lt_trans (by norm_num) hβ.1, hβ.2⟩
    calc ∫ β in Ioc l 1, g β
        ≤ ∫ β in Ioc l 1, sphereGaussianKernel8 (c/2) x y*β^p :=
          setIntegral_mono_on (hgi.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hl0.le)))
            ((hrp.mono_set (Ioc_subset_Ioc_left hl)).const_mul _) measurableSet_Ioc hb
      _ = sphereGaussianKernel8 (c/2) x y*∫ β in Ioc l 1, β^p := integral_const_mul _ _
      _ ≤ sphereGaussianKernel8 (c/2) x y*shortRangeRescaleConst8 p := by
          apply mul_le_mul_of_nonneg_left _ (sphereGaussianKernel8_nonneg _ _ _)
          apply setIntegral_mono_set hrp
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
            exact Real.rpow_nonneg (le_trans (by norm_num) (le_of_lt hβ.1)) _
          · exact (Ioc_subset_Ioc_left hl).eventuallyLE
      _ = _ := mul_comm _ _
  rw [hsplit, hk]
  linarith

theorem sphereGaussianDensityFactor8_ratio {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    sphereGaussianDensityFactor8 N = ((N:ℝ)/M)^(1/4:ℝ)*sphereGaussianDensityFactor8 M := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  unfold sphereGaussianDensityFactor8 sphereGaussianScale8
  have h : (N:ℝ)/sphereArea8.real univ = ((N:ℝ)/M)*((M:ℝ)/sphereArea8.real univ) := by
    field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- Joint version of the all-`N` sharp `s = 4` upper bound with a uniform short-range constant. -/
theorem sphere8_joint_sharp_upper_allN
    (hlow4 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X)
    {p : ℝ} (hp1 : -1 < p) (hp : p < 3) :
    ∃ C' : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+η ∧
      finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => Y i)/(N:ℝ) ≤ C' := by
  obtain ⟨C, hC⟩ := sphere8_joint_sharp_upper_subsequence hlow4 hp1 hp
  set Kr := shortRangeRescaleConst8 p with hKr
  have hKr0 : 0 ≤ Kr := shortRangeRescaleConst8_nonneg p
  set E₁ := predictedCoefficient+1 with hE₁
  set Kg := Real.sqrt 2^9+Real.sqrt 2^9*((2/3)*((8/Real.sqrt 210)*E₁+1))*4+16 with hKg
  refine ⟨32*(max C 0+Kr*(max Kg 0+1)), fun η hη hη1 => ?_⟩
  obtain ⟨d, hd, hsub⟩ := hC (η/2) (by positivity) (by linarith)
  have hpoints := (rationalSizeIndex8_tendsto d hd).eventually hsub
  have hfactor : Tendsto (fun N : ℕ =>
      Real.sqrt ((N:ℝ)/(rationalSizeCeiling8 d N:ℝ))*(predictedCoefficient+η/2))
      atTop (𝓝 (predictedCoefficient+η/2)) := by
    simpa only [one_mul] using (rationalSizeCeiling8_sqrt_ratio_tendsto d hd).mul_const
      (predictedCoefficient+η/2)
  have hratio : ∀ᶠ N : ℕ in atTop, (rationalSizeCeiling8 d N:ℝ)/(N:ℝ) < 2 :=
    (rationalSizeCeiling8_ratio_tendsto d hd).eventually_lt_const (by norm_num)
  filter_upwards [hpoints, hfactor.eventually_lt_const (by linarith :
    predictedCoefficient+η/2 < predictedCoefficient+η), eventually_ge_atTop (2:ℕ), hratio]
    with N hX hf hN hr
  obtain ⟨X, hXE, hXS⟩ := hX
  have hXnorm : normalizedEnergy X < predictedCoefficient+η/2 := by
    rw [normalizedEnergy_power_eight (d*rationalSizeIndex8 d N) X]
    exact hXE
  set M := rationalSizeCeiling8 d N with hMdef
  have hNM : N ≤ M := rationalSizeCeiling8_ge d N hd
  have hNpos : 0 < N := by omega
  have hMpos : 0 < M := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hMR : (0:ℝ) < M := by exact_mod_cast hMpos
  obtain ⟨e, he⟩ := normalizedEnergy_exists_subconfiguration N M hN hNM X
  refine ⟨e.trans X, ?_, ?_⟩
  · exact (he.trans (mul_le_mul_of_nonneg_left hXnorm.le (Real.sqrt_nonneg _))).trans_lt hf
  -- the short-range part
  set l := ((N:ℝ)/M)^(1/4:ℝ) with hl
  have hNMR : (N:ℝ)/M ≤ 1 := by
    rw [div_le_one hMR]
    exact_mod_cast hNM
  have hNMR2 : 1/2 ≤ (N:ℝ)/M := by
    have h := hr
    rw [div_lt_iff₀ hNR] at h
    rw [le_div_iff₀ hMR]
    linarith
  have hl1 : l ≤ 1 := Real.rpow_le_one (by positivity) hNMR (by norm_num)
  have hl2 : 1/2 ≤ l := by
    have h1 : (1/2:ℝ) ≤ (1/2:ℝ)^(1/4:ℝ) := by
      rw [show (1/2:ℝ) = (1/2:ℝ)^(1:ℝ) by norm_num]
      rw [← Real.rpow_mul (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have h2 : (1/2:ℝ)^(1/4:ℝ) ≤ l := Real.rpow_le_rpow (by norm_num) hNMR2 (by norm_num)
    linarith
  have hlpow : l^(-(p+1)) ≤ 16 := by
    have h1 : l^(-(p+1)) ≤ (1/2:ℝ)^(-(p+1)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hl2 (by linarith)
    have h2 : (1/2:ℝ)^(-(p+1)) = (2:ℝ)^(p+1) := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
      norm_num
    have h3 : (2:ℝ)^(p+1) ≤ (2:ℝ)^(4:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2:ℝ)^(4:ℝ) = 16 := by norm_num
    linarith
  have hlpos : 0 ≤ l^(-(p+1)) := Real.rpow_nonneg (by positivity) _
  set cM := sphereGaussianDensityFactor8 M with hcM
  have hcM0 : 0 < cM := sphereGaussianDensityFactor8_pos hMpos
  have hcN : sphereGaussianDensityFactor8 N = l*cM := sphereGaussianDensityFactor8_ratio hNpos hMpos
  have hXnorm1 : normalizedEnergy X ≤ E₁ := by rw [hE₁]; linarith
  have hgX := finitePairSum_gaussian_half_le hMpos X hXnorm1
  have hsub := finitePairSum_embedding_le (shortRangeKernel8 (sphereGaussianDensityFactor8 N) p)
    (shortRangeKernel8_nonneg _ p) e (fun i => X i)
  have hres : finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => X i) ≤
      l^(-(p+1))*(finitePairSum (shortRangeKernel8 cM p) (fun i => X i)+
        Kr*finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i)) := by
    rw [hcN]
    have hpt : ∀ a b : Fin M, shortRangeKernel8 (l*cM) p (X a) (X b) ≤
        l^(-(p+1))*(shortRangeKernel8 cM p (X a) (X b)+Kr*sphereGaussianKernel8 (cM/2) (X a) (X b)) :=
      fun a b => shortRangeKernel8_rescale_le hcM0 hl2 hl1 hp1 (X a) (X b)
    calc finitePairSum (shortRangeKernel8 (l*cM) p) (fun i => X i)
        ≤ ∑ a : Fin M, ∑ b : Fin M,
            l^(-(p+1))*(shortRangeKernel8 cM p (X a) (X b)+Kr*sphereGaussianKernel8 (cM/2) (X a) (X b)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = _ := by
          unfold finitePairSum
          simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
          rfl
  have hXS0 : finitePairSum (shortRangeKernel8 cM p) (fun i => X i)/(M:ℝ) ≤ C := hXS
  have hXS' : finitePairSum (shortRangeKernel8 cM p) (fun i => X i) ≤ M*max C 0 := by
    rw [div_le_iff₀ hMR] at hXS0
    have h2 : C*M ≤ M*max C 0 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hMR.le
    linarith
  have hgX0 : finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i)-M ≤ M*Kg := hgX
  have hgX' : finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i) ≤ M*(max Kg 0+1) := by
    have h1 : M*Kg ≤ M*max Kg 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hMR.le
    linarith
  have hYe : (fun i => (e.trans X) i) = fun i => X (e i) := rfl
  rw [hYe, div_le_iff₀ hNR]
  have hMN : (M:ℝ) ≤ 2*N := by
    have h := hr
    rw [div_lt_iff₀ hNR] at h
    linarith
  calc finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => X (e i))
      ≤ finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 N) p) (fun i => X i) := hsub
    _ ≤ l^(-(p+1))*(finitePairSum (shortRangeKernel8 cM p) (fun i => X i)+
          Kr*finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i)) := hres
    _ ≤ 16*(M*max C 0+Kr*(M*(max Kg 0+1))) := by
        have hin : 0 ≤ finitePairSum (shortRangeKernel8 cM p) (fun i => X i)+
            Kr*finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i) := by
          apply add_nonneg
          · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => shortRangeKernel8_nonneg _ _ _ _
          · exact mul_nonneg hKr0 (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
              sphereGaussianKernel8_nonneg _ _ _)
        calc l^(-(p+1))*(finitePairSum (shortRangeKernel8 cM p) (fun i => X i)+
              Kr*finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i))
            ≤ 16*(finitePairSum (shortRangeKernel8 cM p) (fun i => X i)+
              Kr*finitePairSum (sphereGaussianKernel8 (cM/2)) (fun i => X i)) :=
              mul_le_mul_of_nonneg_right hlpow hin
          _ ≤ 16*(M*max C 0+Kr*(M*(max Kg 0+1))) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              have := mul_le_mul_of_nonneg_left hgX' hKr0
              linarith
    _ ≤ 32*(max C 0+Kr*(max Kg 0+1))*N := by
        have hC0 : 0 ≤ max C 0 := le_max_right _ _
        have hK0 : 0 ≤ Kr*(max Kg 0+1) := mul_nonneg hKr0 (by positivity)
        nlinarith

/-- The sharp upper bound for `4 < s < 8` for every large `N`, under the CKMRV contract. -/
theorem sphere8_riesz_upper_four_lt (D : E8LaplaceSineData8) {s : ℝ} (hs4 : 4 < s) (hs8 : s < 8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      normalizedEnergyRpow s Y ≤ sphereRieszCoefficient8 s+η := by
  have hs : 0 < s := by linarith
  set γ := (8-s)/4 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hp1 : -1 < s/2-1+γ := by rw [hγ]; linarith
  have hp3 : s/2-1+γ < 3 := by rw [hγ]; linarith
  obtain ⟨C', hC'⟩ := sphere8_joint_sharp_upper_allN (sphere8_lower4_of_laplaceSineData D) hp1 hp3
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+1/((j:ℝ)+1) ∧
      finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 N) (s/2-1+γ)) (fun i => Y i)/(N:ℝ) ≤ C' := by
    intro j
    apply hC' _ (by positivity)
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
    linarith
  obtain ⟨J, hJ, hev⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  have hstep : ∀ k : ℕ, ∃ Y : Configuration (k+N₁+1),
      normalizedEnergy Y < predictedCoefficient+1/((J (k+N₁+1):ℝ)+1) ∧
      finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 (k+N₁+1)) (s/2-1+γ))
        (fun i => Y i)/((k+N₁+1:ℕ):ℝ) ≤ C' := fun k => hN₁ (k+N₁+1) (by omega)
  choose X hX using hstep
  have hNt : Tendsto (fun k : ℕ => k+N₁+1) atTop atTop := by
    apply tendsto_atTop_mono (fun k => (by omega : k ≤ k+N₁+1)) tendsto_id
  have hNpos : ∀ k, 0 < k+N₁+1 := fun k => by omega
  have hJt : Tendsto (fun k : ℕ => J (k+N₁+1)) atTop atTop := hJ.comp hNt
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1/((J (k+N₁+1):ℝ)+1) ≤ ε := fun ε hε =>
    hJt.eventually (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε))
  have hmain := sphere8_riesz_upper_four_lt_of_laplaceSineData D hs4 hs8 hNt hNpos X
    (E₀ := predictedCoefficient+1)
    (fun ε hε => by
      filter_upwards [hsmall ε hε] with k hk
      linarith [(hX k).1])
    (fun k => by
      have h1 : 1/((J (k+N₁+1):ℝ)+1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := (Nat.cast_nonneg (J (k+N₁+1)) : (0:ℝ) ≤ J (k+N₁+1))
        linarith
      linarith [(hX k).1])
    (large_tail_of_offDiagonal_tail hs hNpos X
      (large_tail_of_shortRange_bound hs hγ0 hNpos X (Eventually.of_forall fun k => (hX k).2)))
  intro η hη
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hmain η hη)
  refine ⟨k₀+N₁+1, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = k+N₁+1 := ⟨N-N₁-1, by omega⟩
  exact ⟨X k, hk₀ k (by omega)⟩

end SphericalRiesz
