import Riesz.NegMassSplit8
import Riesz.NegSharpSubsequence8
import Riesz.SphereRieszUpperFourLtAllN8
import Riesz.SphereRieszNegUpper8

/-! The sharp negative-exponent asymptotics for every large `N` (stage NEG).

For `N` take the rational size `M = (d m)^8 ≤ N` just below it and the configuration `Y_M` of
`sphere8_neg_sharp_upper_subsequence` (sharp for `s = 4`, small macroscopic end), move the
density factor from `c_M` to `c_N` (`negMacroBlock8_rescale`: `K'(l c, t) = l^(-(p+1)) K'(c, l t)`,
`1 ≤ l ≤ 2`), and add the `r = N - M` missing points one per cell of an exact-mass
stratification of the whole sphere at their own scale (`SphereStratifiable8`), jointly for the
`s = 4` kernel and `√N · K'(1)`. Cell costs: `Σ_j c_N d_j² = (N/r)^(1/4) Σ_j c_r d_j²
≤ √(N/r) B r`, which is `o(N)` since `r/N → 0`. Then the configurations are sharp for `s = 4`
and have small macroscopic ends for every large `N`, and the known-answer transfer gives the
sharp lower bound for every `-2 < s < 0` and every large `N`; with the universal upper bound this
is the two-sided sharp asymptotics, modulo the stratification hypotheses. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

/-- Exact-mass stratifications of the whole sphere at every scale: `r` cells of mass `1/r`
with `Σ_j c_r d_j² ≤ B r` (cells at the density scale `r^(-1/8)`). -/
def SphereStratifiable8 (B : ℝ) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ C : Fin r → Set Sphere8, ∃ dm : Fin r → ℝ,
    (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
    (⋃ j, C j) = univ ∧ (∀ j, sphereProbability8 (C j) = sphereProbability8 univ/(r:ℝ≥0∞)) ∧
    (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
    ∑ j, sphereGaussianDensityFactor8 r*(dm j)^2 ≤ B*r

set_option maxHeartbeats 1000000 in
/-- One step of the all-`N` construction for negative exponents. -/
theorem neg_allN_step {p C₁ η B : ℝ} (hp : -2 < p) (hC₁ : 0 ≤ C₁) (hη : 0 < η) (hη1 : η ≤ 1)
    {M N : ℕ} (hM0 : 0 < M) (hMN : M ≤ N) (YM : Configuration M)
    (hYE : normalizedEnergy YM < predictedCoefficient+η/4)
    (hYmac : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α YM+1) ≤ 2*C₁*(t^(p+3)/(p+3))+3*η)
    (hlowN : ∀ X : Configuration N, predictedCoefficient-η/4 ≤ normalizedEnergy X)
    (hq : 1-η/(4*(|predictedCoefficient|+1)) ≤ ((M:ℝ)/N)*Real.sqrt ((M:ℝ)/N))
    (hl16 : (N:ℝ) ≤ 16*M) (hsphere : SphereStratifiable8 B)
    (hrN : B^2*((N:ℝ)-M) ≤ (η*(p+2)/4)^2*N) :
    ∃ Y : Configuration N, normalizedEnergy Y < predictedCoefficient+η ∧
      ∀ t : ℝ, 0 < t → t ≤ 1/2 →
        ∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α Y+1) ≤
          8*2^(p+3)*C₁*(t^(p+3)/(p+3))+15*η := by
  have hp2 : 0 < p+2 := by linarith
  have hp3 : 0 < p+3 := by linarith
  have h2p : (1:ℝ) ≤ 2^(p+3) := Real.one_le_rpow (by norm_num) hp3.le
  rcases eq_or_lt_of_le hMN with hEq | hlt
  · subst hEq
    refine ⟨YM, by linarith, fun t ht ht2 => ?_⟩
    have h := hYmac t ht (by linarith)
    have hT : 0 ≤ C₁*(t^(p+3)/(p+3)) :=
      mul_nonneg hC₁ (div_nonneg (Real.rpow_nonneg ht.le _) hp3.le)
    have h8 : 2*C₁*(t^(p+3)/(p+3)) ≤ 8*2^(p+3)*C₁*(t^(p+3)/(p+3)) := by
      have : 2*(C₁*(t^(p+3)/(p+3))) ≤ (8*2^(p+3))*(C₁*(t^(p+3)/(p+3))) :=
        mul_le_mul_of_nonneg_right (by linarith) hT
      linarith
    linarith
  -- the missing points
  obtain ⟨R, hRdef⟩ : ∃ R, R = |predictedCoefficient|+1 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hRabs : |predictedCoefficient| ≤ R := by rw [hRdef]; linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = η/(4*R) := ⟨_, rfl⟩
  have hN0 : 0 < N := lt_of_lt_of_le hM0 hMN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hMN' : (M:ℝ) ≤ N := by exact_mod_cast hMN
  obtain ⟨r, hr⟩ : ∃ r, M+r = N := ⟨N-M, by omega⟩
  have hr0 : 0 < r := by omega
  have hrR : (r:ℝ) = (N:ℝ)-M := by
    have : ((M+r:ℕ):ℝ) = (N:ℝ) := by rw [hr]
    push_cast at this
    linarith
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr0
  obtain ⟨C, dm, hCm, hdisj, hunion, hmass, hdiam, hsumS⟩ := hsphere r hr0
  -- the density factors
  set c := sphereGaussianDensityFactor8 N with hcdef
  have hc0 : 0 < c := sphereGaussianDensityFactor8_pos hN0
  have hcM := sphereGaussianDensityFactor8_pos hM0
  have hratioM := sphereGaussianDensityFactor8_ratio hN0 hM0
  have hratior := sphereGaussianDensityFactor8_ratio hN0 hr0
  set l := ((N:ℝ)/M)^(1/4:ℝ) with hldef
  have hl1 : 1 ≤ l := Real.one_le_rpow ((one_le_div hMR).mpr hMN') (by norm_num)
  have hl2 : l ≤ 2 := by
    have h16 : (N:ℝ)/M ≤ 16 := by rw [div_le_iff₀ hMR]; linarith
    have h := Real.rpow_le_rpow (by positivity) h16 (by norm_num : (0:ℝ) ≤ 1/4)
    have h2 : (16:ℝ)^(1/4:ℝ) = 2 := by
      rw [show (16:ℝ) = 2^(4:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h2] at h
    exact h
  have hl0 : 0 < l := by linarith
  -- the cell sum
  set Ω := ∑ j, c*(dm j)^2*((1:ℝ)^(p+2)/(p+2)) with hΩdef
  have hΩ : Ω ≤ η/4*N := by
    have h1 : Ω = (∑ j, c*(dm j)^2)/(p+2) := by
      rw [hΩdef, Real.one_rpow, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hsum : (∑ j, c*(dm j)^2) = ((N:ℝ)/r)^(1/4:ℝ)*∑ j, sphereGaussianDensityFactor8 r*(dm j)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hcdef, hratior]
      ring
    have hNr1 : (1:ℝ) ≤ (N:ℝ)/r := by
      rw [one_le_div hrpos, hrR]
      linarith
    have hq4 : ((N:ℝ)/r)^(1/4:ℝ) ≤ Real.sqrt ((N:ℝ)/r) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
    have hS0 : 0 ≤ ∑ j, sphereGaussianDensityFactor8 r*(dm j)^2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (sphereGaussianDensityFactor8_pos hr0).le (sq_nonneg _)
    have h2 : (∑ j, c*(dm j)^2) ≤ Real.sqrt ((N:ℝ)/r)*(B*r) := by
      rw [hsum]
      calc ((N:ℝ)/r)^(1/4:ℝ)*∑ j, sphereGaussianDensityFactor8 r*(dm j)^2
          ≤ Real.sqrt ((N:ℝ)/r)*∑ j, sphereGaussianDensityFactor8 r*(dm j)^2 :=
            mul_le_mul_of_nonneg_right hq4 hS0
        _ ≤ Real.sqrt ((N:ℝ)/r)*(B*r) :=
            mul_le_mul_of_nonneg_left hsumS (Real.sqrt_nonneg _)
    have h3 : Real.sqrt ((N:ℝ)/r)*(B*r) ≤ η/4*N*(p+2) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
      have hsq : (Real.sqrt ((N:ℝ)/r)*(B*r))^2 = (N:ℝ)/r*(B^2*r^2) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring
      rw [hsq]
      have e1 : (N:ℝ)/r*(B^2*r^2) = B^2*r*N := by
        field_simp
      rw [e1, hrR]
      have e2 : (η/4*N*(p+2))^2 = (η*(p+2)/4)^2*N*N := by ring
      rw [e2]
      have := mul_le_mul_of_nonneg_right hrN hNR.le
      linarith
    rw [h1, div_le_iff₀ hp2]
    linarith
  -- add the missing points with weight √N
  set lam := Real.sqrt (N:ℝ) with hlamdef
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hNR
  obtain ⟨Y', hYE', hK⟩ := configuration_add_points_neg hr hr0 YM C hCm hdisj hunion hmass
    hc0.le hp hlam0 dm hdiam
  have hEM := energy4_sub_eq_normalized hM0 YM
  have hEN := energy4_sub_eq_normalized hN0 Y'
  obtain ⟨q, hqdef⟩ : ∃ q, q = ((M:ℝ)/N)*Real.sqrt ((M:ℝ)/N) := ⟨_, rfl⟩
  have hq' : 1-κ ≤ q := by rw [hκdef, hqdef, hRdef]; exact hq
  have hq0' : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef]
    have h1 : (M:ℝ)/N ≤ 1 := (div_le_one hNR).mpr hMN'
    have h2 : Real.sqrt ((M:ℝ)/N) ≤ 1 := Real.sqrt_le_one.mpr h1
    calc (M:ℝ)/N*Real.sqrt ((M:ℝ)/N) ≤ 1*1 :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hqM : (M:ℝ)*Real.sqrt M = q*((N:ℝ)*Real.sqrt N) := by
    rw [hqdef, Real.sqrt_div hMR.le]
    field_simp
  have hNsN : 0 < (N:ℝ)*Real.sqrt N := by positivity
  have hκq : 1-q ≤ κ := by linarith
  have hRκ : R*κ = η/4 := by rw [hκdef]; field_simp
  -- the cost of the added points
  have hcost : lam*Ω ≤ η/4*((N:ℝ)*Real.sqrt N) := by
    have := mul_le_mul_of_nonneg_left hΩ hlam0.le
    rw [hlamdef] at this ⊢
    nlinarith [Real.sqrt_nonneg (N:ℝ)]
  -- the energy of the enlarged configuration
  have hx : (predictedCoefficient+η/4)*q ≤ predictedCoefficient+η/4+η/4 := by
    have h1 : |predictedCoefficient+η/4| ≤ R := by
      have h2 : |predictedCoefficient+η/4| ≤ |predictedCoefficient|+|η/4| := abs_add_le _ _
      rw [abs_of_pos (by positivity : 0 < η/4)] at h2
      rw [hRdef]; linarith
    have hdev : |predictedCoefficient+η/4| * (1-q) ≤ η/4 := by
      calc |predictedCoefficient+η/4| * (1-q) ≤ R*κ :=
            mul_le_mul h1 hκq (by linarith) hR0.le
        _ = η/4 := hRκ
    have hneg : -((predictedCoefficient+η/4)*(1-q)) ≤ |predictedCoefficient+η/4| * (1-q) := by
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    have hsplit : (predictedCoefficient+η/4)*q =
        (predictedCoefficient+η/4)-(predictedCoefficient+η/4)*(1-q) := by ring
    linarith
  have henergy : normalizedEnergy Y' < predictedCoefficient+η := by
    have h1 : energy4 Y'-(7/16:ℝ)*(N:ℝ)^2 ≤
        (energy4 YM-(7/16:ℝ)*(M:ℝ)^2)+η/4*((N:ℝ)*Real.sqrt N) := by linarith
    rw [hEN, hEM, hqM] at h1
    have h2 : normalizedEnergy YM*(q*((N:ℝ)*Real.sqrt N)) ≤
        (predictedCoefficient+η/4)*(q*((N:ℝ)*Real.sqrt N)) :=
      mul_le_mul_of_nonneg_right hYE.le (by positivity)
    have h3 : normalizedEnergy Y'*((N:ℝ)*Real.sqrt N) ≤
        ((predictedCoefficient+η/4)*q+η/4)*((N:ℝ)*Real.sqrt N) := by
      calc normalizedEnergy Y'*((N:ℝ)*Real.sqrt N)
          ≤ normalizedEnergy YM*(q*((N:ℝ)*Real.sqrt N))+η/4*((N:ℝ)*Real.sqrt N) := h1
        _ ≤ (predictedCoefficient+η/4)*(q*((N:ℝ)*Real.sqrt N))+η/4*((N:ℝ)*Real.sqrt N) :=
            add_le_add h2 le_rfl
        _ = ((predictedCoefficient+η/4)*q+η/4)*((N:ℝ)*Real.sqrt N) := by ring
    have h4 := le_of_mul_le_mul_right h3 hNsN
    linarith
  refine ⟨Y', henergy, fun t ht ht2 => ?_⟩
  -- the deviation is at most η N^(3/2), so the deviation over √N is at most η N
  have hgap : ((energy4 YM-(7/16:ℝ)*(M:ℝ)^2)-(energy4 Y'-(7/16:ℝ)*(N:ℝ)^2))/lam ≤ η*N := by
    have hupM : energy4 YM-(7/16:ℝ)*(M:ℝ)^2 ≤ (predictedCoefficient+η/4)*q*((N:ℝ)*Real.sqrt N) := by
      rw [hEM, hqM, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hNsN.le
      exact mul_le_mul_of_nonneg_right hYE.le hq0'
    have hlowY : (predictedCoefficient-η/4)*((N:ℝ)*Real.sqrt N) ≤ energy4 Y'-(7/16:ℝ)*(N:ℝ)^2 := by
      rw [hEN]
      exact mul_le_mul_of_nonneg_right (hlowN Y') hNsN.le
    have hdiff : (predictedCoefficient+η/4)*q-(predictedCoefficient-η/4) ≤ η := by
      have h1 : |predictedCoefficient| * (1-q) ≤ η/4 := by
        calc |predictedCoefficient| * (1-q) ≤ R*κ := mul_le_mul hRabs hκq (by linarith) hR0.le
          _ = η/4 := hRκ
      have h4 : predictedCoefficient*(q-1) ≤ |predictedCoefficient| * (1-q) := by
        have h5 : predictedCoefficient*(q-1) = (-predictedCoefficient)*(1-q) := by ring
        rw [h5]
        exact mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
      have h6 : (predictedCoefficient+η/4)*q-(predictedCoefficient-η/4) =
          predictedCoefficient*(q-1)+η/4*q+η/4 := by ring
      have h7 : η/4*q ≤ η/4 := by
        have := mul_le_mul_of_nonneg_left hq1 (by positivity : (0:ℝ) ≤ η/4)
        linarith
      rw [h6]
      linarith
    rw [div_le_iff₀ hlam0]
    have hwN : η*N*lam = η*((N:ℝ)*Real.sqrt N) := by rw [hlamdef]; ring
    rw [hwN]
    have := mul_le_mul_of_nonneg_right hdiff hNsN.le
    have e1 : ((predictedCoefficient+η/4)*q-(predictedCoefficient-η/4))*((N:ℝ)*Real.sqrt N) =
        (predictedCoefficient+η/4)*q*((N:ℝ)*Real.sqrt N)-
          (predictedCoefficient-η/4)*((N:ℝ)*Real.sqrt N) := by ring
    linarith
  -- the kept points: rescale the density factor from c_M to c_N
  have hlt1 : l*t ≤ 1 := by nlinarith
  have hlt0 : 0 < l*t := mul_pos hl0 ht
  have hcl : c = l*sphereGaussianDensityFactor8 M := by rw [hcdef, hratioM]
  have hresc := negMacroBlock8_rescale hl0 (sphereGaussianDensityFactor8 M) p ht.le
    (fun i => YM i) univ (M:ℝ)
  rw [← hcl] at hresc
  have hcfgM := negMacroBlock8_config hM0 YM hp hlt0.le
  have hYM := hYmac (l*t) hlt0 hlt1
  have hlp : l^(-(p+1)) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hl1 (show -(p+1) ≤ 1 by linarith)
    rw [Real.rpow_one] at h
    linarith
  have hlp0 : 0 ≤ l^(-(p+1)) := Real.rpow_nonneg hl0.le _
  have hpow : (l*t)^(p+3) ≤ 2^(p+3)*t^(p+3) := by
    rw [← Real.mul_rpow (by norm_num) ht.le]
    exact Real.rpow_le_rpow hlt0.le (by nlinarith) hp3.le
  have hkept : kernelBlock8 (negMacroKernel8 c p t) (fun i => YM i) univ M ≤
      2*N*(2*C₁*(2^(p+3)*t^(p+3)/(p+3))+3*η) := by
    rw [hresc, hcfgM]
    have hin : ∫ α in Ioc 0 (l*t), α^p*(sphereGaussianCenteredScaled8 α YM+1) ≤
        2*C₁*(2^(p+3)*t^(p+3)/(p+3))+3*η := by
      refine hYM.trans ?_
      have : 2*C₁*((l*t)^(p+3)/(p+3)) ≤ 2*C₁*(2^(p+3)*t^(p+3)/(p+3)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hp3.le) (by positivity)
      linarith
    have hB0 : 0 ≤ 2*C₁*(2^(p+3)*t^(p+3)/(p+3))+3*η := by positivity
    have hint0 : 0 ≤ ∫ α in Ioc 0 (l*t), α^p*(sphereGaussianCenteredScaled8 α YM+1) := by
      have h := negMacroBlock8_cutoff_bounds (sphereGaussianDensityFactor8_pos hM0).le hp
        hlt0.le le_rfl (fun i => YM i) univ (M:ℝ) (by rw [Fintype.card_fin, probReal_univ, mul_one])
      rw [hcfgM] at h
      exact nonneg_of_mul_nonneg_right (by linarith [h.1]) hMR
    calc l^(-(p+1))*((M:ℝ)*∫ α in Ioc 0 (l*t), α^p*(sphereGaussianCenteredScaled8 α YM+1))
        ≤ 2*((M:ℝ)*(2*C₁*(2^(p+3)*t^(p+3)/(p+3))+3*η)) := by
          apply mul_le_mul hlp _ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left hin hMR.le
      _ ≤ 2*N*(2*C₁*(2^(p+3)*t^(p+3)/(p+3))+3*η) := by
          have := mul_le_mul_of_nonneg_right hMN' hB0
          linarith
  -- the whole configuration
  have hcfgN := negMacroBlock8_config hN0 Y' hp ht.le
  have hKt := hK t ht.le (by linarith)
  rw [hcfgN] at hKt
  have htot : (N:ℝ)*∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α Y'+1) ≤
      N*(8*2^(p+3)*C₁*(t^(p+3)/(p+3))+15*η) := by
    have hfin : (N:ℝ)*(8*2^(p+3)*C₁*(t^(p+3)/(p+3))+15*η) =
        2*(2*N*(2*C₁*(2^(p+3)*t^(p+3)/(p+3))+3*η))+2*(η/4*N+η*N)+N*(η/2) := by ring
    rw [hfin]
    have hηN : 0 ≤ (N:ℝ)*(η/2) := by positivity
    linarith
  exact le_of_mul_le_mul_left htot hNR


set_option maxHeartbeats 1000000 in
/-- Sharp `s = 4` configurations with a small macroscopic end for every large `N`. -/
theorem sphere8_neg_sharp_allN
    (hlow4 : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      predictedCoefficient-ε ≤ normalizedEnergy X)
    {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) {p : ℝ} (hp : -2 < p) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+η ∧
      ∀ t : ℝ, 0 < t → t ≤ 1/2 →
        ∫ α in Ioc 0 t, α^p*(sphereGaussianCenteredScaled8 α Y+1) ≤ C₂*(t^(p+3)/(p+3))+15*η := by
  obtain ⟨C₁, hC₁, hC⟩ := sphere8_neg_sharp_upper_subsequence hlow4 hB hstrat hp
  have hp2 : 0 < p+2 := by linarith
  refine ⟨8*2^(p+3)*C₁, by positivity, fun η hη hη1 => ?_⟩
  obtain ⟨d, hd, hev⟩ := hC (η/4) (by positivity) (by linarith)
  obtain ⟨N₀, hN₀⟩ := hlow4 (η/4) (by positivity)
  have hratio := rationalSizeFloor8_ratio_tendsto d hd
  have hq : Tendsto (fun N : ℕ => ((rationalSizeFloor8 d N:ℝ)/(N:ℝ))*
      Real.sqrt ((rationalSizeFloor8 d N:ℝ)/(N:ℝ))) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one, mul_one] using hratio.mul hratio.sqrt
  have hκ0 : 0 < η/(4*(|predictedCoefficient|+1)) := by positivity
  have hqev : ∀ᶠ N : ℕ in atTop, 1-η/(4*(|predictedCoefficient|+1)) ≤
      ((rationalSizeFloor8 d N:ℝ)/(N:ℝ))*Real.sqrt ((rationalSizeFloor8 d N:ℝ)/(N:ℝ)) :=
    hq.eventually (Ici_mem_nhds (by linarith))
  have hmev := (rationalSizeFloorIndex8_tendsto d hd).eventually hev
  have hMlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ rationalSizeFloor8 d N := by
    have h := (rationalSizeFloorIndex8_tendsto d hd).eventually (eventually_ge_atTop 1)
    filter_upwards [h] with N hN
    unfold rationalSizeFloor8
    have h1 : rationalSizeFloorIndex8 d N ≤ d*rationalSizeFloorIndex8 d N :=
      Nat.le_mul_of_pos_left _ hd
    have h2 : d*rationalSizeFloorIndex8 d N ≤ (d*rationalSizeFloorIndex8 d N)^8 :=
      Nat.le_self_pow (by norm_num) _
    omega
  have h16ev : ∀ᶠ N : ℕ in atTop, (1:ℝ)/16 ≤ (rationalSizeFloor8 d N:ℝ)/(N:ℝ) :=
    hratio.eventually (Ici_mem_nhds (by norm_num))
  set ε₀ := (η*(p+2)/4)^2/(B^2+1) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hfrev : ∀ᶠ N : ℕ in atTop, 1-ε₀ ≤ (rationalSizeFloor8 d N:ℝ)/(N:ℝ) :=
    hratio.eventually (Ici_mem_nhds (by linarith))
  filter_upwards [hqev, hmev, hMlarge, eventually_ge_atTop N₀, h16ev, hfrev,
    eventually_gt_atTop 0] with N hqN hmN hMbig hNN₀ h16 hfr hNpos
  obtain ⟨YM, hYE, hYmac⟩ := hmN
  have hMN : rationalSizeFloor8 d N ≤ N := rationalSizeFloor8_le d N hd
  have hM0 : 0 < rationalSizeFloor8 d N := hMbig
  have hYnorm : normalizedEnergy YM < predictedCoefficient+η/4 := by
    rw [normalizedEnergy_power_eight (d*rationalSizeFloorIndex8 d N) YM]
    exact hYE
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hl16 : (N:ℝ) ≤ 16*(rationalSizeFloor8 d N:ℝ) := by
    rw [le_div_iff₀ hNR] at h16
    linarith
  have hrN : B^2*((N:ℝ)-rationalSizeFloor8 d N) ≤ (η*(p+2)/4)^2*N := by
    rw [le_div_iff₀ hNR] at hfr
    have h1 : (N:ℝ)-rationalSizeFloor8 d N ≤ ε₀*N := by linarith
    have h2 : B^2*((N:ℝ)-rationalSizeFloor8 d N) ≤ B^2*(ε₀*N) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg B)
    have h3 : B^2*ε₀ ≤ (η*(p+2)/4)^2 := by
      rw [hε₀, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg B, sq_nonneg (η*(p+2)/4)]
    have h4 : B^2*(ε₀*N) ≤ (η*(p+2)/4)^2*N := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h3 hNR.le
    linarith
  exact neg_allN_step hp hC₁ hη hη1 hM0 hMN YM hYnorm
    (fun t ht ht1 => (hYmac t ht ht1).trans (by linarith)) (hN₀ N hNN₀) hqN hl16 hsphere hrN

/-- The sharp lower bound for every `-2 < s < 0` and every large `N`, under the CKMRV contract
and the stratification hypotheses. -/
theorem sphere8_riesz_neg_lower_allN (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      sphereRieszCoefficientNeg8 s-η ≤ normalizedEnergyNeg8 s Y := by
  have hp : -2 < s/2-1 := by linarith
  have hp3 : 0 < s/2-1+3 := by linarith
  obtain ⟨C₂, hC₂, hC⟩ := sphere8_neg_sharp_allN (sphere8_lower4_of_laplaceSineData D) hB hstrat
    hsphere hp
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+1/((j:ℝ)+1) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1/2 →
        ∫ α in Ioc 0 t, α^(s/2-1)*(sphereGaussianCenteredScaled8 α Y+1) ≤
          C₂*(t^(s/2-1+3)/(s/2-1+3))+15*(1/((j:ℝ)+1)) := by
    intro j
    apply hC _ (by positivity)
    rw [div_le_one (by positivity)]
    have := (Nat.cast_nonneg j : (0:ℝ) ≤ j)
    linarith
  obtain ⟨J, hJ, hev⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  have hstep : ∀ k : ℕ, ∃ Y : Configuration (k+N₁+1),
      normalizedEnergy Y < predictedCoefficient+1/((J (k+N₁+1):ℝ)+1) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1/2 →
        ∫ α in Ioc 0 t, α^(s/2-1)*(sphereGaussianCenteredScaled8 α Y+1) ≤
          C₂*(t^(s/2-1+3)/(s/2-1+3))+15*(1/((J (k+N₁+1):ℝ)+1)) :=
    fun k => hN₁ (k+N₁+1) (by omega)
  choose X hX using hstep
  have hNt : Tendsto (fun k : ℕ => k+N₁+1) atTop atTop :=
    tendsto_atTop_mono (fun k => (by omega : k ≤ k+N₁+1)) tendsto_id
  have hNpos : ∀ k, 0 < k+N₁+1 := fun k => by omega
  have hJt : Tendsto (fun k : ℕ => J (k+N₁+1)) atTop atTop := hJ.comp hNt
  have hinv : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1/((J (k+N₁+1):ℝ)+1) ≤ ε := fun ε hε =>
    hJt.eventually (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε))
  have hmain := sphere8_riesz_neg_lower_of_sharp_sequence D hs hs0 hNpos hNt X
    (fun ε hε => by
      filter_upwards [hinv ε hε] with k hk
      linarith [(hX k).1])
    (fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (show 0 < ε*(s/2-1+3)/(2*(C₂+1)) by positivity)
      refine ⟨n₀+1, ?_⟩
      filter_upwards [hinv (ε/30) (by positivity)] with k hk
      have hn1 : (1:ℝ) ≤ ((n₀+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n₀)
      set x : ℝ := 1/(((n₀+1:ℕ):ℝ)+1) with hx
      have hx0 : 0 < x := by positivity
      have hx2 : x ≤ 1/2 := by
        rw [hx]
        apply one_div_le_one_div_of_le (by norm_num)
        linarith
      have hxn : x ≤ 1/((n₀:ℝ)+1) := by
        rw [hx]
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
      have hb := (hX k).2 x hx0 hx2
      have hxq : x^(s/2-1+3) ≤ x := by
        have h := Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith)
          (show (1:ℝ) ≤ s/2-1+3 by linarith)
        rwa [Real.rpow_one] at h
      have hterm : C₂*(x^(s/2-1+3)/(s/2-1+3)) ≤ ε/2 := by
        have h1 : C₂*(x^(s/2-1+3)/(s/2-1+3)) ≤ C₂*(x/(s/2-1+3)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxq hp3.le) hC₂
        have h2 : x < ε*(s/2-1+3)/(2*(C₂+1)) := lt_of_le_of_lt hxn hn₀
        have h3 : C₂*(x/(s/2-1+3)) ≤ ε/2 := by
          rw [mul_div_assoc', div_le_iff₀ hp3]
          have h4 : x*(2*(C₂+1)) < ε*(s/2-1+3) := by
            rwa [lt_div_iff₀ (by positivity)] at h2
          nlinarith
        linarith
      have h15 : 15*(1/((J (k+N₁+1):ℝ)+1)) ≤ ε/2 := by linarith
      linarith)
  intro η hη
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hmain η hη)
  refine ⟨k₀+N₁+1, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, N = k+N₁+1 := ⟨N-N₁-1, by omega⟩
  exact ⟨X k, hk₀ k (by omega)⟩

/-- The sharp asymptotics for every `-2 < s < 0` in conjecture form (all configurations above,
some configuration below, every large `N`), under the CKMRV contract and the exact-mass
stratification hypotheses. -/
theorem sphere8_riesz_neg_sharp_asymptotic (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re+η) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpow s Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8)) := by
  refine ⟨sphere8_riesz_neg_upper_conjecture_form D hs hs0, fun η hη => ?_⟩
  obtain ⟨N₀, h⟩ := sphere8_riesz_neg_lower_allN D hB hstrat hsphere hs hs0 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyNeg8, sphereRieszConstNeg8_eq_pair_integral hs hs0,
    sphereRieszCoefficientNeg8_eq_epstein hs hs0] at hY

#print axioms neg_allN_step
#print axioms sphere8_neg_sharp_allN
#print axioms sphere8_riesz_neg_lower_allN
#print axioms sphere8_riesz_neg_sharp_asymptotic

end SphericalRiesz
