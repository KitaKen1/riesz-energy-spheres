import Riesz.NegAllN8
import Riesz.SphereCapDiscrepancySqrt8

/-! The sharp spherical cap `L²` discrepancy, two-sided (stage DISC).

By Stolarsky's invariance principle on `S⁸`, `N^(1+1/8) D_{L²}(X)² = (35/256)(N² W - Σ|x_i-x_j|)
/N^(7/8)` with `W = ∫∫|x-y|`, so the sharp lower bound for the `s = -1` energy along every large
`N` (some configuration, `sphere8_riesz_neg_sharp_asymptotic`) gives configurations with
`N^(1+1/8) D_{L²}² ≤ (35/256)(-A₈^(1/8) Re ζ_E8(-1)) + η`, the matching upper bound of the
one-sided bound already proved. Hence the optimal cap discrepancy satisfies
`N^(1/2+1/16) D_{L²} → c₈ = 0.25583853953856988…` (Bilyk–Brauchart's conjectured constant), under
the CKMRV contract and the exact-mass stratification hypotheses. -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SphericalRiesz
open Boundary

/-- Configurations with sharp cap discrepancy for every large `N`. -/
theorem sphere8_cap_discrepancy_upper_conjecture_form (D : E8LaplaceSineData8) {B : ℝ}
    (hB : 0 ≤ B) (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : Configuration N,
      (N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X ≤
        sphereAbsMoment8/2*(-((sphereArea8.real univ)^((1:ℝ)/8)*
          (e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re))+η := by
  intro η hη
  set m := sphereAbsMoment8 with hm
  have hm0 : 0 ≤ m := sphereAbsMoment8_nonneg
  have hη' : 0 < η/(m/2+1) := div_pos hη (by linarith)
  obtain ⟨N₀, h⟩ := (sphere8_riesz_neg_sharp_asymptotic D hB hstrat hsphere (s := -1)
    (by norm_num) (by norm_num)).2 (η/(m/2+1)) hη'
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hNpos : 0 < N := hN1
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨X, hX⟩ := h N hN0
  refine ⟨X, ?_⟩
  rw [energyRpow_neg_one_eq, pair_integral_rpow_neg_one] at hX
  set W := ∫ p : Sphere8 × Sphere8, dist p.1 p.2 ∂(sphereProbability8.prod sphereProbability8)
    with hW
  set S := ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j) with hS
  set c := (sphereArea8.real univ)^(-((-1:ℝ)/8))*
    (e8EpsteinCandidate (((-1:ℝ)/2:ℝ):ℂ)).re with hc
  have hc' : (sphereArea8.real univ)^((1:ℝ)/8)*(e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re = c := by
    rw [hc]
    norm_num
  rw [hc']
  have hp : (N:ℝ)^(1+(-1:ℝ)/8) = (N:ℝ)^((7:ℝ)/8) := by norm_num
  rw [hp] at hX
  have hP : 0 < (N:ℝ)^((7:ℝ)/8) := Real.rpow_pos_of_pos hNR _
  rw [capDiscrepancyL2Sq8_eq hNpos, capDiscrepancySq8_stolarsky X, ← hW, ← hm, ← hS]
  have hpow : (N:ℝ)^(1+(1:ℝ)/8)*((N:ℝ)^((7:ℝ)/8)) = (N:ℝ)^2 := by
    rw [← Real.rpow_add hNR]
    norm_num
  have hkey : (N:ℝ)^(1+(1:ℝ)/8)*(m/2*((N:ℝ)^2*W-S)/(N:ℝ)^2) =
      m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8) := by
    rw [← hpow]
    field_simp
  rw [hkey]
  have hb : c-η/(m/2+1) ≤ (S-W*(N:ℝ)^2)/(N:ℝ)^((7:ℝ)/8) := hX
  have hb2 : ((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8) ≤ -c+η/(m/2+1) := by
    have : ((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8) = -((S-W*(N:ℝ)^2)/(N:ℝ)^((7:ℝ)/8)) := by
      rw [← neg_div]; congr 1; ring
    rw [this]; linarith
  have hb3 := mul_le_mul_of_nonneg_left hb2 (by linarith : 0 ≤ m/2)
  have hfrac : m/2*(η/(m/2+1)) ≤ η := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have he : m/2*(((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8)) = m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8) := by
    ring
  rw [← he]
  nlinarith

/-- `N^(1/2+1/16) D_{L²}(X) ≤ c₈ + η` for some configuration, for every large `N`. -/
theorem sphere8_cap_discrepancy_sqrt_upper (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : Configuration N,
      (N:ℝ)^((1:ℝ)/2+1/16)*Real.sqrt (capDiscrepancyL2Sq8 X) ≤ sphereCapDiscrepancyConst8+η := by
  intro η hη
  set K := (35/256:ℝ)*(-((sphereArea8.real univ)^((1:ℝ)/8)*
    (e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re)) with hK
  obtain ⟨N₀, h⟩ := sphere8_cap_discrepancy_upper_conjecture_form D hB hstrat hsphere (η^2)
    (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨X, hX⟩ := h N hN
  rw [sphereStolarskyConst8_eq, ← hK] at hX
  refine ⟨X, ?_⟩
  have hD0 := capDiscrepancyL2Sq8_nonneg X
  have hNR : (0:ℝ) ≤ N := Nat.cast_nonneg N
  set P := (N:ℝ)^((1:ℝ)/2+1/16) with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNR _
  have hPsq : P^2 = (N:ℝ)^(1+(1:ℝ)/8) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hNR]
    norm_num
  have hrhs : P*Real.sqrt (capDiscrepancyL2Sq8 X) =
      Real.sqrt ((N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X) := by
    rw [← hPsq, Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP0]
  rw [hrhs]
  unfold sphereCapDiscrepancyConst8
  rw [← hK]
  have hmono : Real.sqrt ((N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X) ≤ Real.sqrt (K+η^2) :=
    Real.sqrt_le_sqrt hX
  have hsplit : Real.sqrt (K+η^2) ≤ Real.sqrt K+η := by
    rw [Real.sqrt_le_left]
    · rcases le_or_gt 0 K with hK0 | hK0
      · have h2 := Real.sq_sqrt hK0
        have h1 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
        nlinarith
      · rw [Real.sqrt_eq_zero_of_nonpos hK0.le]
        nlinarith
    · positivity
  linarith

/-- The optimal spherical cap `L²` discrepancy on `S⁸` is asymptotic to `c₈ N^(-1/2-1/16)`
(two-sided), under the CKMRV contract and the exact-mass stratification hypotheses. -/
theorem sphere8_cap_discrepancy_sharp (D : E8LaplaceSineData8) {B : ℝ} (hB : 0 ≤ B)
    (hstrat : ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B)
    (hsphere : SphereStratifiable8 B) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ X : Configuration N, sphereCapDiscrepancyConst8-η ≤
        (N:ℝ)^((1:ℝ)/2+1/16)*Real.sqrt (capDiscrepancyL2Sq8 X)) ∧
      ∃ X : Configuration N,
        (N:ℝ)^((1:ℝ)/2+1/16)*Real.sqrt (capDiscrepancyL2Sq8 X) ≤ sphereCapDiscrepancyConst8+η := by
  intro η hη
  obtain ⟨N₁, h1⟩ := sphere8_cap_discrepancy_sqrt_lower D η hη
  obtain ⟨N₂, h2⟩ := sphere8_cap_discrepancy_sqrt_upper D hB hstrat hsphere η hη
  exact ⟨max N₁ N₂, fun N hN => ⟨h1 N (le_of_max_le_left hN), h2 N (le_of_max_le_right hN)⟩⟩

#print axioms sphere8_cap_discrepancy_upper_conjecture_form
#print axioms sphere8_cap_discrepancy_sqrt_upper
#print axioms sphere8_cap_discrepancy_sharp

end SphericalRiesz
