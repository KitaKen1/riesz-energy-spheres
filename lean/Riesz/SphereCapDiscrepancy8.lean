import Riesz.SphereStolarsky8

/-! The sharp spherical cap `L²` discrepancy lower bound on S⁸ (stage DISC, one-sided).

`D_{L²}(X)² = ∫∫ (#(X ∩ C(z,t))/N - σ(C(z,t)))² dσ(z) dt` (centre by the actual sphere
probability, threshold `t ∈ [-1,1]` by Lebesgue measure). By Stolarsky's principle
`N² D_{L²}(X)² = (m/2) (N² ∫∫|x-y| - Σ_{i,j} |x_i-x_j|)`, and the universal sharp bound for the
sum of distances (`s = -1`) gives, under the CKMRV contract, for every `η > 0` and all large `N`,
`N^(1+1/8) D_{L²}(X)² ≥ (m/2) (-A₈^(1/8) Re ζ_E8(-1)) - η` for every configuration, with
`ζ_E8(-1) = 2^(1/2) 240 ζ(-1/2) ζ(-7/2)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace SphericalRiesz

/-- The normalized squared spherical cap `L²` discrepancy. -/
def capDiscrepancyL2Sq8 {N : ℕ} (X : Configuration N) : ℝ :=
  ∫ q, ((∑ i : Fin N, capInd8 q.1 q.2 (X i))/(N:ℝ) -
    ∫ y, capInd8 q.1 q.2 y ∂sphereProbability8)^2 ∂capMeasure8

theorem capDiscrepancyL2Sq8_eq {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    capDiscrepancyL2Sq8 X = capDiscrepancySq8 X/(N:ℝ)^2 := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold capDiscrepancyL2Sq8 capDiscrepancySq8
  rw [← integral_div]
  congr 1
  funext q
  unfold capDiscrepancyFn8
  field_simp

theorem sphereAbsMoment8_nonneg : 0 ≤ sphereAbsMoment8 :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem energyRpow_neg_one_eq {N : ℕ} (X : Configuration N) :
    energyRpow (-1) X = ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j) := by
  rw [energyRpow_eq_full_neg (by norm_num) X]
  simp only [neg_neg, Real.rpow_one]

theorem pair_integral_rpow_neg_one :
    (∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-(-1:ℝ))
        ∂(sphereProbability8.prod sphereProbability8)) =
      ∫ p : Sphere8 × Sphere8, dist p.1 p.2 ∂(sphereProbability8.prod sphereProbability8) := by
  simp only [neg_neg, Real.rpow_one]

/-- Sharp one-sided cap discrepancy bound in conjecture form, under the CKMRV contract. -/
theorem sphere8_cap_discrepancy_lower_conjecture_form (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      sphereAbsMoment8/2*(-((sphereArea8.real univ)^((1:ℝ)/8)*
          (e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re))-η ≤
        (N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X := by
  intro η hη
  set m := sphereAbsMoment8 with hm
  have hm0 : 0 ≤ m := sphereAbsMoment8_nonneg
  have hη' : 0 < η/(m/2+1) := div_pos hη (by linarith)
  obtain ⟨N₀, h⟩ := sphere8_riesz_neg_upper_conjecture_form D (s := -1) (by norm_num)
    (by norm_num) (η/(m/2+1)) hη'
  refine ⟨max N₀ 1, fun N hN X => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hNpos : 0 < N := hN1
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hX := h N hN0 X
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
  -- Stolarsky
  rw [capDiscrepancyL2Sq8_eq hNpos, capDiscrepancySq8_stolarsky X, ← hW, ← hm, ← hS]
  have hpow : (N:ℝ)^(1+(1:ℝ)/8)*((N:ℝ)^((7:ℝ)/8)) = (N:ℝ)^2 := by
    rw [← Real.rpow_add hNR]
    norm_num
  have hkey : (N:ℝ)^(1+(1:ℝ)/8)*(m/2*((N:ℝ)^2*W-S)/(N:ℝ)^2) =
      m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8) := by
    rw [← hpow]
    field_simp
  rw [hkey]
  have hb : (S-W*(N:ℝ)^2)/(N:ℝ)^((7:ℝ)/8) ≤ c+η/(m/2+1) := hX
  have hb2 : -(c+η/(m/2+1)) ≤ ((N:ℝ)^2*W-S)/(N:ℝ)^((7:ℝ)/8) := by
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

#print axioms capDiscrepancyL2Sq8_eq
#print axioms sphereAbsMoment8_nonneg
#print axioms energyRpow_neg_one_eq
#print axioms pair_integral_rpow_neg_one
#print axioms sphere8_cap_discrepancy_lower_conjecture_form

end SphericalRiesz
