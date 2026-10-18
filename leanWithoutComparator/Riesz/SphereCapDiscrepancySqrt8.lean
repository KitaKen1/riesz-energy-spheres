import Riesz.SphereAbsMoment8

/-! The cap discrepancy bound in the Bilyk–Brauchart form (stage DISC).

`D_{L²}(X) ≥ (c₈ - η) N^(-1/2-1/16)` for all large `N` and every configuration, with
`c₈ = √((35/256)(-A₈^(1/8) Re ζ_E8(-1)))`, the conjectured optimal constant of Bilyk–Brauchart
(`= 0.25583853953856988…`), under the CKMRV Laplace–sine contract. Square root of the explicit
squared bound. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The sharp cap discrepancy constant `c₈ = √((35/256)(-A₈^(1/8) Re ζ_E8(-1)))`. -/
def sphereCapDiscrepancyConst8 : ℝ :=
  Real.sqrt ((35/256:ℝ)*(-((sphereArea8.real univ)^((1:ℝ)/8)*
    (e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re)))

theorem capDiscrepancyL2Sq8_nonneg {N : ℕ} (X : Configuration N) : 0 ≤ capDiscrepancyL2Sq8 X :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- `N^(1/2+1/16) D_{L²}(X) ≥ c₈ - η` for all large `N` and every configuration. -/
theorem sphere8_cap_discrepancy_sqrt_lower (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      sphereCapDiscrepancyConst8-η ≤
        (N:ℝ)^((1:ℝ)/2+1/16)*Real.sqrt (capDiscrepancyL2Sq8 X) := by
  intro η hη
  set K := (35/256:ℝ)*(-((sphereArea8.real univ)^((1:ℝ)/8)*
    (e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re)) with hK
  obtain ⟨N₀, h⟩ := sphere8_cap_discrepancy_lower_explicit D (η^2) (by positivity)
  refine ⟨N₀, fun N hN X => ?_⟩
  have hX := h N hN X
  rw [← hK] at hX
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
  by_cases hsmall : Real.sqrt K ≤ η
  · have := Real.sqrt_nonneg ((N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X)
    linarith
  · replace hsmall : η < Real.sqrt K := lt_of_not_ge hsmall
    have hK0 : 0 ≤ K := by
      by_contra hneg
      have hneg' : K < 0 := lt_of_not_ge hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg'.le] at hsmall
      linarith
    have hη2 : η^2 ≤ K := by
      have h1 : η^2 ≤ (Real.sqrt K)^2 := pow_le_pow_left₀ hη.le hsmall.le 2
      rwa [Real.sq_sqrt hK0] at h1
    have hmono : Real.sqrt (K-η^2) ≤ Real.sqrt ((N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X) :=
      Real.sqrt_le_sqrt hX
    have hsplit : Real.sqrt K ≤ Real.sqrt (K-η^2)+η := by
      rw [Real.sqrt_le_left]
      · have h1 : 0 ≤ Real.sqrt (K-η^2) := Real.sqrt_nonneg _
        have h2 := Real.sq_sqrt (by linarith : 0 ≤ K-η^2)
        nlinarith
      · positivity
    linarith

#print axioms capDiscrepancyL2Sq8_nonneg
#print axioms sphere8_cap_discrepancy_sqrt_lower

end SphericalRiesz
