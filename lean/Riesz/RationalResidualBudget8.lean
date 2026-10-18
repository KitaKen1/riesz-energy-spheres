import Riesz.RationalCubeFamily8

/-! Match the leftover integer index budget to the probability of the actual
sphere complement. This is mass accounting; iid selection of residual physical
points and energy control remain separate. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

theorem rationalCubeFamily8_residual_mass {K : ℕ}
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v : Fin K → Fin 8 → ℝ)
    (p q : ℕ) (ℓ : ℝ)
    (hc : ∀ i, IsCompact (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)))
    (hμ : sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) =
      (K : ℝ)*((p : ℝ)/q)^8) :
    sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))ᶜ =
      1-(K : ℝ)*((p : ℝ)/q)^8 := by
  have hmeas := MeasurableSet.iUnion (fun i => (hc i).isClosed.measurableSet)
  rw [measureReal_compl hmeas,probReal_univ,hμ]

theorem rationalCubeFamily8_residual_count_match {K : ℕ}
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v : Fin K → Fin 8 → ℝ)
    (p q m : ℕ) (hq : 0 < q) (hm : 0 < m) (hbudget : K*p^8 < q^8) (ℓ b : ℝ)
    (hc : ∀ i, IsCompact (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)))
    (hμ : sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) =
      (K : ℝ)*((p : ℝ)/q)^8)
    (hl : 1-b < sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)))
    (hu : sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) < 1) :
    ((((q^8-K*p^8)*m^8 : ℕ) : ℝ)/(((q*m)^8 : ℕ) : ℝ)) =
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))ᶜ ∧
    0 < sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))ᶜ ∧
    sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))ᶜ < b := by
  have hr := rationalCubeFamily8_residual_mass g v p q ℓ hc hμ
  refine ⟨(rationalCubeNodeBudget8_residual_ratio K p q m hq hm hbudget.le).trans hr.symm,?_,?_⟩
  · rw [hr]
    linarith
  · rw [hr]
    linarith

end SphericalRiesz
