import Riesz.ResidualFirstMoment

/-! Joint first-moment selection for two neutralized residual functionals.

The neutralized residual energy is linear in the kernel and in the linear term, so the existing
sequential selection applied to `k₁ + w·k₂` gives residual points with
`NE(k₁, L₁) + w·NE(k₂, L₂) ≤ 0`.  For a nonnegative kernel the neutralized energy is bounded below
by its background terms, and the pair sum plus the linear sum is bounded above by the neutralized
energy plus the same terms; these turn the joint inequality into two separate bounds. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SphericalRiesz
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

theorem residualRowPotential_add_smul (k₁ k₂ : E → E → ℝ) (w : ℝ) (x : E)
    (h₁ : Integrable (k₁ x) μ) (h₂ : Integrable (k₂ x) μ) :
    residualRowPotential μ (fun x y => k₁ x y+w*k₂ x y) x =
      residualRowPotential μ k₁ x+w*residualRowPotential μ k₂ x := by
  unfold residualRowPotential
  rw [integral_add h₁ (h₂.const_mul w), integral_const_mul]

theorem residualRowPotential_add_smul_integrable (k₁ k₂ : E → E → ℝ) (w : ℝ)
    (hk₁ : ∀ x, Integrable (k₁ x) μ) (hk₂ : ∀ x, Integrable (k₂ x) μ)
    (hV₁ : Integrable (residualRowPotential μ k₁) μ)
    (hV₂ : Integrable (residualRowPotential μ k₂) μ) :
    Integrable (residualRowPotential μ (fun x y => k₁ x y+w*k₂ x y)) μ := by
  have he : residualRowPotential μ (fun x y => k₁ x y+w*k₂ x y) =
      fun x => residualRowPotential μ k₁ x+w*residualRowPotential μ k₂ x := by
    funext x
    exact residualRowPotential_add_smul k₁ k₂ w x (hk₁ x) (hk₂ x)
  rw [he]
  exact hV₁.add (hV₂.const_mul w)

theorem residualBackground_add_smul (k₁ k₂ : E → E → ℝ) (w : ℝ)
    (hk₁ : ∀ x, Integrable (k₁ x) μ) (hk₂ : ∀ x, Integrable (k₂ x) μ)
    (hV₁ : Integrable (residualRowPotential μ k₁) μ)
    (hV₂ : Integrable (residualRowPotential μ k₂) μ) :
    residualBackground μ (fun x y => k₁ x y+w*k₂ x y) =
      residualBackground μ k₁+w*residualBackground μ k₂ := by
  unfold residualBackground
  have he : residualRowPotential μ (fun x y => k₁ x y+w*k₂ x y) =
      fun x => residualRowPotential μ k₁ x+w*residualRowPotential μ k₂ x := by
    funext x
    exact residualRowPotential_add_smul k₁ k₂ w x (hk₁ x) (hk₂ x)
  rw [he, integral_add hV₁ (hV₂.const_mul w), integral_const_mul]

theorem residualNeutralizedEnergy_add_smul (k₁ k₂ : E → E → ℝ) (L₁ L₂ : E → ℝ) (w : ℝ)
    (hk₁ : ∀ x, Integrable (k₁ x) μ) (hk₂ : ∀ x, Integrable (k₂ x) μ)
    (hV₁ : Integrable (residualRowPotential μ k₁) μ)
    (hV₂ : Integrable (residualRowPotential μ k₂) μ)
    (hL₁ : Integrable L₁ μ) (hL₂ : Integrable L₂ μ) {n : ℕ} (X : Fin n → E) :
    residualNeutralizedEnergy μ (fun x y => k₁ x y+w*k₂ x y) (fun x => L₁ x+w*L₂ x) X =
      residualNeutralizedEnergy μ k₁ L₁ X+w*residualNeutralizedEnergy μ k₂ L₂ X := by
  unfold residualNeutralizedEnergy residualPairEnergy
  rw [residualBackground_add_smul k₁ k₂ w hk₁ hk₂ hV₁ hV₂,
    integral_add hL₁ (hL₂.const_mul w), integral_const_mul]
  simp_rw [residualRowPotential_add_smul k₁ k₂ w _ (hk₁ _) (hk₂ _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Joint sequential first moment: one choice of residual points controls both functionals. -/
theorem exists_residualNeutralizedEnergy_joint [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (k₁ k₂ : E → E → ℝ) (L₁ L₂ : E → ℝ) {w : ℝ} (hw : 0 ≤ w)
    (hs₁ : ∀ x y, k₁ x y = k₁ y x) (hs₂ : ∀ x y, k₂ x y = k₂ y x)
    (h0₁ : ∀ x, k₁ x x = 0) (h0₂ : ∀ x, k₂ x x = 0)
    (hpos₁ : ∀ x y, 0 ≤ k₁ x y) (hpos₂ : ∀ x y, 0 ≤ k₂ x y)
    (hk₁ : ∀ x, Integrable (k₁ x) μ) (hk₂ : ∀ x, Integrable (k₂ x) μ)
    (hV₁ : Integrable (residualRowPotential μ k₁) μ)
    (hV₂ : Integrable (residualRowPotential μ k₂) μ)
    (hL₁ : Integrable L₁ μ) (hL₂ : Integrable L₂ μ)
    (B : Set E) (hB : μ B = 0) (r : ℕ) :
    ∃ X : Fin r → E, Function.Injective X ∧ (∀ i, X i ∉ B) ∧
      residualNeutralizedEnergy μ k₁ L₁ X+w*residualNeutralizedEnergy μ k₂ L₂ X ≤ 0 := by
  obtain ⟨X, hX, hXB, _, hzero⟩ := exists_residualNeutralizedEnergy_nonpos
    (μ := μ) (fun x y => k₁ x y+w*k₂ x y) (fun x => L₁ x+w*L₂ x)
    (fun x y => by rw [hs₁ x y, hs₂ x y])
    (fun x => by rw [h0₁ x, h0₂ x, mul_zero, add_zero])
    (fun x y => add_nonneg (hpos₁ x y) (mul_nonneg hw (hpos₂ x y)))
    (fun x => (hk₁ x).add ((hk₂ x).const_mul w))
    (residualRowPotential_add_smul_integrable k₁ k₂ w hk₁ hk₂ hV₁ hV₂)
    (hL₁.add (hL₂.const_mul w)) B hB r
  refine ⟨X, hX, hXB, ?_⟩
  rw [← residualNeutralizedEnergy_add_smul k₁ k₂ L₁ L₂ w hk₁ hk₂ hV₁ hV₂ hL₁ hL₂]
  exact hzero

theorem residualRowPotential_nonneg (k : E → E → ℝ) (hpos : ∀ x y, 0 ≤ k x y) (x : E) :
    0 ≤ residualRowPotential μ k x :=
  integral_nonneg fun y => hpos x y

theorem residualBackground_nonneg (k : E → E → ℝ) (hpos : ∀ x y, 0 ≤ k x y) :
    0 ≤ residualBackground μ k :=
  integral_nonneg fun x => residualRowPotential_nonneg k hpos x

/-- Lower bound of the neutralized energy of a nonnegative kernel by its background terms. -/
theorem residualNeutralizedEnergy_ge_of_nonneg (k : E → E → ℝ) (L : E → ℝ)
    (hpos : ∀ x y, 0 ≤ k x y) (hL : ∀ x, 0 ≤ L x) {R I : ℝ}
    (hR : ∀ x, residualRowPotential μ k x ≤ R) (hI : ∫ x, L x ∂μ ≤ I)
    {n : ℕ} (X : Fin n → E) :
    -(2*(n:ℝ)^2*R+(n:ℝ)*I) ≤ residualNeutralizedEnergy μ k L X := by
  have hp : 0 ≤ residualPairEnergy k X :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hpos _ _
  have hb : 0 ≤ residualBackground μ k := residualBackground_nonneg k hpos
  have hs : 0 ≤ ∑ i, L (X i) := Finset.sum_nonneg fun i _ => hL _
  have hrow : ∑ i, residualRowPotential μ k (X i) ≤ (n:ℝ)*R := by
    calc ∑ i, residualRowPotential μ k (X i) ≤ ∑ _i : Fin n, R :=
          Finset.sum_le_sum fun i _ => hR _
      _ = (n:ℝ)*R := by simp
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  unfold residualNeutralizedEnergy
  nlinarith [mul_le_mul_of_nonneg_left hrow (by positivity : (0:ℝ) ≤ 2*(n:ℝ)),
    mul_le_mul_of_nonneg_left hI hn, mul_nonneg (sq_nonneg (n:ℝ)) hb]

/-- The pair sum plus the linear sum, bounded by the neutralized energy plus background terms. -/
theorem residualPair_add_linear_le (k : E → E → ℝ) (L : E → ℝ)
    (hpos : ∀ x y, 0 ≤ k x y) {R I : ℝ}
    (hR : ∀ x, residualRowPotential μ k x ≤ R) (hI : ∫ x, L x ∂μ ≤ I)
    {n : ℕ} (X : Fin n → E) :
    residualPairEnergy k X+∑ i, L (X i) ≤
      residualNeutralizedEnergy μ k L X+(2*(n:ℝ)^2*R+(n:ℝ)*I) := by
  have hb : 0 ≤ residualBackground μ k := residualBackground_nonneg k hpos
  have hrow : ∑ i, residualRowPotential μ k (X i) ≤ (n:ℝ)*R := by
    calc ∑ i, residualRowPotential μ k (X i) ≤ ∑ _i : Fin n, R :=
          Finset.sum_le_sum fun i _ => hR _
      _ = (n:ℝ)*R := by simp
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  unfold residualNeutralizedEnergy
  nlinarith [mul_le_mul_of_nonneg_left hrow (by positivity : (0:ℝ) ≤ 2*(n:ℝ)),
    mul_le_mul_of_nonneg_left hI hn, mul_nonneg (sq_nonneg (n:ℝ)) hb]

end SphericalRiesz
