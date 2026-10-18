import Riesz.EqualAreaMovingRescaling8

/-! A finite maximum of the actual derivative bounds supplies a single
C7 constant. This needs no explicit expansion of seventh derivatives. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem equalAreaMovingNormalizedE8Chart_high_derivatives_through (n : ℕ) :
    ∃ C ≥ 0, ∀ k : ℕ, 2 ≤ k → k ≤ n → ∀ v : Fin 8 → ℝ,
      ∀ ε : ℝ, 0 < ε → ‖v‖+ε*equalAreaScaleRadius ≤ 1/8 →
      ∀ x : Fin 8 → ℝ, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedE8Chart v ε) x‖ ≤ C*ε^(k-1) := by
  induction n with
  | zero => exact ⟨0,le_rfl,by intro k hk hkn; omega⟩
  | succ n ih =>
    obtain ⟨C,hC,hb⟩ := ih
    by_cases hn : 2 ≤ n+1
    · obtain ⟨D,hD,hd⟩ := equalAreaMovingNormalizedE8Chart_high_derivatives (n+1) hn
      refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
      intro k hk hkn v ε hε hs x hx
      by_cases h : k ≤ n
      · exact (hb k hk h v ε hε hs x hx).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · have he : k = n+1 := by omega
        subst k
        exact (hd v ε hε hs x hx).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · exact ⟨0,le_rfl,by intro k hk hkn; omega⟩

theorem equalAreaMovingNormalizedE8Chart_C7_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ x : Fin 8 → ℝ, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (equalAreaMovingNormalizedE8Chart v ε) x-equalAreaFlatDerivative8‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ 7 →
        ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedE8Chart v ε) x‖ ≤ η := by
  obtain ⟨C,hC,hb⟩ := equalAreaMovingNormalizedE8Chart_high_derivatives_through 7
  obtain ⟨r,hr,hr1,hfirst⟩ := equalAreaMovingNormalizedE8Chart_first_uniform η hη
  let ρ : ℝ := min r (η/(C+1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ r := min_le_left _ _
  refine ⟨ρ,hρ,hρr.trans hr1,?_⟩
  intro v hv ε hε hs x hx
  refine ⟨hfirst v (hv.trans hρr) ε hε (hs.trans hρr) x hx,?_⟩
  intro k hk hk7
  have hs1 : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8 := by linarith
  have heρ : ε ≤ ρ := by
    have hrad : 1 ≤ equalAreaScaleRadius := by unfold equalAreaScaleRadius; linarith [norm_nonneg e8Map]
    nlinarith
  have he1 : ε ≤ 1 := by linarith
  have hpow : ε^(k-1) ≤ ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one hε.le he1 (show 1 ≤ k-1 by omega)
  calc
    _ ≤ C*ε^(k-1) := hb k hk hk7 v ε hε hs1 x hx
    _ ≤ C*ε := mul_le_mul_of_nonneg_left hpow hC
    _ ≤ C*ρ := mul_le_mul_of_nonneg_left heρ hC
    _ ≤ C*(η/(C+1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    _ ≤ η := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
      nlinarith

end SphericalRiesz
