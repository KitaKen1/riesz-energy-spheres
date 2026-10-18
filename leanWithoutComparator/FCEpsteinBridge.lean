import FCDefinitions
import FCEpsteinIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set MeasureTheory
namespace RieszSphereFC

/-- The FC theta integral is the regular Mellin continuation with the distance exponent. -/
theorem epstein_eq_weakFEPair (d : ℕ) (θ : ℝ → ℝ) (P : WeakFEPair ℂ)
    (hk : P.k = (d : ℝ) / 2) (hfg : P.f = P.g) (hε : P.ε = 1)
    (hf₀ : P.f₀ = 1) (hg₀ : P.g₀ = 1)
    (hθ : ∀ t : ℝ, 1 < t → (θ t : ℂ) = P.f t) (s : ℂ) :
    epstein d θ s = (Real.pi : ℂ) ^ (s / 2) *
      (P.Λ₀ (s / 2) * (Complex.Gamma (s / 2))⁻¹ -
        (Complex.Gamma (s / 2 + 1))⁻¹ -
        ((d : ℂ) / 2 - s / 2)⁻¹ * (Complex.Gamma (s / 2))⁻¹) := by
  have hkC : (P.k : ℂ) = (d : ℂ) / 2 := by
    rw [hk]
    push_cast
    rfl
  have hJ : P.Λ₀ (s / 2) = ∫ t in Ioi (1 : ℝ), ((θ t - 1 : ℝ) : ℂ) *
      ((t : ℂ) ^ (s / 2 - 1) + (t : ℂ) ^ ((d : ℂ) / 2 - s / 2 - 1)) := by
    rw [weakFEPair_lambdaZero_integral P hfg hε hf₀ hg₀, hkC]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Complex.ofReal_sub, Complex.ofReal_one, hθ t ht]
  dsimp only [epstein]
  rw [← hJ]
  ring

end RieszSphereFC
