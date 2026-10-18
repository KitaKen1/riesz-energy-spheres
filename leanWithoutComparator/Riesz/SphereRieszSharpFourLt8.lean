import Riesz.SphereRieszUpperFourLtAllN8
import Riesz.SphereRieszConstPair8

/-! Two-sided sharp second-order asymptotics for `4 < s < 8` in conjecture form.

Under the CKMRV Laplace–sine contract, for every `4 < s < 8`, with `I_s` the actual uniform double
integral of `|x-y|^(-s)` on `S⁸` and `C_s = A₈^(-s/8)·Re(2^(-s/2)·240·ζ(s/2)ζ(s/2-3))`:
every configuration satisfies `(E_s - I_s N²)/N^(1+s/8) ≥ C_s - η` for large `N`, and for every
large `N` some configuration satisfies `(E_s - I_s N²)/N^(1+s/8) ≤ C_s + η`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz

theorem sphere8_riesz_upper_four_lt_conjecture_form (D : E8LaplaceSineData8) {s : ℝ}
    (hs4 : 4 < s) (hs8 : s < 8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyRpow s Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re+η := by
  have hs : 0 < s := by linarith
  have hs2 : s ≠ 2 := by intro h; linarith
  intro η hη
  obtain ⟨N₀, h⟩ := sphere8_riesz_upper_four_lt D hs4 hs8 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyRpow, sphereRieszConst8_eq_pair_integral hs hs8,
    sphereRieszCoefficient8_eq_epstein hs hs8 hs2] at hY

/-- Two-sided sharp asymptotics for `4 < s < 8` in conjecture form, under the CKMRV contract. -/
theorem sphere8_riesz_sharp_asymptotic_four_lt (D : E8LaplaceSineData8) {s : ℝ}
    (hs4 : 4 < s) (hs8 : s < 8) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyRpow s Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re+η) :=
  ⟨sphere8_riesz_sharp_lower_conjecture_form D (by linarith) hs8 (by intro h; linarith),
    sphere8_riesz_upper_four_lt_conjecture_form D hs4 hs8⟩

end SphericalRiesz
