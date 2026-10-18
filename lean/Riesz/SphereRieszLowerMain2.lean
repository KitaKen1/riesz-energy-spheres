import Riesz.HexGaussianBridge2
import Riesz.SphereRieszLower2

/-! The universal lower bound for the Riesz energy on S², without hypotheses (stage S2).

The Gaussian certificates of the triangular lattice exist at every scale
(`hexGaussianContact_all`, the OpenAI theorem in the form of this project), so the lower half of
the S² chain loses its hypothesis: for `0 < s < 2`, every `η > 0` and every large `N`, every
configuration of `N` points on the unit sphere S² satisfies

`(E_s - I_s N²)/N^(1+s/2) ≥ (4π)^(-s/2) Re ζ_Λ(s) - η`,

where `E_s` is the ordered off-diagonal sum of `|x_i - x_j|^(-s)`, `I_s` the double integral of
`|x - y|^(-s)` over the uniform measure, and `ζ_Λ` the continued Epstein zeta function of the
triangular lattice of covolume one (in the variable `u = s/2`).  The matching upper bound (the
construction of configurations) is not in this module. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

/-- The sharp lower Gaussian profile of S²: no hypothesis. -/
theorem sphere2_gaussian_sharp_profile_lower : SphereGaussianSharpProfileLower2 :=
  sphereGaussianSharpProfileLower2_of_contact hexGaussianContact_all

/-- Universal lower bound for the normalized Riesz energy on S², `0 < s < 2`: no hypothesis. -/
theorem sphere2_riesz_sharp_lower {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      sphereRieszCoefficient2 s-η ≤ normalizedEnergyRpow2 s X :=
  sphere2_riesz_sharp_lower_of_contact hexGaussianContact_all hs hs2

/-- Universal lower bound on S² in the form of the conjecture, with the actual double integral
and the Epstein coefficient of the triangular lattice: no hypothesis. -/
theorem sphere2_riesz_sharp_lower_unconditional {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) :=
  sphere2_riesz_sharp_lower_epstein hexGaussianContact_all hs hs2

/-- The same bound with the area `4π` of S² written out. -/
theorem sphere2_riesz_sharp_lower_explicit {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) := by
  have h := sphere2_riesz_sharp_lower_unconditional hs hs2
  rw [sphereArea2_univ_real] at h
  exact h

end SphericalRiesz
