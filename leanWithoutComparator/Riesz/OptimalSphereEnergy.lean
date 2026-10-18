import Riesz.OptimalValues
import Riesz.HexConstruction2
import Riesz.HexNegSharp2
import Riesz.HexLogConstruction2
import Riesz.SphereCapDiscrepancy2
import Riesz.ResidualStratification8
import Riesz.SphereRieszUpperLtFour8
import Riesz.LeechSharpUpper24
import Riesz.LeechNegSharp24
import Riesz.SphereLogUpper24
import Riesz.SphereCapDiscrepancy24

/-! Optimal physical energies on S², S⁸ and S²⁴.

The extrema are real infima/suprema over injective configurations, before normalization.
Every limit ranges over all integer sizes. S² is unconditional; the E8 and Leech inputs
remain explicit in dimensions 8 and 24. No existence of an exact optimizer is assumed. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

def minimumRieszEnergyD (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  sInf (range (fun X : ConfigurationD d N => energyRpowD s X))

def maximumRieszEnergyD (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  sSup (range (fun X : ConfigurationD d N => energyRpowD s X))

def minimumLogEnergyD (d N : ℕ) : ℝ :=
  sInf (range (fun X : ConfigurationD d N => energyLogD X))

def continuousRieszEnergyD (d : ℕ) (s : ℝ) : ℝ :=
  ∫ p : SphereD d × SphereD d, (dist p.1 p.2)^(-s)
    ∂((sphereProbabilityD d).prod (sphereProbabilityD d))

def continuousLogEnergyD (d : ℕ) : ℝ :=
  ∫ p : SphereD d × SphereD d, -Real.log (dist p.1 p.2)
    ∂((sphereProbabilityD d).prod (sphereProbabilityD d))

def normalizedMinimumRieszEnergyD (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  (minimumRieszEnergyD d s N-continuousRieszEnergyD d s*(N:ℝ)^2)/(N:ℝ)^(1+s/d)

def normalizedMaximumRieszEnergyD (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  (maximumRieszEnergyD d s N-continuousRieszEnergyD d s*(N:ℝ)^2)/(N:ℝ)^(1+s/d)

def normalizedMinimumLogEnergyD (d N : ℕ) : ℝ :=
  (minimumLogEnergyD d N-continuousLogEnergyD d*(N:ℝ)^2+
    (N:ℝ)/d*Real.log N)/(N:ℝ)

def minimumCapDiscrepancy2 (N : ℕ) : ℝ :=
  sInf (range (fun X : ConfigurationD 2 N => Real.sqrt (capDiscrepancyL2Sq2 X)))

def minimumCapDiscrepancy8 (N : ℕ) : ℝ :=
  sInf (range (fun X : ConfigurationD 8 N => Real.sqrt (capDiscrepancyL2Sq8 X)))

def minimumCapDiscrepancy24 (N : ℕ) : ℝ :=
  sInf (range (fun X : ConfigurationD 24 N => Real.sqrt (capDiscrepancyL2Sq24 X)))

theorem minimum_riesz_tendsto_of_sharp_bounds {d : ℕ} {s c : ℝ}
    (h : (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ X : ConfigurationD d N,
      c-ε ≤ (energyRpowD s X-continuousRieszEnergyD d s*(N:ℝ)^2)/(N:ℝ)^(1+s/d)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ X : ConfigurationD d N,
      (energyRpowD s X-continuousRieszEnergyD d s*(N:ℝ)^2)/(N:ℝ)^(1+s/d) ≤ c+ε)) :
    Tendsto (normalizedMinimumRieszEnergyD d s) atTop (𝓝 c) :=
  tendsto_normalized_csInf_of_eventual_bounds
    (fun N (X : ConfigurationD d N) => energyRpowD s X)
    (fun N => (N:ℝ)^(1+s/d)) (fun N => continuousRieszEnergyD d s*(N:ℝ)^2)
    (eventually_natCast_rpow_pos _) h.1 h.2

theorem maximum_riesz_tendsto_of_sharp_bounds {d : ℕ} {s c : ℝ}
    (h : (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ X : ConfigurationD d N,
      (energyRpowD s X-continuousRieszEnergyD d s*(N:ℝ)^2)/(N:ℝ)^(1+s/d) ≤ c+ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ X : ConfigurationD d N,
      c-ε ≤ (energyRpowD s X-continuousRieszEnergyD d s*(N:ℝ)^2)/(N:ℝ)^(1+s/d))) :
    Tendsto (normalizedMaximumRieszEnergyD d s) atTop (𝓝 c) :=
  tendsto_normalized_csSup_of_eventual_bounds
    (fun N (X : ConfigurationD d N) => energyRpowD s X)
    (fun N => (N:ℝ)^(1+s/d)) (fun N => continuousRieszEnergyD d s*(N:ℝ)^2)
    (eventually_natCast_rpow_pos _) h.1 h.2

theorem minimum_log_tendsto_of_sharp_bounds {d : ℕ} {c : ℝ}
    (h : (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ X : ConfigurationD d N,
      c-ε ≤ (energyLogD X-continuousLogEnergyD d*(N:ℝ)^2+
        (N:ℝ)/d*Real.log N)/(N:ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ X : ConfigurationD d N,
      (energyLogD X-continuousLogEnergyD d*(N:ℝ)^2+
        (N:ℝ)/d*Real.log N)/(N:ℝ) ≤ c+ε)) :
    Tendsto (normalizedMinimumLogEnergyD d) atTop (𝓝 c) := by
  have heq (N : ℕ) (X : ConfigurationD d N) :
      (energyLogD X-(continuousLogEnergyD d*(N:ℝ)^2-(N:ℝ)/d*Real.log N))/(N:ℝ) =
      (energyLogD X-continuousLogEnergyD d*(N:ℝ)^2+(N:ℝ)/d*Real.log N)/(N:ℝ) := by ring
  have ht := tendsto_normalized_csInf_of_eventual_bounds
    (fun N (X : ConfigurationD d N) => energyLogD X) (fun N => (N:ℝ))
    (fun N => continuousLogEnergyD d*(N:ℝ)^2-(N:ℝ)/d*Real.log N)
    (by simpa only [Real.rpow_one] using eventually_natCast_rpow_pos 1)
    (by simpa only [heq] using h.1) (by simpa only [heq] using h.2)
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  dsimp [normalizedMinimumLogEnergyD, minimumLogEnergyD]
  ring

theorem sphere2_minimum_riesz_tendsto {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    Tendsto (normalizedMinimumRieszEnergyD 2 s) atTop
      (𝓝 ((4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re)) :=
  minimum_riesz_tendsto_of_sharp_bounds (sphere2_riesz_sharp_asymptotic_explicit hs hs2)

theorem sphere2_maximum_riesz_tendsto {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMaximumRieszEnergyD 2 s) atTop
      (𝓝 ((4*Real.pi)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re)) :=
  maximum_riesz_tendsto_of_sharp_bounds (sphere2_riesz_neg_sharp_asymptotic_explicit hs hs0)

theorem sphere2_minimum_log_tendsto :
    Tendsto (normalizedMinimumLogEnergyD 2) atTop
      (𝓝 ((1/2)*(deriv hexEpsteinZetaCont 0).re+(1/2)*Real.log (4*Real.pi))) := by
  apply minimum_log_tendsto_of_sharp_bounds
  simpa only [sphereArea2_univ_real, continuousLogEnergyD, Nat.cast_ofNat] using
    sphere2_log_sharp_asymptotic_unconditional

theorem sphere2_minimum_cap_discrepancy_tendsto :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/4)*minimumCapDiscrepancy2 N)
      atTop (𝓝 sphereCapDiscrepancyConst2) :=
  tendsto_scaled_csInf_of_twoSidedTarget
    (fun N (X : ConfigurationD 2 N) => Real.sqrt (capDiscrepancyL2Sq2 X)) _ _
    sphere2_cap_discrepancy_sharp_unconditional

theorem sphere8_minimum_riesz_tendsto (D : E8LaplaceSineData8) {s : ℝ}
    (hs : 0 < s) (hs8 : s < 8) :
    Tendsto (normalizedMinimumRieszEnergyD 8 s) atTop (𝓝 (sphereRieszCoefficient8 s)) :=
  minimum_riesz_tendsto_of_sharp_bounds (sphere8_riesz_sharp_asymptotic_all D hs hs8)

theorem sphere8_minimum_riesz_tendsto_epstein (D : E8LaplaceSineData8) {s : ℝ}
    (hs : 0 < s) (hs8 : s < 8) (hs2 : s ≠ 2) :
    Tendsto (normalizedMinimumRieszEnergyD 8 s) atTop
      (𝓝 ((sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re)) :=
  minimum_riesz_tendsto_of_sharp_bounds (sphere8_riesz_sharp_asymptotic D hs hs8 hs2)

theorem sphere8_minimum_riesz_two_tendsto (D : E8LaplaceSineData8) :
    Tendsto (normalizedMinimumRieszEnergyD 8 2) atTop
      (𝓝 ((sphereArea8.real univ)^(-((2:ℝ)/8))*(120*(deriv riemannZeta (-2)).re))) :=
  minimum_riesz_tendsto_of_sharp_bounds (sphere8_riesz_sharp_asymptotic_two D)

theorem sphere8_maximum_riesz_tendsto (D : E8LaplaceSineData8) {s : ℝ}
    (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMaximumRieszEnergyD 8 s) atTop
      (𝓝 ((sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re)) :=
  maximum_riesz_tendsto_of_sharp_bounds (sphere8_riesz_neg_sharp D hs hs0)

theorem sphere8_minimum_log_tendsto (D : E8LaplaceSineData8) :
    Tendsto (normalizedMinimumLogEnergyD 8) atTop
      (𝓝 (-60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105)) :=
  minimum_log_tendsto_of_sharp_bounds (sphere8_log_sharp D)

theorem sphere8_minimum_cap_discrepancy_tendsto (D : E8LaplaceSineData8) :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/16)*minimumCapDiscrepancy8 N)
      atTop (𝓝 sphereCapDiscrepancyConst8) :=
  tendsto_scaled_csInf_of_twoSidedTarget
    (fun N (X : ConfigurationD 8 N) => Real.sqrt (capDiscrepancyL2Sq8 X)) _ _
    (sphere8_cap_discrepancy_sharp_ckmrv D)

theorem sphere24_minimum_riesz_tendsto
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    Tendsto (normalizedMinimumRieszEnergyD 24 s) atTop
      (𝓝 (((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re)) :=
  minimum_riesz_tendsto_of_sharp_bounds (sphere24_riesz_sharp_asymptotic_epstein hG24 hs hs24)

theorem sphere24_maximum_riesz_tendsto
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMaximumRieszEnergyD 24 s) atTop
      (𝓝 (((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re)) :=
  maximum_riesz_tendsto_of_sharp_bounds (sphere24_riesz_neg_sharp_asymptotic hG24 hs hs0)

theorem sphere24_minimum_log_tendsto
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    Tendsto (normalizedMinimumLogEnergyD 24) atTop
      (𝓝 ((1/2)*(deriv leechEpsteinZetaCont 0).re+
        (1/24)*Real.log ((sphereAreaD 24).real univ))) :=
  minimum_log_tendsto_of_sharp_bounds (sphere24_log_sharp_asymptotic hG24)

theorem sphere24_minimum_cap_discrepancy_tendsto
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/48)*minimumCapDiscrepancy24 N)
      atTop (𝓝 sphereCapDiscrepancyConst24) :=
  tendsto_scaled_csInf_of_twoSidedTarget
    (fun N (X : ConfigurationD 24 N) => Real.sqrt (capDiscrepancyL2Sq24 X)) _ _
    (sphere24_cap_discrepancy_sharp hG24)

end SphericalRiesz
