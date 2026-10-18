import Riesz.SphereProfileFinal24
import Riesz.OptimalSphereEnergy

/-! The limits of the actual extremal values on `S²⁴` from the sharp lower Gaussian profile alone.

Generated (with `Riesz/SphereProfileFinal24.lean`): the theorems of `Riesz/OptimalSphereEnergy.lean`
about `S²⁴` with the all-scale contact certificates as hypothesis, restated with the profile as
hypothesis; same proof text.  Kept apart because `Riesz.OptimalSphereEnergy` also covers `S²`
and `S⁸`, so that the main results of dimension 24 do not depend on those chains. -/

-- from Riesz/OptimalSphereEnergy.lean
section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

theorem sphere24_minimum_riesz_tendsto_of_profile
    (hG24p : SphereGaussianSharpProfileLower24)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    Tendsto (normalizedMinimumRieszEnergyD 24 s) atTop
      (𝓝 (((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re)) :=
  minimum_riesz_tendsto_of_sharp_bounds (sphere24_riesz_sharp_asymptotic_epstein_of_profile hG24p hs hs24)

theorem sphere24_maximum_riesz_tendsto_of_profile
    (hG24p : SphereGaussianSharpProfileLower24)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMaximumRieszEnergyD 24 s) atTop
      (𝓝 (((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re)) :=
  maximum_riesz_tendsto_of_sharp_bounds (sphere24_riesz_neg_sharp_asymptotic_of_profile hG24p hs hs0)

theorem sphere24_minimum_log_tendsto_of_profile
    (hG24p : SphereGaussianSharpProfileLower24) :
    Tendsto (normalizedMinimumLogEnergyD 24) atTop
      (𝓝 ((1/2)*(deriv leechEpsteinZetaCont 0).re+
        (1/24)*Real.log ((sphereAreaD 24).real univ))) :=
  minimum_log_tendsto_of_sharp_bounds (sphere24_log_sharp_asymptotic_of_profile hG24p)

theorem sphere24_minimum_cap_discrepancy_tendsto_of_profile
    (hG24p : SphereGaussianSharpProfileLower24) :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/48)*minimumCapDiscrepancy24 N)
      atTop (𝓝 sphereCapDiscrepancyConst24) :=
  tendsto_scaled_csInf_of_twoSidedTarget
    (fun N (X : ConfigurationD 24 N) => Real.sqrt (capDiscrepancyL2Sq24 X)) _ _
    (sphere24_cap_discrepancy_sharp_of_profile hG24p)

end SphericalRiesz
end
end
