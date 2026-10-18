import Riesz.SphereMain24
import Riesz.SphereOptimalProfile24

/-! The limits of the actual extremal values on `S²⁴` without hypotheses (stage G24).

Generated with `Riesz/SphereMain24.lean`: each statement is the corresponding statement of
`Riesz/SphereOptimalProfile24.lean` with the hypothesis removed, proved by one application of
`sphere24_gaussian_sharp_profile_lower`. -/

-- from Riesz/OptimalSphereEnergy.lean
section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz


theorem sphere24_minimum_riesz_tendsto_unconditional
    
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    Tendsto (normalizedMinimumRieszEnergyD 24 s) atTop
      (𝓝 (((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re))  :=
  sphere24_minimum_riesz_tendsto_of_profile sphere24_gaussian_sharp_profile_lower hs hs24

theorem sphere24_maximum_riesz_tendsto_unconditional
    
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMaximumRieszEnergyD 24 s) atTop
      (𝓝 (((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re))  :=
  sphere24_maximum_riesz_tendsto_of_profile sphere24_gaussian_sharp_profile_lower hs hs0

theorem sphere24_minimum_log_tendsto_unconditional :
    Tendsto (normalizedMinimumLogEnergyD 24) atTop
      (𝓝 ((1/2)*(deriv leechEpsteinZetaCont 0).re+
        (1/24)*Real.log ((sphereAreaD 24).real univ)))  :=
  sphere24_minimum_log_tendsto_of_profile sphere24_gaussian_sharp_profile_lower

theorem sphere24_minimum_cap_discrepancy_tendsto_unconditional :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/48)*minimumCapDiscrepancy24 N)
      atTop (𝓝 sphereCapDiscrepancyConst24)  :=
  sphere24_minimum_cap_discrepancy_tendsto_of_profile sphere24_gaussian_sharp_profile_lower

end SphericalRiesz
end
end
