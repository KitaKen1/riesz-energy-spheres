import FCTargetDefinitions

open Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RieszSphereFC
/-- The inverse-fourth minimum on S⁸ has leading coefficient 7/16 and next coefficient −5√210/48. -/
theorem riesz_energy_four_sphere8 :
    Tendsto (fun N : ℕ =>
      (sInf (range fun X : Config 8 N =>
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))⁻¹^4)-
        7/16*(N:ℝ)^2)/((N:ℝ)*Real.sqrt N)) atTop (𝓝 (-5*Real.sqrt 210/48)) := by
  sorry

/-- For 0 < s < 2, the normalized minimum converges to A_2^(−s/2) Z_L(s). -/
theorem riesz_energy_sphere2 {s : ℝ} (hs : 0 < s) (hsd : s < 2) :
    Tendsto (normalizedMin 2 s) atTop
      (𝓝 ((area 2)^(-(s/2))*(hexZeta ((s/2:ℝ):ℂ)).re)) := by
  sorry

/-- For −2 < s < 0, use a supremum; the normalized maximum on S^2 has the same continued Epstein coefficient. -/
theorem riesz_energy_neg_sphere2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMax 2 s) atTop
      (𝓝 ((area 2)^(-(s/2))*(hexZeta ((s/2:ℝ):ℂ)).re)) := by
  sorry

/-- The logarithmic minimum on S^2, after subtracting W N² and adding (N/2) log N, has the displayed linear coefficient. -/
theorem log_energy_sphere2 :
    Tendsto (normalizedLogMin 2) atTop
      (𝓝 ((1/2)*(deriv hexZetaCont 0).re+(1/2)*Real.log (area 2))) := by
  sorry

/-- The optimal L² cap discrepancy on S^2, using dt on [−1,1] and uniform directions, scales as N^(−1/2−1/4). -/
theorem cap_discrepancy_sphere2 :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/4)*minimumCap 2 N)
      atTop (𝓝 (Real.sqrt ((1/4:ℝ)*(-((area 2)^((1:ℝ)/2)*
        (hexZeta ((-1/2:ℝ):ℂ)).re))))) := by
  sorry

/-- For 0 < s < 8, the normalized minimum converges to A_8^(−s/8) Z_L(s). The removable value s=2 is stated separately. -/
theorem riesz_energy_sphere8 {s : ℝ} (hs : 0 < s) (hsd : s < 8) (hs2 : s ≠ 2) :
    Tendsto (normalizedMin 8 s) atTop
      (𝓝 ((area 8)^(-(s/8))*(e8Zeta ((s/2:ℝ):ℂ)).re)) := by
  sorry

/-- For −2 < s < 0, use a supremum; the normalized maximum on S^8 has the same continued Epstein coefficient. -/
theorem riesz_energy_neg_sphere8 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMax 8 s) atTop
      (𝓝 ((area 8)^(-(s/8))*(e8Zeta ((s/2:ℝ):ℂ)).re)) := by
  sorry

/-- The logarithmic minimum on S^8, after subtracting W N² and adding (N/8) log N, has the displayed linear coefficient. -/
theorem log_energy_sphere8 :
    Tendsto (normalizedLogMin 8) atTop
      (𝓝 (-60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105)) := by
  sorry

/-- The optimal L² cap discrepancy on S^8, using dt on [−1,1] and uniform directions, scales as N^(−1/2−1/16). -/
theorem cap_discrepancy_sphere8 :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/16)*minimumCap 8 N)
      atTop (𝓝 (Real.sqrt ((35/256:ℝ)*(-((area 8)^((1:ℝ)/8)*
        (e8Zeta ((-1/2:ℝ):ℂ)).re))))) := by
  sorry

/-- For 0 < s < 24, the normalized minimum converges to A_24^(−s/24) Z_L(s). -/
theorem riesz_energy_sphere24 {s : ℝ} (hs : 0 < s) (hsd : s < 24) :
    Tendsto (normalizedMin 24 s) atTop
      (𝓝 ((area 24)^(-(s/24))*(leechZeta ((s/2:ℝ):ℂ)).re)) := by
  sorry

/-- For −2 < s < 0, use a supremum; the normalized maximum on S^24 has the same continued Epstein coefficient. -/
theorem riesz_energy_neg_sphere24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (normalizedMax 24 s) atTop
      (𝓝 ((area 24)^(-(s/24))*(leechZeta ((s/2:ℝ):ℂ)).re)) := by
  sorry

/-- The logarithmic minimum on S^24, after subtracting W N² and adding (N/24) log N, has the displayed linear coefficient. -/
theorem log_energy_sphere24 :
    Tendsto (normalizedLogMin 24) atTop
      (𝓝 ((1/2)*(deriv leechZetaCont 0).re+(1/24)*Real.log (area 24))) := by
  sorry

/-- The optimal L² cap discrepancy on S^24, using dt on [−1,1] and uniform directions, scales as N^(−1/2−1/48). -/
theorem cap_discrepancy_sphere24 :
    Tendsto (fun N : ℕ => (N:ℝ)^((1:ℝ)/2+1/48)*minimumCap 24 N)
      atTop (𝓝 (Real.sqrt ((676039/8388608:ℝ)*(-((area 24)^((1:ℝ)/24)*
        (leechZeta ((-1/2:ℝ):ℂ)).re))))) := by
  sorry

/-- The removable E8 value s=2 uses 120 ζ′(−2), multiplied by A_8^(−1/4). -/
theorem riesz_energy_two_sphere8 :
    Tendsto (normalizedMin 8 2) atTop
      (𝓝 ((area 8)^(-((2:ℝ)/8))*(120*(deriv riemannZeta (-2)).re))) := by
  sorry

end RieszSphereFC
