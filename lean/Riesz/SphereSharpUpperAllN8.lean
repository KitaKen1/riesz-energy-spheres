import Riesz.SphereSharpUpperSubsequence8
import Riesz.SphereEnergySubconfiguration4
import Riesz.RationalSizeCeiling8

/-! The actual sharp upper bound for every sufficiently large integer N.
Nonnegative pair energy permits a squared-density extraction bound; its
constant background cancels exactly and its normalized factor tends to one. -/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace SphericalRiesz

theorem sphere8_inverse_fourth_sharp_upper_allN (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∃ Y : Configuration N,
      normalizedEnergy Y < predictedCoefficient+η := by
  obtain ⟨d, hd, hsub⟩ := sphere8_inverse_fourth_sharp_normalized_upper_subsequence
    (η/2) (by positivity)
  have hpoints := (rationalSizeIndex8_tendsto d hd).eventually hsub
  have hfactor : Tendsto (fun N : ℕ =>
      Real.sqrt ((N:ℝ)/(rationalSizeCeiling8 d N:ℝ))*(predictedCoefficient+η/2))
      atTop (𝓝 (predictedCoefficient+η/2)) := by
    simpa only [one_mul] using (rationalSizeCeiling8_sqrt_ratio_tendsto d hd).mul_const
      (predictedCoefficient+η/2)
  filter_upwards [hpoints, hfactor.eventually_lt_const (by linarith :
    predictedCoefficient+η/2 < predictedCoefficient+η), eventually_ge_atTop (2:ℕ)]
    with N hX hfactor hN
  obtain ⟨X, hX⟩ := hX
  change Configuration (rationalSizeCeiling8 d N) at X
  obtain ⟨e, he⟩ := normalizedEnergy_exists_subconfiguration N (rationalSizeCeiling8 d N)
    hN (rationalSizeCeiling8_ge d N hd) X
  refine ⟨e.trans X, ?_⟩
  exact (he.trans (mul_le_mul_of_nonneg_left hX.le (Real.sqrt_nonneg _))).trans_lt hfactor

theorem sphere8_inverse_fourth_sharp_upper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      normalizedEnergy Y ≤ predictedCoefficient+η := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (sphere8_inverse_fourth_sharp_upper_allN η hη)
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN
  obtain ⟨Y, hY⟩ := hN₀ N ((le_max_right _ _).trans hN)
  exact ⟨Y, hY.le⟩

theorem normalizedEnergy_bddBelow (N : ℕ) :
    BddBelow (Set.range (fun X : Configuration N => normalizedEnergy X)) := by
  refine ⟨(-(7/16:ℝ)*(N:ℝ)^2)/((N:ℝ)*Real.sqrt (N:ℝ)), ?_⟩
  rintro _ ⟨X, rfl⟩
  unfold normalizedEnergy
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [energy4_nonneg X]

theorem sphere8_inverse_fourth_infimum_upper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      sInf (Set.range (fun X : Configuration N => normalizedEnergy X)) ≤
        predictedCoefficient+η := by
  obtain ⟨N₀, hN₀, h⟩ := sphere8_inverse_fourth_sharp_upper η hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  obtain ⟨Y, hY⟩ := h N hN
  exact (csInf_le (normalizedEnergy_bddBelow N) (Set.mem_range_self Y)).trans hY

theorem S8s4Target_of_sharp_lower
    (hl : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, predictedCoefficient-η ≤ normalizedEnergy X) : S8s4Target := by
  intro η hη
  obtain ⟨L, hL⟩ := hl η hη
  obtain ⟨U, hU, hu⟩ := sphere8_inverse_fourth_sharp_upper η hη
  refine ⟨max L U, hU.trans (le_max_right _ _), ?_⟩
  intro N hN
  exact ⟨hL N ((le_max_left _ _).trans hN), hu N ((le_max_right _ _).trans hN)⟩

end SphericalRiesz
