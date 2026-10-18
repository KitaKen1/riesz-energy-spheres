import E8Leech.ConditionalCrystallization

/-!
# From a quadratic slack certificate to the analytic transfer input

The stationary LP inequality and the actual auxiliary function remain explicit
proof obligations. Once supplied, a constant lower bound away from the first
lattice distance and a quadratic lower bound near it suffice. The known cutoff
`t = δ^(1/3)` then gives the exact cost ratio, without ENNReal subtraction.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

/-- Additive stationary LP gap. Constructing it for CKMRV slack is a deep input. -/
structure StationarySlackGapInput {d : ℕ} (Λ : Set (Ambient d)) (s : ℝ)
    (V : Ambient d → Ambient d → ℝ≥0∞) : Prop where
  gap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
    IsStationary μ → HasIntensity μ 1 →
    latticeRieszEnergy Λ s + (∫⁻ z, orderedWindowEnergy V z (unitWindow d) ∂μ) ≤
      rieszEnergy s μ

/-- Cancel the finite lattice baseline rather than subtracting infinite energies. -/
theorem expected_slack_le_of_excess {d : ℕ} {Λ : Set (Ambient d)} {s : ℝ}
    {V : Ambient d → Ambient d → ℝ≥0∞}
    (hgap : StationarySlackGapInput Λ s V)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) {δ : ℝ}
    (hexcess : HasRieszExcessAtMost s μ (latticeRieszEnergy Λ s) (ENNReal.ofReal δ)) :
    (∫⁻ z, orderedWindowEnergy V z (unitWindow d) ∂μ) ≤ ENNReal.ofReal δ := by
  exact ENNReal.le_of_add_le_add_left hexcess.1
    ((hgap.gap μ inferInstance hμ hρ).trans hexcess.2)

/-- The known cubic cutoff converts quadratic close-pair cost into linear loss. -/
theorem quadratic_slack_cost_ratio {k t δ : ℝ} (hk : 0 < k) (ht : 0 < t)
    (hcube : t ^ 3 = δ) :
    ENNReal.ofReal δ / ENNReal.ofReal (k * t ^ 2) = ENNReal.ofReal (k⁻¹ * t) := by
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hk (pow_pos ht 2)), ← hcube]
  congr 1
  field_simp [ne_of_gt hk, ne_of_gt ht]

/-- A uniform quadratic lower bound supplies the entire analytic cost interface. -/
theorem analyticUnitCostInput_of_quadratic_slack {d : ℕ}
    (Λ : Set (Ambient d)) (s r k : ℝ) (hk : 0 < k)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hgap : StationarySlackGapInput Λ s V)
    (hlower : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ∀ x y, x ≠ y → dist x y < r * (1 - t) → ENNReal.ofReal (k * t ^ 2) ≤ V x y) :
    AnalyticUnitCostInput Λ s r k⁻¹ (1 / 8) := by
  constructor
  intro μ hprob hμ hρ δ hδ hsmall hexcess
  let _ := hprob
  let t := δ ^ (1 / 3 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hδ _
  have hhalf : t ≤ 1 / 2 := one_third_cutoff_le_half hδ.le hsmall.le
  have hkt : 0 < k * t ^ 2 := mul_pos hk (pow_pos ht 2)
  refine ⟨ENNReal.ofReal (k * t ^ 2), ENNReal.ofReal δ, V,
    ENNReal.ofReal_ne_zero_iff.mpr hkt, ENNReal.ofReal_ne_top, ?_, hlower t ht hhalf, ?_⟩
  · exact (quadratic_slack_cost_ratio hk ht (one_third_cutoff_cube hδ.le)).le
  · exact expected_slack_le_of_excess hgap μ hμ hρ hexcess

/-- The coefficient used by the two-zone certificate. -/
def quadraticSlackCoefficient (r a b : ℝ) : ℝ := min (4 * a) (b * r ^ 2)

theorem quadraticSlackCoefficient_pos {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    0 < quadraticSlackCoefficient r a b := by
  exact lt_min (by positivity) (by positivity)

/-- Away from the first lattice distance a constant bound suffices; near it,
only the quadratic remainder is needed. No differentiability is assumed here. -/
theorem two_zone_quadratic_lower {r a b t u v : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hhalf : t ≤ 1 / 2)
    (_hu : 0 < u) (hclose : u < r * (1 - t))
    (hfar : u ≤ r / 2 → a ≤ v)
    (hnear : r / 2 ≤ u → u < r → b * (r - u) ^ 2 ≤ v) :
    quadraticSlackCoefficient r a b * t ^ 2 ≤ v := by
  by_cases hzone : u ≤ r / 2
  · have hs : t ^ 2 ≤ 1 / 4 := by nlinarith
    calc
      quadraticSlackCoefficient r a b * t ^ 2 ≤ (4 * a) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg t)
      _ ≤ a := by nlinarith [mul_le_mul_of_nonneg_left hs ha.le]
      _ ≤ v := hfar hzone
  · have hur : u < r := by nlinarith [mul_pos hr ht]
    have hgap : r * t ≤ r - u := by nlinarith
    have hrt : 0 ≤ r * t := (mul_pos hr ht).le
    have hsq : (r * t) ^ 2 ≤ (r - u) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hgap) (add_nonneg (by linarith : 0 ≤ r - u) hrt)]
    calc
      quadraticSlackCoefficient r a b * t ^ 2 ≤ (b * r ^ 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
      _ = b * (r * t) ^ 2 := by ring
      _ ≤ b * (r - u) ^ 2 := mul_le_mul_of_nonneg_left hsq hb.le
      _ ≤ v := hnear (not_le.mp hzone).le hur

/-- Nonnegative radial slack, keeping diagonal exclusion in orderedWindowEnergy. -/
def radialSlackPotential {d : ℕ} (φ : ℝ → ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (φ (dist x y))

theorem measurable_radialSlackPotential {d : ℕ} {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (Function.uncurry (radialSlackPotential (d := d) φ)) := by
  exact (hφ.comp (measurable_fst.dist measurable_snd)).ennreal_ofReal

theorem measurable_radialSlackEnergy {d : ℕ} {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (fun z => orderedWindowEnergy (radialSlackPotential φ) z (unitWindow d)) := by
  exact measurable_orderedWindowEnergy (measurable_radialSlackPotential hφ) (measurable_unitWindow d)

/-- Remaining analytic obligations for one actual radial slack. These fields
are hypotheses to prove, not existence assertions or imported axioms. -/
structure TwoZoneSlackCertificate {d : ℕ} (Λ : Set (Ambient d))
    (s r a b : ℝ) (φ : ℝ → ℝ) : Prop where
  measurable : Measurable φ
  gap : StationarySlackGapInput Λ s (radialSlackPotential φ)
  far : ∀ u : ℝ, 0 < u → u ≤ r / 2 → a ≤ φ u
  near : ∀ u : ℝ, r / 2 ≤ u → u < r → b * (r - u) ^ 2 ≤ φ u

theorem radial_slack_close_pair_bound {d : ℕ} {Λ : Set (Ambient d)} {s r a b : ℝ}
    {φ : ℝ → ℝ} (hcert : TwoZoneSlackCertificate Λ s r a b φ)
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    {t : ℝ} (ht : 0 < t) (hhalf : t ≤ 1 / 2)
    (x y : Ambient d) (hne : x ≠ y) (hclose : dist x y < r * (1 - t)) :
    ENNReal.ofReal (quadraticSlackCoefficient r a b * t ^ 2) ≤ radialSlackPotential φ x y := by
  apply ENNReal.ofReal_le_ofReal
  exact two_zone_quadratic_lower hr ha hb ht hhalf (dist_pos.mpr hne) hclose
    (hcert.far (dist x y) (dist_pos.mpr hne)) (hcert.near (dist x y))

theorem analyticUnitCostInput_of_two_zone_slack {d : ℕ}
    {Λ : Set (Ambient d)} {s r a b : ℝ} {φ : ℝ → ℝ}
    (hcert : TwoZoneSlackCertificate Λ s r a b φ)
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    AnalyticUnitCostInput Λ s r (quadraticSlackCoefficient r a b)⁻¹ (1 / 8) := by
  apply analyticUnitCostInput_of_quadratic_slack Λ s r _
    (quadraticSlackCoefficient_pos hr ha hb) (radialSlackPotential φ) hcert.gap
  intro t ht hhalf x y hne hclose
  exact radial_slack_close_pair_bound hcert hr ha hb ht hhalf x y hne hclose

/-- The exact original-law target now needs just the two-zone analytic
certificate plus the previously isolated packing / jointly measurable BRR input. -/
theorem stationaryCrystallizationFor_of_two_zone_slack {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r E B c η₀ : ℝ) (hr : 0 < r) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : PeriodicStabilityInput Λ r E B c η₀)
    (hanalytic : ∀ s : ℝ, (d : ℝ) < s → ∃ a b : ℝ, ∃ φ : ℝ → ℝ,
      0 < a ∧ 0 < b ∧ TwoZoneSlackCertificate Λ s r a b φ) :
    StationaryCrystallizationFor Λ := by
  apply stationaryCrystallizationFor_of_inputs Λ hΛ r E B c η₀ hr hE hB hc hη₀ hperiodic
  intro s hs
  obtain ⟨a, b, φ, ha, hb, hcert⟩ := hanalytic s hs
  exact ⟨(quadraticSlackCoefficient r a b)⁻¹, 1 / 8,
    (inv_pos.mpr (quadraticSlackCoefficient_pos hr ha hb)).le, by norm_num,
    analyticUnitCostInput_of_two_zone_slack hcert hr ha hb⟩

end E8Leech
