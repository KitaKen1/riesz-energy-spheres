import E8Leech.PeriodizationTransfer
import E8Leech.ProbabilityBounds
import E8Leech.ScaleRestoration
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Expected density deficit and the original-law probability budget

Periodic packing optimality is an explicit input `D ≤ 1`. With that input,
the truncated nonnegative deficit has mean `1 - E[D]`. Bernoulli's inequality
supplies the finite guard loss; Markov and a measurable BRR good event then
feed the transfer theorem. No periodic optimality or BRR theorem is postulated
as an axiom or proved here.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

def expandedGuardDeficit {d : ℕ} (c : Configuration (Ambient d))
    (L r t : ℝ) (ht : t < 1) : ℝ≥0∞ :=
  1 - guardDensity (expandAfterDeletion c r t ht) L r

theorem measurable_expandedGuardDeficit {d : ℕ}
    (L r t : ℝ) (ht : t < 1) :
    Measurable (fun c : Configuration (Ambient d) => expandedGuardDeficit c L r t ht) :=
  measurable_const.sub ((measurable_guardDensity L r).comp
    (measurable_expandAfterDeletion r t ht))

/-- This identity uses the deep packing upper bound as a hypothesis. Without that
bound, `E[(1-D)₊] = 1-E[D]` would in general be false. -/
theorem expected_expandedGuardDeficit_eq {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (L r t : ℝ) (ht : t < 1)
    (hpacking : ∀ c : Configuration (Ambient d), guardDensity (expandAfterDeletion c r t ht) L r ≤ 1) :
    (∫⁻ c, expandedGuardDeficit c L r t ht ∂μ) =
      1 - (∫⁻ c, guardDensity (expandAfterDeletion c r t ht) L r ∂μ) := by
  have hm : Measurable (fun c : Configuration (Ambient d) =>
      guardDensity (expandAfterDeletion c r t ht) L r) :=
    (measurable_guardDensity L r).comp (measurable_expandAfterDeletion r t ht)
  have hf : (∫⁻ c, guardDensity (expandAfterDeletion c r t ht) L r ∂μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hpacking
      _ = 1 := by simp
  simpa only [expandedGuardDeficit, lintegral_const, measure_univ, mul_one] using
    (lintegral_sub hm hf (ae_of_all μ hpacking))

theorem expected_expandedGuardDeficit_formula {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) (hρtop : ρ ≠ ∞)
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1)
    (hpacking : ∀ c : Configuration (Ambient d), guardDensity (expandAfterDeletion c r t ht) L r ≤ 1) :
    (∫⁻ c, expandedGuardDeficit c L r t ht ∂μ) =
      1 - (retainedIntensity μ (r * (1 - t)) * ENNReal.ofReal ((1 - t) ^ d)) *
        ENNReal.ofReal (((L - r) / L) ^ d) := by
  rw [expected_expandedGuardDeficit_eq μ L r t ht hpacking,
    expected_expanded_guardDensity μ hμ ρ hρ hρtop L r t hr hL ht]

theorem expandedIntensity_le_one {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (hρ : HasIntensity μ 1) (r t : ℝ) (ht0 : 0 ≤ t) (ht : t < 1) :
    processIntensity (μ.map (fun c => expandAfterDeletion c r t ht)) ≤ 1 := by
  rw [expandedIntensity_eq μ hμ 1 hρ (by norm_num) r t ht]
  have hc : ENNReal.ofReal ((1 - t) ^ d) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact pow_le_one₀ (sub_pos.mpr ht).le (by linarith)
  calc
    _ ≤ 1 * 1 := mul_le_mul' (retainedIntensity_le μ 1 hρ _) hc
    _ = 1 := one_mul _

/-- The expected guard loss is at most the expanded intensity loss plus `d*r/L`. -/
theorem expected_expandedGuardDeficit_le {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (L r t ε : ℝ) (hr : 0 < r) (hL : r < L) (ht0 : 0 ≤ t) (ht : t < 1)
    (hε : 0 ≤ ε)
    (hlower : 1 - ε ≤
      (processIntensity (μ.map (fun c => expandAfterDeletion c r t ht))).toReal)
    (hpacking : ∀ c : Configuration (Ambient d), guardDensity (expandAfterDeletion c r t ht) L r ≤ 1) :
    (∫⁻ c, expandedGuardDeficit c L r t ht ∂μ) ≤
      ENNReal.ofReal (ε + (d : ℝ) * r / L) := by
  let ρ := processIntensity (μ.map (fun c => expandAfterDeletion c r t ht))
  have hρ1 : ρ ≤ 1 := expandedIntensity_le_one μ hμ hρ r t ht0 ht
  have hρfin : ρ ≠ ∞ := ne_top_of_le_ne_top (by norm_num) hρ1
  have hρreal : ρ.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hρ1
  have hL0 : 0 < L := hr.trans hL
  have hz : 0 ≤ r / L := div_nonneg hr.le hL0.le
  have hz1 : r / L ≤ 1 := (div_le_one hL0).mpr hL.le
  have hc : (L - r) / L = 1 - r / L := by
    rw [sub_div, div_self hL0.ne']
  have hb : 1 - (ε + (d : ℝ) * r / L) ≤ ρ.toReal * (((L - r) / L) ^ d) := by
    have hh := density_after_expansion_lower_bound d ENNReal.toReal_nonneg
      hρreal hz hz1 hlower
    rw [← hc] at hh
    convert hh using 1; ring
  have he : (∫⁻ c, guardDensity (expandAfterDeletion c r t ht) L r ∂μ) =
      ρ * ENNReal.ofReal (((L - r) / L) ^ d) := by
    rw [expected_expanded_guardDensity μ hμ 1 hρ (by norm_num) L r t hr hL ht]
    rw [show ρ = _ from expandedIntensity_eq μ hμ 1 hρ (by norm_num) r t ht]
  have hprod : ρ * ENNReal.ofReal (((L - r) / L) ^ d) ≠ ∞ :=
    ENNReal.mul_ne_top hρfin ENNReal.ofReal_ne_top
  have hmean : ENNReal.ofReal (1 - (ε + (d : ℝ) * r / L)) ≤
      ∫⁻ c, guardDensity (expandAfterDeletion c r t ht) L r ∂μ := by
    rw [he, ENNReal.ofReal_le_iff_le_toReal hprod, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg (sub_pos.mpr hL).le hL0.le) d)]
    exact hb
  rw [expected_expandedGuardDeficit_eq μ L r t ht hpacking]
  have hbudget : 0 ≤ ε + (d : ℝ) * r / L :=
    add_nonneg hε (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hr.le) hL0.le)
  have hcomp : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - (ε + (d : ℝ) * r / L)) ≤
      ENNReal.ofReal (ε + (d : ℝ) * r / L) := by
    rw [ENNReal.ofReal_sub 1 hbudget, ENNReal.ofReal_one]
    exact tsub_tsub_le
  exact (tsub_le_tsub_left hmean 1).trans hcomp

theorem expected_expandedGuardDeficit_le_of_deletedIntensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (L r t : ℝ) (hr : 0 < r) (hL : r < L) (ht0 : 0 ≤ t) (ht : t < 1)
    (q : ℝ≥0∞) (hq : q ≠ ∞) (hdel : deletedIntensity μ (r * (1 - t)) ≤ q)
    (hpacking : ∀ c : Configuration (Ambient d), guardDensity (expandAfterDeletion c r t ht) L r ≤ 1) :
    (∫⁻ c, expandedGuardDeficit c L r t ht ∂μ) ≤
      ENNReal.ofReal (q.toReal + (d : ℝ) * t + (d : ℝ) * r / L) := by
  apply expected_expandedGuardDeficit_le μ hμ hρ L r t
    (q.toReal + (d : ℝ) * t) hr hL ht0 ht
    (add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg d) ht0)) _ hpacking
  have h := expandedIntensity_lower_bound_of_deletedIntensity μ hμ hρ r t ht0 ht q hq hdel
  convert h using 1
  ring

theorem lintegral_expandedGuardDeficit_prod {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (L r t : ℝ) (ht : t < 1) :
    (∫⁻ p, expandedGuardDeficit p.1 L r t ht ∂(μ.prod ν)) =
      ∫⁻ c, expandedGuardDeficit c L r t ht ∂μ := by
  have hm : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      expandedGuardDeficit p.1 L r t ht) :=
    (measurable_expandedGuardDeficit L r t ht).comp measurable_fst
  rw [lintegral_prod _ hm.aemeasurable]
  simp

/-- Conditional BRR descent with an explicit density Markov term and boundary term. -/
theorem measurable_good_event_of_guardedExpanded_markov {d : ℕ}
    (Λ : Set (Ambient d))
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (L r t R error loss : ℝ)
    (hr : 0 < r) (hL : r < L) (ht : t < 1) (hR : 0 ≤ R) (hw : r + 2 * R ≤ L)
    (η ε p q : ℝ≥0∞) (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hmean : (∫⁻ c, expandedGuardDeficit c L r t ht ∂μ) ≤ ε)
    (H S : Set (Configuration (Ambient d) × Ambient d)) (hH : MeasurableSet H)
    (hgood : ∀ z ∈ H, LocalCrystal Λ
      (translate (-z.2) (guardedExpandedConfiguration z.1 L r t hr hL ht)) R error loss)
    (hcover : Hᶜ ⊆ {z | η ≤ expandedGuardDeficit z.1 L r t ht} ∪ S)
    (hS : (μ.prod (uniformPeriodCell d L)) S ≤ p)
    (hq : q < 1 - (ε / η + p) - ENNReal.ofReal ((d : ℝ) * (r + 2 * R) / L)) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | LocalCrystal Λ (expandAfterDeletion c r t ht) R error loss} ∧ q < μ G := by
  let _ := uniformPeriodCell_probability d L (hr.trans hL)
  have hmean' : (∫⁻ z, expandedGuardDeficit z.1 L r t ht
      ∂(μ.prod (uniformPeriodCell d L))) ≤ ε := by
    rw [lintegral_expandedGuardDeficit_prod]
    exact hmean
  have hfail : (μ.prod (uniformPeriodCell d L)) Hᶜ ≤ ε / η + p := by
    have hb := periodization_failure_probability_le (μ.prod (uniformPeriodCell d L))
      (fun z => expandedGuardDeficit z.1 L r t ht) η ε hη hηtop
      ((measurable_expandedGuardDeficit L r t ht).comp measurable_fst).aemeasurable
      hmean' Hᶜ S ∅ p 0
      (by simpa only [Set.union_empty] using hcover) hS (by simp)
    simpa only [add_zero] using hb
  exact measurable_good_event_of_guardedExpanded_failure Λ μ hμ L r t R error loss
    hr hL ht hR hw H hH hgood (ε / η + p) q hfail hq

/-- Finish the deterministic and probability transfer to all original points.
The analytic cost bound and the measurable periodic good event are still inputs. -/
theorem measurable_good_event_periodization_restoration_of_unit_cost {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (L r t R error loss : ℝ) (hr : 0 < r) (hL : r < L)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hR : 0 ≤ R) (he : 0 ≤ error)
    (hw : r + 2 * ((1 - t)⁻¹ * R) ≤ L)
    (η ε p budget : ℝ≥0∞) (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hmean : (∫⁻ c, expandedGuardDeficit c L r t (by linarith) ∂μ) ≤ ε)
    (H S : Set (Configuration (Ambient d) × Ambient d)) (hH : MeasurableSet H)
    (hgood : ∀ z ∈ H, LocalCrystal Λ
      (translate (-z.2) (guardedExpandedConfiguration z.1 L r t hr hL (by linarith)))
        ((1 - t)⁻¹ * R) error loss)
    (hcover : Hᶜ ⊆ {z | η ≤ expandedGuardDeficit z.1 L r t (by linarith)} ∪ S)
    (hS : (μ.prod (uniformPeriodCell d L)) S ≤ p)
    (hbudget : budget < 1 - (ε / η + p) -
      ENNReal.ofReal ((d : ℝ) * (r + 2 * ((1 - t)⁻¹ * R)) / L))
    (κ cost : ℝ≥0∞) (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (V : Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, x ≠ y → dist x y < r * (1 - t) → κ ≤ V x y)
    (hcost : (∫⁻ c, orderedWindowEnergy V c (unitWindow d) ∂μ) ≤ cost) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | LocalCrystal Λ c R (2 * error + 4 * t * R) loss} ∧
      budget - cost / κ * volume (Metric.closedBall (0 : Ambient d) R) ≤ μ G := by
  have hRad : 0 ≤ (1 - t)⁻¹ * R :=
    mul_nonneg (inv_pos.mpr (by linarith : 0 < 1 - t)).le hR
  obtain ⟨F, hF, hFg, hFm⟩ := measurable_good_event_of_guardedExpanded_markov Λ μ hμ
    L r t ((1 - t)⁻¹ * R) error loss hr hL (by linarith) hRad hw
    η ε p budget hη hηtop hmean H S hH hgood hcover hS hbudget
  have hret : F ⊆ {c | LocalCrystal Λ (c.deleteClose (r * (1 - t)))
      R (2 * error + 4 * t * R) loss} := by
    intro c hc
    exact localCrystal_of_expandAfterDeletion Λ hΛ c r t ht0 ht R error loss hR he (hFg hc)
  obtain ⟨G, hG, hGg, hGm⟩ := measurable_good_event_restoration_of_unit_cost μ hμ
    1 hρ (by norm_num) Λ (r * (1 - t)) R (2 * error + 4 * t * R) loss
    κ cost hκ0 hκtop V hV hcost F hF hret
  exact ⟨G, hG, hGg, (tsub_le_tsub_right hFm.le _).trans hGm⟩

end E8Leech
