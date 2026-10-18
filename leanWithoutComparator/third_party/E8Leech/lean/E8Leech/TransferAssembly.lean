import E8Leech.ProbabilityScales
import E8Leech.ScaleRestoration

/-!
# Uniform constants and probability budgets for the stationary transfer

Choose the known density tolerance `η = δ^(25/78)` directly, so `K = 1`.
All coefficients are absorbed into the small-excess threshold and the final
constant. No analytic energy estimate or BRR theorem is asserted here.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

def transferConstant (E B : ℝ) : ℝ := 2 * E + 7 * B + 5

theorem transferConstant_pos {E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B) :
    0 < transferConstant E B := by unfold transferConstant; linarith

theorem localCrystal_mono_loss {d : ℕ} {Λ : Set (Ambient d)}
    {c : Configuration (Ambient d)} {R error loss loss' : ℝ}
    (hgood : LocalCrystal Λ c R error loss) (hl : loss ≤ loss') :
    LocalCrystal Λ c R error loss' := by
  refine ⟨hgood.1, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl).trans hgood.2

/-- Scalar facts needed by the deterministic and measure-theoretic transfer. -/
structure TransferScaleData (d : ℕ) (A E B c η₀ δ : ℝ) : Prop where
  cutoff_pos : 0 < δ ^ (1 / 3 : ℝ)
  cutoff_half : δ ^ (1 / 3 : ℝ) ≤ 1 / 2
  radius_pos : 0 < observationRadius δ
  eta_pos : 0 < δ ^ (25 / 78 : ℝ)
  eta_small : δ ^ (25 / 78 : ℝ) < η₀
  eta_radius_pos : 0 < observationRadius (δ ^ (25 / 78 : ℝ))
  contains : observationRadius (δ ^ (25 / 78 : ℝ)) ≤
    (1 - δ ^ (1 / 3 : ℝ))⁻¹ * observationRadius δ
  diameter : 2 * ((1 - δ ^ (1 / 3 : ℝ))⁻¹ * observationRadius δ) ≤
    (624 / 25 : ℝ) * observationRadius (δ ^ (25 / 78 : ℝ))
  error : 2 * (E * Real.exp (c * observationRadius (δ ^ (25 / 78 : ℝ))) *
    (δ ^ (25 / 78 : ℝ)) ^ (1 / 4 : ℝ)) +
    4 * δ ^ (1 / 3 : ℝ) * observationRadius δ ≤
    transferConstant E B * δ ^ (1 / 13 : ℝ)
  stability : B * observationRadius (δ ^ (25 / 78 : ℝ)) ^ (-1 / 2 : ℝ) ≤
    7 * B * observationRadius δ ^ (-1 / 2 : ℝ)
  loss : B * observationRadius (δ ^ (25 / 78 : ℝ)) ^ (-1 / 2 : ℝ) ≤
    transferConstant E B * observationRadius δ ^ (-1 / 2 : ℝ)
  markov : ((A + (d : ℝ) + 1) * δ ^ (1 / 3 : ℝ)) /
    δ ^ (25 / 78 : ℝ) ≤ observationRadius δ ^ (-1 / 2 : ℝ)
  deletion : ENNReal.ofReal (A * δ ^ (1 / 3 : ℝ)) *
    volume (Metric.closedBall (0 : Ambient d) (observationRadius δ)) ≤
    ENNReal.ofReal (observationRadius δ ^ (-1 / 2 : ℝ))

/-- The common threshold is chosen before either the process law or `δ`. -/
theorem exists_uniform_transfer_parameters (d : ℕ) (A E B c η₀ : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → TransferScaleData d A E B c η₀ δ := by
  obtain ⟨δ₁, h₁, hs₁, hr⟩ := exists_small_brr_restoration_parameters 1 c η₀
    (by norm_num) hc hη₀
  obtain ⟨δ₂, h₂, hs₂, hb⟩ := exists_small_brr_scale_parameters 1 c η₀
    (by norm_num) hc hη₀
  obtain ⟨δ₃, h₃, hs₃, hm⟩ := exists_small_window_probability_bound
    (A + (d : ℝ) + 1) 0 (1 / 78) 1 (by positivity) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨δ₄, h₄, hs₄, hd⟩ := exists_small_deleted_volume_probability_bound d A 1
    hA (by norm_num)
  refine ⟨min (min δ₁ δ₂) (min δ₃ δ₄),
    lt_min (lt_min h₁ h₂) (lt_min h₃ h₄),
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) hs₁, ?_⟩
  intro δ hδ hsmall
  have hδ₁ : δ < δ₁ := hsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₂ : δ < δ₂ := hsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₃ : δ < δ₃ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₄ : δ < δ₄ := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hr' := hr δ hδ hδ₁
  have hb' := hb δ hδ hδ₂
  simp only [one_mul, Real.one_rpow] at hr' hb'
  have hR := observationRadius_pos hδ (hδ₁.trans hs₁)
  have hprob := mul_le_mul_of_nonneg_left
    (brr_probability_radius_le hR hb'.2.2.2.1) hB
  have hprob' : B * observationRadius (δ ^ (25 / 78 : ℝ)) ^ (-1 / 2 : ℝ) ≤
      7 * B * observationRadius δ ^ (-1 / 2 : ℝ) := by nlinarith [hprob]
  refine ⟨hr'.1, hr'.2.1, hR, hr'.2.2.1, hr'.2.2.2.1,
    hr'.2.2.2.2.1, hr'.2.2.2.2.2.1, hr'.2.2.2.2.2.2.1, ?_, hprob', ?_, ?_, ?_⟩
  · have he := mul_le_mul_of_nonneg_left hr'.2.2.2.2.2.2.2.1 hE
    have hp : 0 ≤ δ ^ (1 / 13 : ℝ) := Real.rpow_nonneg hδ.le _
    dsimp [transferConstant]
    nlinarith [hr'.2.2.2.2.2.2.2.2]
  · dsimp [transferConstant]
    nlinarith [Real.rpow_nonneg hR.le (-1 / 2 : ℝ)]
  · have hh := hm δ hδ hδ₃
    simp only [Real.rpow_zero, mul_one, one_mul] at hh
    calc
      _ = (A + (d : ℝ) + 1) * δ ^ (1 / 78 : ℝ) := by
        have hi := markov_power_identity hδ 1
        simp only [one_mul, inv_one] at hi
        rw [mul_div_assoc, hi]
      _ ≤ _ := hh
  · simpa only [one_mul] using hd δ hδ hδ₄

/-- Reserve one positive rate unit for the strict good-section inequality. -/
theorem ennreal_strict_transfer_budget {B q m p b : ℝ}
    (hB : 0 ≤ B) (hq : 0 < q) (hm0 : 0 ≤ m) (hp0 : 0 ≤ p) (hb0 : 0 ≤ b)
    (hm : m ≤ q) (hp : p ≤ 7 * B * q) (hb : b ≤ q)
    (hpos : 0 < 1 - (7 * B + 3) * q) :
    ENNReal.ofReal (1 - (7 * B + 3) * q) <
      1 - (ENNReal.ofReal m + ENNReal.ofReal p) - ENNReal.ofReal b := by
  have hsum : m + p + b ≤ (7 * B + 2) * q := by linarith
  calc
    _ < ENNReal.ofReal (1 - (7 * B + 2) * q) := by
      apply ENNReal.ofReal_lt_ofReal_iff'.mpr
      constructor <;> linarith
    _ = 1 - ENNReal.ofReal ((7 * B + 2) * q) := by
      rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one]
    _ ≤ 1 - ENNReal.ofReal (m + p + b) := tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hsum) _
    _ = _ := by
      rw [ENNReal.ofReal_add (add_nonneg hm0 hp0) hb0, ENNReal.ofReal_add hm0 hp0,
        tsub_add_eq_tsub_tsub]

theorem ennreal_restored_transfer_budget {E B q : ℝ}
    (hE : 0 ≤ E) (_hB : 0 ≤ B) (hq : 0 ≤ q) {D : ℝ≥0∞}
    (hD : D ≤ ENNReal.ofReal q) :
    ENNReal.ofReal (1 - transferConstant E B * q) ≤
      ENNReal.ofReal (1 - (7 * B + 3) * q) - D := by
  calc
    _ ≤ ENNReal.ofReal (1 - (7 * B + 4) * q) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [transferConstant]
      nlinarith
    _ = ENNReal.ofReal (1 - (7 * B + 3) * q) - ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_sub _ hq]
      congr 1
      ring
    _ ≤ _ := tsub_le_tsub_left hD _

end E8Leech
