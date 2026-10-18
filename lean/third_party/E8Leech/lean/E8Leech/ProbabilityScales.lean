import E8Leech.BRRScales
import E8Leech.GuardedPeriodization

/-!
# Absorbing probability losses into the logarithmic rate

Only scalar inequalities are proved here. The Markov power `δ^(1/78)` and
the deletion term `δ^(1/3) * Rδ^d` are smaller than `Rδ^(-1/2)` uniformly
below a threshold chosen from their fixed coefficients. Point-process and
periodic-stability hypotheses remain in the transfer theorems.
-/

namespace E8Leech

open Filter Set MeasureTheory
open scoped ENNReal

/-- A bounding box supplies the only ball-volume estimate needed for absorption. -/
theorem closedBall_zero_subset_probability_box {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Metric.closedBall (0 : Ambient d) R ⊆ coordinateBox d (-2 * R) (2 * R) := by
  intro x hx i
  have hd : dist x (0 : Ambient d) ≤ R := Metric.mem_closedBall.mp hx
  have hi : |x i| ≤ R := by
    have hh := PiLp.dist_apply_le x (0 : Ambient d) i
    simpa only [Real.dist_eq, PiLp.zero_apply, sub_zero] using hh.trans hd
  have hb := abs_le.mp hi
  constructor <;> linarith

theorem volume_closedBall_le_probability_box {d : ℕ} {R : ℝ} (hR : 0 < R) :
    volume (Metric.closedBall (0 : Ambient d) R) ≤ ENNReal.ofReal ((4 : ℝ) ^ d * R ^ d) := by
  calc
    _ ≤ volume (coordinateBox d (-2 * R) (2 * R)) :=
      measure_mono (closedBall_zero_subset_probability_box hR)
    _ = ENNReal.ofReal ((4 : ℝ) ^ d * R ^ d) := by
      rw [volume_coordinateBox]
      have he : 2 * R - -2 * R = 4 * R := by ring
      rw [he, ← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hR.le) d, mul_pow]

theorem markov_power_identity {δ : ℝ} (hδ : 0 < δ) (K : ℝ) :
    δ ^ (1 / 3 : ℝ) / (K * δ ^ (25 / 78 : ℝ)) =
      K⁻¹ * δ ^ (1 / 78 : ℝ) := by
  have he : (1 / 3 : ℝ) - 25 / 78 = 1 / 78 := by norm_num
  rw [← he, Real.rpow_sub hδ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A deliberately loose constant avoids any square-root arithmetic. -/
theorem brr_probability_radius_le {Rδ Rη : ℝ}
    (hRδ : 0 < Rδ) (hlow : (25 / 156 : ℝ) * Rδ ≤ Rη) :
    Rη ^ (-1 / 2 : ℝ) ≤ 7 * Rδ ^ (-1 / 2 : ℝ) := by
  have hq : 0 < (25 / 156 : ℝ) := by norm_num
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hq hRδ) hlow
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  rw [Real.mul_rpow hq.le hRδ.le] at hpow
  have hc : (25 / 156 : ℝ) ^ (-1 / 2 : ℝ) ≤ 7 := by
    calc
      _ ≤ (25 / 156 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hq (by norm_num) (by norm_num)
      _ ≤ 7 := by norm_num
  exact hpow.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hRδ.le _))

/-- An explicit finite period length controls both guard-density and boundary losses. -/
theorem exists_finite_period_length (d : ℕ) (r R ε b : ℝ)
    (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 < ε) (hb : 0 < b) :
    ∃ L : ℝ, r < L ∧ r + 2 * R ≤ L ∧
      (d : ℝ) * r / L ≤ ε ∧ (d : ℝ) * (r + 2 * R) / L ≤ b := by
  let L := r + 2 * R + 1 + (d : ℝ) * r / ε + (d : ℝ) * (r + 2 * R) / b
  have hfirst : 0 ≤ (d : ℝ) * r / ε :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hr.le) hε.le
  have hsecond : 0 ≤ (d : ℝ) * (r + 2 * R) / b :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hb.le
  have hLr : r < L := by dsimp [L]; linarith
  have hL0 : 0 < L := hr.trans hLr
  refine ⟨L, hLr, by dsimp [L]; linarith, ?_, ?_⟩
  · apply (div_le_iff₀ hL0).mpr
    have hlarge : (d : ℝ) * r / ε ≤ L := by dsimp [L]; linarith
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  · apply (div_le_iff₀ hL0).mpr
    have hlarge : (d : ℝ) * (r + 2 * R) / b ≤ L := by dsimp [L]; linarith
    have h := (div_le_iff₀ hb).mp hlarge
    nlinarith

theorem eventually_window_probability_absorption (A k b ε : ℝ)
    (hA : 0 ≤ A) (hk : 0 ≤ k) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop,
      A * Real.exp (-b * u) * observationRadius (Real.exp (-u)) ^ k ≤
        ε * observationRadius (Real.exp (-u)) ^ (-1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_polynomial_exp_lt (k + 1 / 2) b (ε / (A + 1)) hb
      (div_pos hε (by linarith))] with u hu hp
  have hu1 : 1 < u := lt_of_lt_of_le (by simp : 1 < Real.exp 1) hu
  have hu0 : 0 < u := by linarith
  have hR : 0 < observationRadius (Real.exp (-u)) := observationRadius_exp_neg_pos hu1
  have hRu := observationRadius_exp_neg_le hu
  have hpow : observationRadius (Real.exp (-u)) ^ (k + 1 / 2 : ℝ) ≤
      u ^ (k + 1 / 2 : ℝ) := Real.rpow_le_rpow hR.le hRu (by linarith)
  have hp0 : 0 ≤ u ^ (k + 1 / 2 : ℝ) * Real.exp (-b * u) :=
    mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.exp_pos _).le
  have hbound : A * (u ^ (k + 1 / 2 : ℝ) * Real.exp (-b * u)) ≤ ε := by
    have h := (lt_div_iff₀ (by linarith : 0 < A + 1)).mp hp
    nlinarith
  have hweighted : (A * Real.exp (-b * u) * observationRadius (Real.exp (-u)) ^ k) *
      observationRadius (Real.exp (-u)) ^ (1 / 2 : ℝ) ≤ ε := by
    calc
      _ = A * Real.exp (-b * u) * observationRadius (Real.exp (-u)) ^ (k + 1 / 2 : ℝ) := by
        rw [Real.rpow_add hR]
        ring
      _ ≤ A * Real.exp (-b * u) * u ^ (k + 1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hA (Real.exp_pos _).le)
      _ ≤ ε := by nlinarith [hbound]
  calc
    _ = ((A * Real.exp (-b * u) * observationRadius (Real.exp (-u)) ^ k) *
        observationRadius (Real.exp (-u)) ^ (1 / 2 : ℝ)) *
          observationRadius (Real.exp (-u)) ^ (-1 / 2 : ℝ) := by
      rw [mul_assoc (A * Real.exp (-b * u) * observationRadius (Real.exp (-u)) ^ k),
        ← Real.rpow_add hR]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hweighted (Real.rpow_nonneg hR.le _)

theorem exists_small_window_probability_bound (A k b ε : ℝ)
    (hA : 0 ≤ A) (hk : 0 ≤ k) (hb : 0 < b) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        A * δ ^ b * observationRadius δ ^ k ≤ ε * observationRadius δ ^ (-1 / 2 : ℝ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_window_probability_absorption A k b ε hA hk hb hε)
  let U := max M (Real.exp 1 + 1)
  have hMU : M ≤ U := le_max_left _ _
  have hEU : Real.exp 1 < U := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨Real.exp (-U), Real.exp_pos _, Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro δ hδ hsmall
  have hlog : Real.log δ < -U := by
    simpa only [Real.log_exp] using Real.log_lt_log hδ hsmall
  have h := hM (-Real.log δ) (by linarith : M ≤ -Real.log δ)
  rw [← exp_neg_rpow] at h
  simpa only [neg_neg, Real.exp_log hδ] using h

/-- Both concrete probability losses are absorbed with one law-independent threshold. -/
theorem exists_small_markov_deletion_probability_bounds (d : ℕ) (A B ε : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        A * δ ^ (1 / 78 : ℝ) + B * δ ^ (1 / 3 : ℝ) * observationRadius δ ^ d ≤
          ε * observationRadius δ ^ (-1 / 2 : ℝ) := by
  obtain ⟨δ₁, h₁, hs₁, hM⟩ := exists_small_window_probability_bound A 0 (1 / 78)
    (ε / 2) hA (by norm_num) (by norm_num) (half_pos hε)
  obtain ⟨δ₂, h₂, hs₂, hD⟩ := exists_small_window_probability_bound B d (1 / 3)
    (ε / 2) hB (Nat.cast_nonneg _) (by norm_num) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min h₁ h₂, lt_of_le_of_lt (min_le_left _ _) hs₁, ?_⟩
  intro δ hδ hsmall
  have hM' := hM δ hδ (hsmall.trans_le (min_le_left _ _))
  have hD' := hD δ hδ (hsmall.trans_le (min_le_right _ _))
  simp only [Real.rpow_zero, mul_one] at hM'
  rw [Real.rpow_natCast] at hD'
  nlinarith

theorem exists_small_deleted_volume_probability_bound (d : ℕ) (C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ENNReal.ofReal (C * δ ^ (1 / 3 : ℝ)) *
            volume (Metric.closedBall (0 : Ambient d) (observationRadius δ)) ≤
          ENNReal.ofReal (ε * observationRadius δ ^ (-1 / 2 : ℝ)) := by
  obtain ⟨δ₀, h0, hs, hb⟩ := exists_small_window_probability_bound (C * (4 : ℝ) ^ d)
    d (1 / 3) ε (mul_nonneg hC (pow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
    (by norm_num) hε
  refine ⟨δ₀, h0, hs, ?_⟩
  intro δ hδ hsmall
  have hR := observationRadius_pos hδ (hsmall.trans hs)
  have h := hb δ hδ hsmall
  rw [Real.rpow_natCast] at h
  calc
    _ ≤ ENNReal.ofReal (C * δ ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal ((4 : ℝ) ^ d * observationRadius δ ^ d) :=
      mul_le_mul' le_rfl (volume_closedBall_le_probability_box hR)
    _ = ENNReal.ofReal ((C * (4 : ℝ) ^ d) * δ ^ (1 / 3 : ℝ) * observationRadius δ ^ d) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hδ.le _))]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

end E8Leech
