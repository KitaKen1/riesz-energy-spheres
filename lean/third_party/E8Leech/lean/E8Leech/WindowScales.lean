import E8Leech.Asymptotics
import E8Leech.Target
import E8Leech.Deletion

/-!
# The logarithmic window and inverse-dilation error

Use the known parameter u = log (1 / δ). The observation radius is u / log u,
and any strictly better power δ^α absorbs its radius factor relative to δ^γ.
These estimates discharge the O(t R) error from scale restoration. They do not
assert the CKMRV energy bound or the BRR stability input.
-/

namespace E8Leech

open Filter

theorem observationRadius_exp_neg (u : ℝ) :
    observationRadius (Real.exp (-u)) = u / Real.log u := by
  have he : 1 / Real.exp (-u) = Real.exp u := by
    rw [Real.exp_neg, one_div, inv_inv]
  rw [observationRadius, he, Real.log_exp]

theorem observationRadius_exp_neg_pos {u : ℝ} (hu : 1 < u) :
    0 < observationRadius (Real.exp (-u)) := by
  rw [observationRadius_exp_neg]
  exact div_pos (by linarith) (Real.log_pos hu)

theorem observationRadius_exp_neg_le {u : ℝ} (hu : Real.exp 1 ≤ u) :
    observationRadius (Real.exp (-u)) ≤ u := by
  have hlog : 1 ≤ Real.log u := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hu
  rw [observationRadius_exp_neg]
  exact div_le_self ((Real.exp_pos 1).le.trans hu) hlog

theorem observationRadius_pos {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ < Real.exp (-Real.exp 1)) : 0 < observationRadius δ := by
  have hlog : Real.log δ < -Real.exp 1 := by
    simpa only [Real.log_exp] using Real.log_lt_log hδ hsmall
  have hu : 1 < -Real.log δ := by
    have hExp : 1 < Real.exp 1 := by simp
    linarith
  have h := observationRadius_exp_neg_pos hu
  simpa only [neg_neg, Real.exp_log hδ] using h

theorem exp_neg_rpow (u α : ℝ) :
    (Real.exp (-u)) ^ α = Real.exp (-α * u) := by
  rw [← Real.exp_mul]
  congr 1
  ring

theorem eventually_scale_error_absorption (α γ ε : ℝ)
    (hgap : γ < α) (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop,
      Real.exp (-α * u) * observationRadius (Real.exp (-u)) ≤ ε * Real.exp (-γ * u) := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_polynomial_exp_lt 1 (α - γ) ε (by linarith) hε] with u hu hp
  have hp' : u * Real.exp (-(α - γ) * u) ≤ ε := by
    simpa only [Real.rpow_one] using hp.le
  calc
    Real.exp (-α * u) * observationRadius (Real.exp (-u)) ≤ Real.exp (-α * u) * u :=
      mul_le_mul_of_nonneg_left (observationRadius_exp_neg_le hu) (Real.exp_pos _).le
    _ = (u * Real.exp (-(α - γ) * u)) * Real.exp (-γ * u) := by
      rw [mul_comm (Real.exp (-α * u)) u, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ε * Real.exp (-γ * u) := mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le

theorem exists_small_scale_error_bound (α γ ε : ℝ) (hgap : γ < α) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        δ ^ α * observationRadius δ ≤ ε * δ ^ γ := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_scale_error_absorption α γ ε hgap hε)
  let U := max M (Real.exp 1 + 1)
  have hMU : M ≤ U := le_max_left _ _
  have hEU : Real.exp 1 < U := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨Real.exp (-U), Real.exp_pos _, Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro δ hδ hsmall
  have hlog : Real.log δ < -U := by
    simpa only [Real.log_exp] using Real.log_lt_log hδ hsmall
  have hbound := hM (-Real.log δ) (by linarith : M ≤ -Real.log δ)
  rw [← exp_neg_rpow, ← exp_neg_rpow] at hbound
  simpa only [neg_neg, Real.exp_log hδ] using hbound

theorem exists_one_thirteenth_scale_error_bound :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        4 * δ ^ (1 / 3 : ℝ) * observationRadius δ ≤ δ ^ (1 / 13 : ℝ) := by
  obtain ⟨δ₀, h0, hs, hb⟩ :=
    exists_small_scale_error_bound (1 / 3) (1 / 13) (1 / 4) (by norm_num) (by norm_num)
  refine ⟨δ₀, h0, hs, ?_⟩
  intro δ hδ hsmall
  have h := hb δ hδ hsmall
  nlinarith

theorem one_third_cutoff_cube {δ : ℝ} (hδ : 0 ≤ δ) :
    (δ ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = δ := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow hδ (by norm_num : (3 : ℕ) ≠ 0)

theorem one_third_cutoff_le_half {δ : ℝ} (hδ : 0 ≤ δ) (hs : δ ≤ 1 / 8) :
    δ ^ (1 / 3 : ℝ) ≤ 1 / 2 := by
  apply (pow_le_pow_iff_left₀ (n := 3) (Real.rpow_nonneg hδ _)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mp
  rw [one_third_cutoff_cube hδ]
  norm_num
  exact hs

theorem exists_one_third_restoration_parameters :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        0 < δ ^ (1 / 3 : ℝ) ∧ δ ^ (1 / 3 : ℝ) ≤ 1 / 2 ∧
        δ = (δ ^ (1 / 3 : ℝ)) ^ (3 : ℕ) ∧ 0 < observationRadius δ ∧
        4 * δ ^ (1 / 3 : ℝ) * observationRadius δ ≤ δ ^ (1 / 13 : ℝ) := by
  obtain ⟨δ₁, h₁, hsmall₁, hb⟩ := exists_one_thirteenth_scale_error_bound
  refine ⟨min δ₁ (1 / 8), lt_min h₁ (by norm_num),
    lt_of_le_of_lt (min_le_left _ _) hsmall₁, ?_⟩
  intro δ hδ hsmall
  have hδ₁ : δ < δ₁ := hsmall.trans_le (min_le_left _ _)
  have hδ₈ : δ ≤ 1 / 8 := hsmall.le.trans (min_le_right _ _)
  exact ⟨Real.rpow_pos_of_pos hδ _, one_third_cutoff_le_half hδ.le hδ₈,
    (one_third_cutoff_cube hδ.le).symm, observationRadius_pos hδ (hδ₁.trans hsmall₁),
    hb δ hδ hδ₁⟩

end E8Leech
