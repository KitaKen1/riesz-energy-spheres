import Riesz.Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A rational-size competitor immediately above every integer point count.
The existing ceil/x limit avoids a separate discrete eighth-root algorithm. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SphericalRiesz

def rationalSizeIndex8 (d N : ℕ) : ℕ :=
  ⌈((N:ℝ) ^ (1/8:ℝ))/(d:ℝ)⌉₊

def rationalSizeCeiling8 (d N : ℕ) : ℕ := (d*rationalSizeIndex8 d N)^8

theorem real_eighth_root_pow (N : ℕ) : ((N:ℝ) ^ (1/8:ℝ))^8 = (N:ℝ) := by
  simpa using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (8:ℕ) ≠ 0)

theorem rationalSizeIndex8_argument_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N:ℝ) ^ (1/8:ℝ))/(d:ℝ)) atTop atTop := by
  exact Tendsto.atTop_div_const (by exact_mod_cast hd)
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp
      tendsto_natCast_atTop_atTop)

theorem rationalSizeIndex8_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (rationalSizeIndex8 d) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (rationalSizeIndex8_argument_tendsto d hd)

theorem rationalSizeCeiling8_ge (d N : ℕ) (hd : 0 < d) : N ≤ rationalSizeCeiling8 d N := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hr : (N:ℝ) ^ (1/8:ℝ) ≤ (d*rationalSizeIndex8 d N:ℕ) := by
    have h := Nat.le_ceil (((N:ℝ) ^ (1/8:ℝ))/(d:ℝ))
    change _ ≤ (rationalSizeIndex8 d N:ℝ) at h
    have hh := (div_le_iff₀ hdR).mp h
    simpa only [Nat.cast_mul, mul_comm] using hh
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hr 8
  rw [real_eighth_root_pow] at hpow
  exact_mod_cast hpow

theorem rationalSizeCeiling8_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (rationalSizeCeiling8 d N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_ceil_div_atTop (R := ℝ)).comp
    (rationalSizeIndex8_argument_tendsto d hd)).pow 8
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hnz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (((rationalSizeIndex8 d N:ℕ):ℝ)/((N:ℝ)^(1/8:ℝ)/(d:ℝ)))^8 = _
  rw [div_pow, div_pow, real_eighth_root_pow]
  unfold rationalSizeCeiling8
  push_cast
  field_simp [hnz, hdz]

theorem rationalSizeCeiling8_inverse_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N:ℝ)/(rationalSizeCeiling8 d N:ℝ)) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using (rationalSizeCeiling8_ratio_tendsto d hd).inv₀ one_ne_zero

theorem rationalSizeCeiling8_sqrt_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => Real.sqrt ((N:ℝ)/(rationalSizeCeiling8 d N:ℝ)))
      atTop (𝓝 1) := by
  simpa only [Real.sqrt_one] using (rationalSizeCeiling8_inverse_ratio_tendsto d hd).sqrt

end SphericalRiesz
