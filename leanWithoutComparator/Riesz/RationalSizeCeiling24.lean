import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A rational-size competitor immediately above every integer point count.
Dimension 24: the ceil/x limit avoids a separate discrete twenty-fourth-root algorithm. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SphericalRiesz

def rationalSizeIndex24 (d N : ℕ) : ℕ :=
  ⌈((N:ℝ) ^ (1/24:ℝ))/(d:ℝ)⌉₊

def rationalSizeCeiling24 (d N : ℕ) : ℕ := (d*rationalSizeIndex24 d N)^24

theorem real_twentyFourth_root_pow (N : ℕ) : ((N:ℝ) ^ (1/24:ℝ))^24 = (N:ℝ) := by
  simpa using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (24:ℕ) ≠ 0)

theorem rationalSizeIndex24_argument_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N:ℝ) ^ (1/24:ℝ))/(d:ℝ)) atTop atTop := by
  exact Tendsto.atTop_div_const (by exact_mod_cast hd)
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/24)).comp
      tendsto_natCast_atTop_atTop)

theorem rationalSizeIndex24_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (rationalSizeIndex24 d) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (rationalSizeIndex24_argument_tendsto d hd)

theorem rationalSizeCeiling24_ge (d N : ℕ) (hd : 0 < d) : N ≤ rationalSizeCeiling24 d N := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hr : (N:ℝ) ^ (1/24:ℝ) ≤ (d*rationalSizeIndex24 d N:ℕ) := by
    have h := Nat.le_ceil (((N:ℝ) ^ (1/24:ℝ))/(d:ℝ))
    change _ ≤ (rationalSizeIndex24 d N:ℝ) at h
    have hh := (div_le_iff₀ hdR).mp h
    simpa only [Nat.cast_mul, mul_comm] using hh
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hr 24
  rw [real_twentyFourth_root_pow] at hpow
  exact_mod_cast hpow

theorem rationalSizeCeiling24_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (rationalSizeCeiling24 d N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_ceil_div_atTop (R := ℝ)).comp
    (rationalSizeIndex24_argument_tendsto d hd)).pow 24
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hnz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (((rationalSizeIndex24 d N:ℕ):ℝ)/((N:ℝ)^(1/24:ℝ)/(d:ℝ)))^24 = _
  rw [div_pow, div_pow, real_twentyFourth_root_pow]
  unfold rationalSizeCeiling24
  push_cast
  field_simp [hnz, hdz]

theorem rationalSizeCeiling24_inverse_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N:ℝ)/(rationalSizeCeiling24 d N:ℝ)) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using (rationalSizeCeiling24_ratio_tendsto d hd).inv₀ one_ne_zero

end SphericalRiesz
