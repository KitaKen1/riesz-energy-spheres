import Riesz.RationalSizeCeiling8

/-! A rational-size configuration immediately below every integer point count.

`rationalSizeFloor8 d N = (d ⌊N^{1/8}/d⌋)⁸ ≤ N` and its ratio to `N` tends to `1`; the missing
`N - M` points are added to a rational-size configuration. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SphericalRiesz

def rationalSizeFloorIndex8 (d N : ℕ) : ℕ :=
  ⌊((N:ℝ) ^ (1/8:ℝ))/(d:ℝ)⌋₊

def rationalSizeFloor8 (d N : ℕ) : ℕ := (d*rationalSizeFloorIndex8 d N)^8

theorem rationalSizeFloorIndex8_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (rationalSizeFloorIndex8 d) atTop atTop :=
  tendsto_nat_floor_atTop.comp (rationalSizeIndex8_argument_tendsto d hd)

theorem rationalSizeFloor8_le (d N : ℕ) (hd : 0 < d) : rationalSizeFloor8 d N ≤ N := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hx : 0 ≤ ((N:ℝ) ^ (1/8:ℝ))/(d:ℝ) := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hdR.le
  have hr : ((d*rationalSizeFloorIndex8 d N:ℕ):ℝ) ≤ (N:ℝ) ^ (1/8:ℝ) := by
    have h := Nat.floor_le hx
    change (rationalSizeFloorIndex8 d N:ℝ) ≤ _ at h
    have hh := (le_div_iff₀ hdR).mp h
    push_cast
    linarith
  have hpow := pow_le_pow_left₀ (by positivity) hr 8
  rw [real_eighth_root_pow] at hpow
  exact_mod_cast hpow

theorem rationalSizeFloor8_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (rationalSizeFloor8 d N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp
    (rationalSizeIndex8_argument_tendsto d hd)).pow 8
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hnz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (((rationalSizeFloorIndex8 d N:ℕ):ℝ)/((N:ℝ)^(1/8:ℝ)/(d:ℝ)))^8 = _
  rw [div_pow, div_pow, real_eighth_root_pow]
  unfold rationalSizeFloor8
  push_cast
  field_simp [hnz, hdz]

end SphericalRiesz
