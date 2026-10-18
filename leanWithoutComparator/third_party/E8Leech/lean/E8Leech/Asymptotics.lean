import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing powers of the logarithmic parameter

Use `u = log (1 / δ)`. Polynomial factors in `u` can be absorbed by any fixed exponential
gap. The small positive gap `1/312` is supplied explicitly, rather than optimized by Lean.
The complete `u / log u` window estimates remain to be assembled.
-/

namespace E8Leech

open Filter

theorem polynomial_exp_absorption (k b : ℝ) (hb : 0 < b) :
    Tendsto (fun u : ℝ => u ^ k * Real.exp (-b * u)) atTop (nhds 0) :=
  tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k b hb

theorem eventually_polynomial_exp_lt (k b η : ℝ) (hb : 0 < b) (hη : 0 < η) :
    ∀ᶠ u : ℝ in atTop, u ^ k * Real.exp (-b * u) < η :=
  (polynomial_exp_absorption k b hb).eventually_lt_const hη

end E8Leech
