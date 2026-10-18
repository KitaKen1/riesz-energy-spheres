import E8Leech.KronLeechExpr

/-!
# The Leech numerator with the second variable inverted

For `t < 1` put `t = 1/s`. The generators at `i/s` are those at `is` after the modular inversion:
`E₂ ↦ −s² E₂ + 6s/π`, `V ↦ s² W`, `W ↦ s² V`, and the logarithm satisfies
`l_B t̂ − Λ = l_S t̂` with `t̂ = s/π` and `l_S = Λ L_S(is)`. With `p = 1/π` the six `z`-side factors
of the numerator of `KronLeechExpr` become `s¹⁶` times

`Ẑ₁ = Z₁⁰`, `Ẑ₂ = Z₂⁰`, `Ẑ₃ = Z₃⁰` (the parts without `t̂`, at the generators of `is`),
`Ẑ₄ = −p² (E₄² F₆ l_S + 2Λ E₄³ V)`, `Ẑ₅ = p² D V`,
`Ẑ₆ = p² (−E₄ F₆ ((V+W)² − W²) + 4 E₄³ V)`,

so that `axE24 = −s¹⁶ (axLPlus0 + axLMinusS)`. The variable `s` enters only through the factor
`s¹⁶` and the nome. Both parts vanish when the generators of the second variable equal those of the
first, for every `û` and `l_A`.

* `axLZS4`, `axLZS5`, `axLZS6`, `axLMinusS`: the logarithmic part.
* `axE24_S`, `axE24K_S`: the numerators of `𝒦̂` and of `𝒦`.
* `axLMinusS_diag`: the logarithmic part vanishes on the diagonal.
-/

namespace E8Leech.Kron

/-- The fourth `z`-side factor with the second variable inverted, divided by `s¹⁶`. -/
def axLZS4 (Λ V W lS p : ℝ) : ℝ :=
  -(p ^ 2 * (axE4 V W ^ 2 * axF6 V W * lS + 2 * Λ * axE4 V W ^ 3 * V))

/-- The fifth `z`-side factor with the second variable inverted, divided by `s¹⁶`. -/
def axLZS5 (V W p : ℝ) : ℝ := p ^ 2 * (axD256 V W * V)

/-- The sixth `z`-side factor with the second variable inverted, divided by `s¹⁶`. -/
def axLZS6 (V W p : ℝ) : ℝ :=
  p ^ 2 * (-(axE4 V W * axF6 V W * ((V + W) ^ 2 - W ^ 2)) + 4 * axE4 V W ^ 3 * V)

/-- The logarithmic part with the second variable inverted, divided by `s¹⁶`. -/
def axLMinusS (Λ Va Wa lA lSA uh V W lS p : ℝ) : ℝ :=
  axLA4 Va Wa uh * axLZS4 Λ V W lS p + axLA5 Λ Va Wa lA lSA uh * axLZS5 V W p +
    axLA6 Λ Va Wa lA lSA uh * axLZS6 V W p

/-- The quasimodular part under the inversion of the second variable. -/
theorem axLPlus_S (Λ E2a Va Wa uh E V W s p : ℝ) :
    axLPlus0 Λ E2a Va Wa uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V) +
        s * p * axLPlus12 Λ E2a Va Wa uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V)
          (s * p) =
      s ^ 16 * axLPlus0 Λ E2a Va Wa uh E V W := by
  simp only [axLPlus0, axLPlus12, axLZ10, axLZ20, axLZ30, axLZ11, axLZ21, axLZ31, axD256, axF6,
    axE4]
  ring

/-- The logarithmic part under the inversion of the second variable. -/
theorem axLMinus_S (Λ Va Wa lA lSA uh V W lS lB s p : ℝ)
    (hlB : lB * (s * p) - Λ = lS * (s * p)) :
    s * p * axLMinus12 Λ Va Wa lA lSA uh (s ^ 2 * W) (s ^ 2 * V) lB (s * p) =
      s ^ 16 * axLMinusS Λ Va Wa lA lSA uh V W lS p := by
  simp only [axLMinus12, axLMinusS, axLZ41, axLZ51, axLZ61, axLZS4, axLZS5, axLZS6, axD256, axF6,
    axE4, hlB]
  ring

/-- **The numerator of `𝒦̂⁽²⁴⁾` with the second variable inverted.** -/
theorem axE24_S (Λ E2a Va Wa lA lSA uh E V W lS lB s p : ℝ)
    (hlB : lB * (s * p) - Λ = lS * (s * p)) :
    axE24 Λ E2a Va Wa lA lSA uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V) lB (s * p) =
      -(s ^ 16 * (axLPlus0 Λ E2a Va Wa uh E V W + axLMinusS Λ Va Wa lA lSA uh V W lS p)) := by
  have h1 := axLPlus_S Λ E2a Va Wa uh E V W s p
  have h2 := axLMinus_S Λ Va Wa lA lSA uh V W lS lB s p hlB
  rw [axE24, axE240, axE2412]
  linear_combination -h1 - h2

/-- **The numerator of `𝒦⁽²⁴⁾` with the second variable inverted.** -/
theorem axE24K_S (Λ E2a Va Wa lA lSA uh E V W lS lB s p : ℝ)
    (hlB : lB * (s * p) - Λ = lS * (s * p)) :
    axE240 Λ E2a Va Wa uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V) -
        s * p * axE2412S Λ E2a Va Wa lA lSA uh (-s ^ 2 * E + 6 * s * p) (s ^ 2 * W) (s ^ 2 * V)
          lB (s * p) =
      -(s ^ 16 * (axLPlus0 Λ E2a Va Wa uh E V W - axLMinusS Λ Va Wa lA lSA uh V W lS p)) := by
  have h1 := axLPlus_S Λ E2a Va Wa uh E V W s p
  have h2 := axLMinus_S Λ Va Wa lA lSA uh V W lS lB s p hlB
  rw [axE240, axE2412S]
  linear_combination -h1 + h2

/-- **The logarithmic part vanishes on the diagonal**, for every `û` and `l_A`. -/
theorem axLMinusS_diag (Λ V W lA lS uh p : ℝ) : axLMinusS Λ V W lA lS uh V W lS p = 0 := by
  simp only [axLMinusS, axLA4, axLA5, axLA6, axLZS4, axLZS5, axLZS6, axT2h, axPsi2h, axPsi4h,
    axD256, axF6, axE4]
  ring

end E8Leech.Kron
