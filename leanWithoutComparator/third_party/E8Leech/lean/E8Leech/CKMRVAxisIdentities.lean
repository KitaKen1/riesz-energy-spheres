import E8Leech.CKMRVAxisNumerator

/-!
# Algebraic identities of the axis numerators on the singular curves

The axis numerators `axPhi` (`= Δ(τ)·2𝒦̂·Δ(z)(j(τ) − j(z))`) and `axPhiK` (the same with `𝒦`)
vanish on the two singular curves *as polynomial identities* in the generators:

* **diagonal**: if the `z`-side generators `E₂, V, W` equal the `τ`-side ones and the logarithms
  differ only in their polynomial parts (`L = L₀ − πu`, `L_z = L₀ − πt`), then `axPhi = 0` for
  independent `u, t`, and `axPhiK = 2(t − u)E₄²E₆Δ`;
* **antidiagonal**: if the `z`-side generators are the `S`-transforms of the `τ`-side ones
  (`E₂ ↦ −s²E₂ + 6s/π`, `V ↦ s²W`, `W ↦ s²V`, `L_z = L_S`, `t = 1/s`), then both vanish, again
  for independent `u, s` (the case `s = u` is the antidiagonal `t = 1/u`).

These are the identities behind the removable singularities of `𝒦̂` and `𝒦` at `z = τ` and
`z = −1/τ` on the imaginary axis. The decoupled form (independent polynomial parts `u, t`) is what
the divided-difference (telescoping) argument for (6.4)(1) uses.
-/

noncomputable section

namespace E8Leech

open scoped Real

theorem axPhi_diag (E2 V W L0 LS u t : ℝ) (ht : t ≠ 0) :
    axPhi E2 V W (L0 - π * u) LS u E2 V W (L0 - π * t) t = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axPhi, axPlusNum, axMinusNum, axPsiTwo, axPsiFour, axE4, axE6, axDelta]
  field_simp
  ring

theorem axPhiK_diag (E2 V W L0 LS u t : ℝ) (ht : t ≠ 0) :
    axPhiK E2 V W (L0 - π * u) LS u E2 V W (L0 - π * t) t =
      2 * (t - u) * axE4 V W ^ 2 * axE6 V W * axDelta V W := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axPhiK, axPlusNum, axMinusNum, axPsiTwo, axPsiFour, axE4, axE6, axDelta]
  field_simp
  ring

theorem axPhi_anti (E2 V W La LS u s : ℝ) :
    axPhi E2 V W La LS u (-s ^ 2 * E2 + 6 * s / π) (s ^ 2 * W) (s ^ 2 * V) LS s⁻¹ = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axPhi, axPlusNum, axMinusNum, axPsiTwo, axPsiFour, axE4, axE6, axDelta]
  field_simp
  ring

theorem axPhiK_anti (E2 V W La LS u s : ℝ) :
    axPhiK E2 V W La LS u (-s ^ 2 * E2 + 6 * s / π) (s ^ 2 * W) (s ^ 2 * V) LS s⁻¹ = 0 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [axPhiK, axPlusNum, axMinusNum, axPsiTwo, axPsiFour, axE4, axE6, axDelta]
  field_simp
  ring

end E8Leech
