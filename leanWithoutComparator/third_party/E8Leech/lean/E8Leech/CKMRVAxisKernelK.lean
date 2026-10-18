import E8Leech.CKMRVAxisNumerator

/-!
# The kernel `𝒦⁽⁸⁾ = (K₊ + K₋)/2` on the imaginary axes

The companion of `ckmrvEightHatKernel_axis`: off the singular curves
`2 𝒦(iu, it) · 𝒩 = axPhiK`, with the same polynomial `𝒩 = axNu` and with the sign of the
logarithmic part changed. By `ckmrvEightHatKernel_imagPt` the hat kernel at `i/u` is
`−u⁴ 𝒦(iu, ·)`, so the inequality (6.4)(1) for `u < 1` is the negativity of `𝒦` for `u > 1`.
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

theorem ckmrvEight_algebra (P M D J : ℂ) (pr mr db jr : ℝ) (hP : P = I * (pr : ℂ))
    (hM : M = (mr : ℂ)) (hD : D = (db : ℂ)) (hJ : J = (jr : ℂ)) (hdb : db ≠ 0) (hjr : jr ≠ 0) :
    (P / (36 * (π : ℂ) ^ (-2 : ℤ) * I * D * J) + M / (2 * 1728 * (π : ℂ) * D * J)) / 2 =
      (((π ^ 2 * pr / 36 + mr / (3456 * π)) / (db * jr) / 2 : ℝ) : ℂ) := by
  subst hP hM hD hJ
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπc : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdbc : (db : ℂ) ≠ 0 := ofReal_ne_zero.mpr hdb
  have hjrc : (jr : ℂ) ≠ 0 := ofReal_ne_zero.mpr hjr
  rw [zpow_neg, zpow_two]
  push_cast
  field_simp
  ring

/-- **The kernel `𝒦` on the axes.** Off the singular curves,
`2 𝒦(iu, it) · 𝒩 = Φ_𝒦` with `𝒩 = Δ(iu)Δ(it)(j(iu) − j(it))`. -/
theorem ckmrvEightKernel_axis {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    2 * (ckmrvEightKernel (imagPt u) (imagPt t)).re *
        axNu (axV u) (axW u) (axV t) (axW t) =
      axPhiK (axE2 u) (axV u) (axW u) (axL u) (axLS u) u (axE2 t) (axV t) (axW t) (axL t) t := by
  have hΔa := axDelta_ne_zero hu
  have hΔb := axDelta_ne_zero ht
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hJr : axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
      axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t) ≠ 0 := by
    intro h0
    apply hJ
    rw [kleinModularJ_imagPt_eq_ax hu, kleinModularJ_imagPt_eq_ax ht]
    exact congrArg ((↑) : ℝ → ℂ) (sub_eq_zero.mp h0)
  have hJeq : kleinModularJ (imagPt u) - kleinModularJ (imagPt t) =
      ((axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
        axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t) : ℝ) : ℂ) := by
    rw [kleinModularJ_imagPt_eq_ax hu, kleinModularJ_imagPt_eq_ax ht, ← ofReal_sub]
  have hK := ckmrvEight_algebra (ckmrvEightPlusContraction (imagPt u) (imagPt t))
    (ckmrvEightMinusContraction (imagPt u) (imagPt t)) (ModularForm.discriminant (imagPt t))
    (kleinModularJ (imagPt u) - kleinModularJ (imagPt t))
    (axPlusContr (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t)
    (axMinusContr (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t))
    (axDelta (axV t) (axW t)) _ (plusContraction_axis hu ht) (minusContraction_axis hu ht)
    (discriminant_imagPt_eq_ax ht) hJeq hΔb hJr
  rw [ckmrvEightKernel, ckmrvEightPlusKernel_eq_contraction,
    ckmrvEightMinusKernel_eq_contraction, ckmrvPlusScale, ckmrvMinusScale, hK, ofReal_re]
  have hplus := axDelta_mul_axPlusContr (E2a := axE2 u) (u := u) (E2b := axE2 t) hΔa hΔb ht.ne'
  have hminus := axDelta_mul_axMinusContr (La := axL u) (LSa := axLS u) (Lb := axL t)
    (Vb := axV t) (Wb := axW t) hΔa
  have hNu : axNu (axV u) (axW u) (axV t) (axW t) = axDelta (axV u) (axW u) *
      axDelta (axV t) (axW t) * (axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
        axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t)) := by
    simp only [axNu]
    field_simp
  have hN : axDelta (axV t) (axW t) * axE4 (axV u) (axW u) ^ 3 -
      axDelta (axV u) (axW u) * axE4 (axV t) (axW t) ^ 3 ≠ 0 := by
    have hEq : axDelta (axV t) (axW t) * axE4 (axV u) (axW u) ^ 3 -
        axDelta (axV u) (axW u) * axE4 (axV t) (axW t) ^ 3 =
          axDelta (axV u) (axW u) * axDelta (axV t) (axW t) *
            (axE4 (axV u) (axW u) ^ 3 / axDelta (axV u) (axW u) -
              axE4 (axV t) (axW t) ^ 3 / axDelta (axV t) (axW t)) := by
      field_simp
    rw [hEq]
    exact mul_ne_zero (mul_ne_zero hΔa hΔb) hJr
  rw [hNu]
  calc _ = π ^ 2 * (axDelta (axV u) (axW u) *
          axPlusContr (axE2 u) (axV u) (axW u) u (axE2 t) (axV t) (axW t) t) / 36 +
        (axDelta (axV u) (axW u) *
          axMinusContr (axV u) (axW u) (axL u) (axLS u) (axV t) (axW t) (axL t)) / (3456 * π) := by
        field_simp
    _ = _ := by
        rw [hplus, hminus]
        simp only [axPhiK]
        ring

end E8Leech
