import E8Leech.KronKernelExpr
import E8Leech.CKMRVAxisDerivatives

/-!
# The derivation of the second variable on expressions

Along the imaginary axis the generators satisfy a first-order polynomial system
(`CKMRVAxisDerivatives`). In terms of the eight atoms `x, θ₃, θ₄, η₁, E₂, Λ log θ₃, Λ log θ₄,
Λ log η₁` of the nome `x = e^{−πt}` and of `t̂ = 1/(πt)`, with `V = 16 x η₁⁴`, `W = θ₄⁴`:

`d/dt = −(π/12) ∂`,  `∂x = 12x`, `∂t̂ = 12 t̂²`, `∂θ₃ = θ₃ (E₂ + V − W)`, `∂θ₄ = θ₄ (E₂ − 2V − W)`,
`∂η₁ = η₁ (E₂ + V + 2W − 3)`, `∂E₂ = 2 (E₂² − E₄)`, and `∂(Λ log θ) = Λ ∂θ/θ`.

`IExpr.dz` is this derivation on expressions; `hasDerivAt_evalB` says that it computes the
derivative in `t` of the value of an expression, for nomes below `1/3`.

* `hasDerivAt_logTheta3`, `hasDerivAt_logTheta4`, `hasDerivAt_logEta1`: the logarithmic
  derivatives of the three series in `t`.
* `IExpr.dz`, `hasDerivAt_evalB`: the derivation and its meaning.
* `IExpr.hOf`, `hasDerivAt_sq_mul_evalB`, `hasDerivAt_sq_mul_evalB'`: the first and second
  derivatives of `π² t² · x`, the second being `(π⁴t²/144) · hOf x`.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real Topology

/-! ## The three series along the axis -/

section Series

variable {t : ℝ}

theorem nomeTheta3_pow_four (ht : 0 < t) :
    nomeTheta3 (Real.exp (-π * t)) ^ 4 = axV t + axW t := by
  have h1 := thetaU_imagPt_eq_nome ht
  rw [thetaU_imagPt_eq_ax ht] at h1
  exact (Complex.ofReal_injective h1).symm

/-- `(log (V + W))'/4` for the system of the generators. -/
theorem log_sum_deriv (V W E : ℝ) (hU : V + W ≠ 0) :
    (-(π / 3) * (V * (E + V + 2 * W)) + -(π / 3) * (W * (E - 2 * V - W))) / (V + W) / 4 =
      -(π / 12) * (E + V - W) := by
  rw [div_div, div_eq_iff (mul_ne_zero hU (by norm_num))]
  ring

/-- `(log W)'/4` for the system of the generators. -/
theorem log_w_deriv (V W E : ℝ) (hW : W ≠ 0) :
    -(π / 3) * (W * (E - 2 * V - W)) / W / 4 = -(π / 12) * (E - 2 * V - W) := by
  rw [div_div, div_eq_iff (mul_ne_zero hW (by norm_num))]
  ring

/-- `d/dt log θ₃ = −(π/12)(E₂ + V − W)`. -/
theorem hasDerivAt_logTheta3 (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (nomeTheta3 (Real.exp (-π * s))))
      (-(π / 12) * (axE2 t + axV t - axW t)) t := by
  have hV := hasDerivAt_axV ht
  have hW := hasDerivAt_axW ht
  have hU : 0 < axV t + axW t := add_pos (axV_pos ht) (axW_pos ht)
  have hUd : HasDerivAt (fun s => axV s + axW s)
      (-(π / 3) * (axV t * (axE2 t + axV t + 2 * axW t)) +
        -(π / 3) * (axW t * (axE2 t - 2 * axV t - axW t))) t := hV.add hW
  have h := (hUd.log hU.ne').div_const 4
  have hev : (fun s => Real.log (nomeTheta3 (Real.exp (-π * s)))) =ᶠ[𝓝 t]
      fun s => Real.log (axV s + axW s) / 4 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [← nomeTheta3_pow_four hs', Real.log_pow]
    push_cast
    ring
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  exact log_sum_deriv _ _ _ hU.ne'

/-- `d/dt log θ₄ = −(π/12)(E₂ − 2V − W)`. -/
theorem hasDerivAt_logTheta4 (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (nomeTheta4 (Real.exp (-π * s))))
      (-(π / 12) * (axE2 t - 2 * axV t - axW t)) t := by
  have hW := hasDerivAt_axW ht
  have hWp := axW_pos ht
  have h := (hW.log hWp.ne').div_const 4
  have hev : (fun s => Real.log (nomeTheta4 (Real.exp (-π * s)))) =ᶠ[𝓝 t]
      fun s => Real.log (axW s) / 4 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [axW_eq_nome hs', Real.log_pow]
    push_cast
    ring
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  exact log_w_deriv _ _ _ hWp.ne'

/-- `d/dt log η₁ = −(π/12)(E₂ + V + 2W − 3)`. -/
theorem hasDerivAt_logEta1 (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (nomeEta1 (Real.exp (-π * s))))
      (-(π / 12) * (axE2 t + axV t + 2 * axW t - 3)) t := by
  have hL := hasDerivAt_axL ht
  have h3 := hasDerivAt_logTheta3 ht
  have hid : HasDerivAt (fun s : ℝ => π * s) π t := by
    simpa using (hasDerivAt_id t).const_mul π
  have h := (((hL.sub_const (4 * Real.log 2)).add hid).add (h3.const_mul 4)).div_const 4
  have hev : (fun s => Real.log (nomeEta1 (Real.exp (-π * s)))) =ᶠ[𝓝 t]
      fun s => (axL s - 4 * Real.log 2 + π * s +
        4 * Real.log (nomeTheta3 (Real.exp (-π * s)))) / 4 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : (0 : ℝ) < s := hs
    rw [axL_eq_nome hs']
    ring
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

theorem exp_neg_pi_mul_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-π * s)) (-π * Real.exp (-π * t)) t := by
  have h : HasDerivAt (fun s : ℝ => -π * s) (-π) t := by
    simpa using (hasDerivAt_id t).const_mul (-π)
  exact h.exp.congr_deriv (mul_comm _ _)

/-- `d/dt θ₃ = −(π/12) θ₃ (E₂ + V − W)`. -/
theorem hasDerivAt_theta3 (ht : 0 < t) :
    HasDerivAt (fun s => nomeTheta3 (Real.exp (-π * s)))
      (-(π / 12) * (nomeTheta3 (Real.exp (-π * t)) * (axE2 t + axV t - axW t))) t := by
  have h := (hasDerivAt_logTheta3 ht).exp
  have hpos : ∀ s : ℝ, 0 < nomeTheta3 (Real.exp (-π * s)) := fun s =>
    lt_of_lt_of_le one_pos (one_le_nomeTheta3 (Real.exp_pos _).le)
  have hfun : (fun s => nomeTheta3 (Real.exp (-π * s))) =
      fun s => Real.exp (Real.log (nomeTheta3 (Real.exp (-π * s)))) :=
    funext fun s => (Real.exp_log (hpos s)).symm
  rw [hfun]
  refine h.congr_deriv ?_
  rw [Real.exp_log (hpos t)]
  ring

/-- `d/dt θ₄ = −(π/12) θ₄ (E₂ − 2V − W)`, for nomes below `1/3`. -/
theorem hasDerivAt_theta4 (ht : 0 < t) (hx : Real.exp (-π * t) < 1 / 3) :
    HasDerivAt (fun s => nomeTheta4 (Real.exp (-π * s)))
      (-(π / 12) * (nomeTheta4 (Real.exp (-π * t)) * (axE2 t - 2 * axV t - axW t))) t := by
  have h := (hasDerivAt_logTheta4 ht).exp
  have hcont : ContinuousAt (fun s : ℝ => Real.exp (-π * s)) t :=
    (exp_neg_pi_mul_hasDerivAt t).continuousAt
  have hev : (fun s => nomeTheta4 (Real.exp (-π * s))) =ᶠ[𝓝 t]
      fun s => Real.exp (Real.log (nomeTheta4 (Real.exp (-π * s)))) := by
    filter_upwards [hcont.tendsto.eventually (gt_mem_nhds hx)] with s hs
    exact (Real.exp_log (nomeTheta4_pos (Real.exp_pos _).le hs)).symm
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [Real.exp_log (nomeTheta4_pos (Real.exp_pos _).le hx)]
  ring

/-- `d/dt η₁ = −(π/12) η₁ (E₂ + V + 2W − 3)`. -/
theorem hasDerivAt_eta1 (ht : 0 < t) :
    HasDerivAt (fun s => nomeEta1 (Real.exp (-π * s)))
      (-(π / 12) * (nomeEta1 (Real.exp (-π * t)) * (axE2 t + axV t + 2 * axW t - 3))) t := by
  have h := (hasDerivAt_logEta1 ht).exp
  have hpos : ∀ s : ℝ, 0 < s → 0 < nomeEta1 (Real.exp (-π * s)) := fun s hs => by
    obtain ⟨hx0, hx1⟩ := exp_neg_pi_mem hs
    exact nomeEta1_pos hx0 hx1
  have hev : (fun s => nomeEta1 (Real.exp (-π * s))) =ᶠ[𝓝 t]
      fun s => Real.exp (Real.log (nomeEta1 (Real.exp (-π * s)))) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (Real.exp_log (hpos s hs)).symm
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [Real.exp_log (hpos t ht)]
  ring

/-- `d/dt E₂ = −(π/12) · 2 (E₂² − E₄)` in the nome. -/
theorem hasDerivAt_nomeE2 (ht : 0 < t) :
    HasDerivAt (fun s => nomeE2 (Real.exp (-π * s)))
      (-(π / 12) * (2 * (axE2 t ^ 2 - axE4 (axV t) (axW t)))) t := by
  have h := hasDerivAt_axE2 ht
  have hev : (fun s => nomeE2 (Real.exp (-π * s))) =ᶠ[𝓝 t] axE2 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : (0 : ℝ) < s := hs
    exact (axE2_eq_nome hs').symm
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

end Series

/-! ## Powers of functions with a logarithmic derivative -/

theorem hasDerivAt_pow_of_log {f : ℝ → ℝ} {c t : ℝ} (hf : HasDerivAt f (c * f t) t) (n : ℕ) :
    HasDerivAt (fun s => f s ^ n) (n * c * f t ^ n) t := by
  induction n with
  | zero => simpa using hasDerivAt_const t (1 : ℝ)
  | succ n ih =>
    have h := ih.mul hf
    have hfun : (fun s => f s ^ (n + 1)) = (fun s => f s ^ n) * f := by
      funext s
      exact pow_succ (f s) n
    rw [hfun]
    refine h.congr_deriv ?_
    push_cast
    ring

theorem hasDerivAt_recip (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => 1 / (π * s)) (-π * (1 / (π * t)) * (1 / (π * t))) t := by
  have hπ := Real.pi_pos
  have h : HasDerivAt (fun s : ℝ => π * s) π t := by
    simpa using (hasDerivAt_id t).const_mul π
  have h2 := h.inv (mul_pos hπ ht).ne'
  have hfun : (fun s : ℝ => 1 / (π * s)) = fun s => (π * s)⁻¹ := funext fun s => one_div _
  rw [hfun]
  refine h2.congr_deriv ?_
  have hne : π * t ≠ 0 := (mul_pos hπ ht).ne'
  have hq : (1 : ℝ) / (π * t) * (π * t) = 1 := one_div_mul_cancel hne
  rw [div_eq_iff (pow_ne_zero 2 hne)]
  linear_combination (π * (1 / (π * t) * (π * t) + 1)) * hq

theorem hasDerivAt_sq (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
  simpa using hasDerivAt_pow 2 t

/-! ## The derivation -/

section Atoms

variable (Λ : ℕ) (ex : List (ℝ → ℝ))

@[simp] theorem evalB_zat1 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 1) e = genFun 1 e.b := rfl
@[simp] theorem evalB_zat6 (e : NEnv) :
    IExpr.evalB (kernelAtoms Λ ++ ex) (.zat 6) e = Λ * logFun 1 e.b := rfl

end Atoms

namespace IExpr

/-- The derivation of the second variable: `d/dt = −(π/12) dz` along the imaginary axis. -/
def dz (Λ : ℕ) : IExpr → IExpr
  | .zat 0 => 12 * .zat 0
  | .zat 1 => .zat 1 * (.zat 4 + vZ - wZ)
  | .zat 2 => .zat 2 * (.zat 4 - 2 * vZ - wZ)
  | .zat 3 => .zat 3 * (.zat 4 + vZ + 2 * wZ - 3)
  | .zat 4 => 2 * ((.zat 4) ^ 2 - e4E vZ wZ)
  | .zat 5 => .cst Λ * (.zat 4 + vZ - wZ)
  | .zat 6 => .cst Λ * (.zat 4 - 2 * vZ - wZ)
  | .zat 7 => .cst Λ * (.zat 4 + vZ + 2 * wZ - 3)
  | .zat _ => .cst 0
  | .tat _ => .cst 0
  | .cst _ => .cst 0
  | .mono m => .cst (12 * m.eb) * .mono m + .cst (12 * m.et) * (.mono m * thE)
  | .add x y => .add (dz Λ x) (dz Λ y)
  | .sub x y => .sub (dz Λ x) (dz Λ y)
  | .mul x y => .add (.mul (dz Λ x) y) (.mul x (dz Λ y))

/-- The expression of the second derivative of `π² t² · x`, up to the factor `π⁴ t²/144`:
`∂²x − 48 t̂ ∂x + 288 t̂² x`. -/
def hOf (Λ : ℕ) (x : IExpr) : IExpr :=
  dz Λ (dz Λ x) - 48 * thE * dz Λ x + 288 * thE ^ 2 * x

end IExpr

theorem hasDerivAt_mono (u : ℝ) {t : ℝ} (ht : 0 < t) (m : NMono) :
    HasDerivAt (fun s => m.eval (axisNEnv u s))
      (-(π / 12) * (12 * m.eb * m.eval (axisNEnv u t) +
        12 * m.et * (m.eval (axisNEnv u t) * (axisNEnv u t).t))) t := by
  have hb := hasDerivAt_pow_of_log (f := fun s : ℝ => Real.exp (-π * s)) (c := -π)
    (exp_neg_pi_mul_hasDerivAt t) m.eb
  have hth := hasDerivAt_pow_of_log (f := fun s : ℝ => 1 / (π * s)) (c := -π * (1 / (π * t)))
    (hasDerivAt_recip t ht) m.et
  have h := ((((hasDerivAt_const t (Real.exp (-π * u) ^ m.ea)).mul hb).mul
    (hasDerivAt_const t ((1 / (π * u)) ^ m.eu))).mul hth).mul
    (hasDerivAt_const t (Real.log 2 ^ m.el))
  refine h.congr_deriv ?_
  simp only [NMono.eval, axisNEnv, Pi.mul_apply]
  ring

/-- **The derivation computes the derivative in `t`**, for nomes below `1/3`. -/
theorem hasDerivAt_evalB (Λ : ℕ) (u : ℝ) {t : ℝ} (ht : 0 < t) (hx : Real.exp (-π * t) < 1 / 3)
    (x : IExpr) :
    HasDerivAt (fun s => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u s))
      (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t)) t := by
  have eb : (axisNEnv u t).b = Real.exp (-π * t) := rfl
  have hE2 : nomeE2 (Real.exp (-π * t)) = axE2 t := (axE2_eq_nome ht).symm
  have hV : nomeV (Real.exp (-π * t)) = axV t := by
    rw [axV_eq_nome ht]
    rfl
  have hW : nomeW (Real.exp (-π * t)) = axW t := by
    rw [axW_eq_nome ht]
    rfl
  induction x with
  | zat i =>
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · -- the nome
      show HasDerivAt (fun s : ℝ => Real.exp (-π * s))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (12 * .zat 0) (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_nat, evalB_zat0]
      refine (exp_neg_pi_mul_hasDerivAt t).congr_deriv ?_
      show -π * Real.exp (-π * t) = -(π / 12) * (((12 : ℕ) : ℝ) * Real.exp (-π * t))
      push_cast
      ring
    · -- `θ₃`
      show HasDerivAt (fun s : ℝ => nomeTheta3 (Real.exp (-π * s)))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.zat 1 * (.zat 4 + vZ - wZ))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_sub, IExpr.evalB_add, evalB_zat1, evalB_zat4, evalB_vZ,
        evalB_wZ, eb]
      refine (hasDerivAt_theta3 ht).congr_deriv ?_
      show _ = -(π / 12) * (nomeTheta3 (Real.exp (-π * t)) *
        (nomeE2 (Real.exp (-π * t)) + nomeV (Real.exp (-π * t)) - nomeW (Real.exp (-π * t))))
      rw [hE2, hV, hW]
    · -- `θ₄`
      show HasDerivAt (fun s : ℝ => nomeTheta4 (Real.exp (-π * s)))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.zat 2 * (.zat 4 - 2 * vZ - wZ))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_sub, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat,
        evalB_zat2, evalB_zat4, evalB_vZ, evalB_wZ, eb]
      refine (hasDerivAt_theta4 ht hx).congr_deriv ?_
      show _ = -(π / 12) * (nomeTheta4 (Real.exp (-π * t)) *
        (nomeE2 (Real.exp (-π * t)) - ((2 : ℕ) : ℝ) * nomeV (Real.exp (-π * t)) -
          nomeW (Real.exp (-π * t))))
      rw [hE2, hV, hW]
      push_cast
      ring
    · -- `η₁`
      show HasDerivAt (fun s : ℝ => nomeEta1 (Real.exp (-π * s)))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.zat 3 * (.zat 4 + vZ + 2 * wZ - 3))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_sub, IExpr.evalB_add, IExpr.evalB_add, IExpr.evalB_mul,
        IExpr.evalB_nat, IExpr.evalB_nat, evalB_zat3, evalB_zat4, evalB_vZ, evalB_wZ, eb]
      refine (hasDerivAt_eta1 ht).congr_deriv ?_
      show _ = -(π / 12) * (nomeEta1 (Real.exp (-π * t)) *
        (nomeE2 (Real.exp (-π * t)) + nomeV (Real.exp (-π * t)) +
          ((2 : ℕ) : ℝ) * nomeW (Real.exp (-π * t)) - ((3 : ℕ) : ℝ)))
      rw [hE2, hV, hW]
      push_cast
      ring
    · -- `E₂`
      show HasDerivAt (fun s : ℝ => nomeE2 (Real.exp (-π * s)))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (2 * ((.zat 4) ^ 2 - e4E vZ wZ))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_nat, IExpr.evalB_sub, IExpr.evalB_pow, evalB_e4E,
        evalB_zat4, evalB_vZ, evalB_wZ, eb]
      refine (hasDerivAt_nomeE2 ht).congr_deriv ?_
      show _ = -(π / 12) * (((2 : ℕ) : ℝ) * (nomeE2 (Real.exp (-π * t)) ^ 2 -
        axE4 (nomeV (Real.exp (-π * t))) (nomeW (Real.exp (-π * t)))))
      rw [hE2, hV, hW]
      push_cast
      ring
    · -- `Λ log θ₃`
      show HasDerivAt (fun s : ℝ => (Λ : ℝ) * Real.log (nomeTheta3 (Real.exp (-π * s))))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.cst Λ * (.zat 4 + vZ - wZ))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_sub, IExpr.evalB_add, IExpr.evalB_cst, evalB_zat4,
        evalB_vZ, evalB_wZ, eb]
      refine ((hasDerivAt_logTheta3 ht).const_mul (Λ : ℝ)).congr_deriv ?_
      show _ = -(π / 12) * ((((Λ : ℕ) : ℤ) : ℝ) *
        (nomeE2 (Real.exp (-π * t)) + nomeV (Real.exp (-π * t)) - nomeW (Real.exp (-π * t))))
      rw [hE2, hV, hW]
      push_cast
      ring
    · -- `Λ log θ₄`
      show HasDerivAt (fun s : ℝ => (Λ : ℝ) * Real.log (nomeTheta4 (Real.exp (-π * s))))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.cst Λ * (.zat 4 - 2 * vZ - wZ))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_sub, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_nat,
        IExpr.evalB_cst, evalB_zat4, evalB_vZ, evalB_wZ, eb]
      refine ((hasDerivAt_logTheta4 ht).const_mul (Λ : ℝ)).congr_deriv ?_
      show _ = -(π / 12) * ((((Λ : ℕ) : ℤ) : ℝ) *
        (nomeE2 (Real.exp (-π * t)) - ((2 : ℕ) : ℝ) * nomeV (Real.exp (-π * t)) -
          nomeW (Real.exp (-π * t))))
      rw [hE2, hV, hW]
      push_cast
      ring
    · -- `Λ log η₁`
      show HasDerivAt (fun s : ℝ => (Λ : ℝ) * Real.log (nomeEta1 (Real.exp (-π * s))))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.cst Λ * (.zat 4 + vZ + 2 * wZ - 3))
          (axisNEnv u t)) t
      rw [IExpr.evalB_mul, IExpr.evalB_sub, IExpr.evalB_add, IExpr.evalB_add, IExpr.evalB_mul,
        IExpr.evalB_nat, IExpr.evalB_nat, IExpr.evalB_cst, evalB_zat4, evalB_vZ, evalB_wZ, eb]
      refine ((hasDerivAt_logEta1 ht).const_mul (Λ : ℝ)).congr_deriv ?_
      show _ = -(π / 12) * ((((Λ : ℕ) : ℤ) : ℝ) *
        (nomeE2 (Real.exp (-π * t)) + nomeV (Real.exp (-π * t)) +
          ((2 : ℕ) : ℝ) * nomeW (Real.exp (-π * t)) - ((3 : ℕ) : ℝ)))
      rw [hE2, hV, hW]
      push_cast
      ring
    · -- no further atoms
      show HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.cst 0) (axisNEnv u t)) t
      rw [IExpr.evalB_cst, Int.cast_zero, mul_zero]
      exact hasDerivAt_const t 0
  | tat i =>
    show HasDerivAt (fun _ : ℝ => IExpr.evalB (kernelAtoms Λ ++ []) (.tat i) (axisNEnv u t))
      (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.cst 0) (axisNEnv u t)) t
    rw [IExpr.evalB_cst, Int.cast_zero, mul_zero]
    exact hasDerivAt_const t _
  | cst c =>
    show HasDerivAt (fun _ : ℝ => (c : ℝ))
      (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (.cst 0) (axisNEnv u t)) t
    rw [IExpr.evalB_cst, Int.cast_zero, mul_zero]
    exact hasDerivAt_const t _
  | mono m =>
    show HasDerivAt (fun s : ℝ => m.eval (axisNEnv u s))
      (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ [])
        (.cst (12 * m.eb) * .mono m + .cst (12 * m.et) * (.mono m * thE)) (axisNEnv u t)) t
    rw [IExpr.evalB_add, IExpr.evalB_mul, IExpr.evalB_mul, IExpr.evalB_mul, IExpr.evalB_cst,
      IExpr.evalB_cst, IExpr.evalB_mono, evalB_thE]
    refine (hasDerivAt_mono u ht m).congr_deriv ?_
    push_cast
    ring
  | add x y ihx ihy =>
    refine (ihx.add ihy).congr_deriv ?_
    show -(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) +
        -(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ y) (axisNEnv u t) =
      -(π / 12) * (IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) +
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ y) (axisNEnv u t))
    ring
  | sub x y ihx ihy =>
    refine (ihx.sub ihy).congr_deriv ?_
    show -(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) -
        -(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ y) (axisNEnv u t) =
      -(π / 12) * (IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) -
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ y) (axisNEnv u t))
    ring
  | mul x y ihx ihy =>
    refine (ihx.mul ihy).congr_deriv ?_
    show -(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) *
          IExpr.evalB (kernelAtoms Λ ++ []) y (axisNEnv u t) +
        IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u t) *
          (-(π / 12) * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ y) (axisNEnv u t)) =
      -(π / 12) * (IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) *
          IExpr.evalB (kernelAtoms Λ ++ []) y (axisNEnv u t) +
        IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u t) *
          IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ y) (axisNEnv u t))
    ring

/-- The derivative of `π² t² · x`. -/
theorem hasDerivAt_sq_mul_evalB (Λ : ℕ) (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hx : Real.exp (-π * t) < 1 / 3) (x : IExpr) :
    HasDerivAt (fun s => π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u s))
      (2 * π ^ 2 * t * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u t) -
        π ^ 3 * t ^ 2 / 12 *
          IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t)) t := by
  have h0 := hasDerivAt_evalB Λ u ht hx x
  have hq : HasDerivAt (fun s : ℝ => π ^ 2 * s ^ 2) (π ^ 2 * (2 * t)) t :=
    (hasDerivAt_sq t).const_mul (π ^ 2)
  refine (hq.mul h0).congr_deriv ?_
  ring

/-- **The second derivative of `π² t² · x` is `(π⁴ t²/144) · hOf x`.** -/
theorem hasDerivAt_sq_mul_evalB' (Λ : ℕ) (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hx : Real.exp (-π * t) < 1 / 3) (x : IExpr) :
    HasDerivAt
      (fun s => 2 * π ^ 2 * s * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u s) -
        π ^ 3 * s ^ 2 / 12 * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u s))
      (π ^ 4 * t ^ 2 / 144 *
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv u t)) t := by
  have hπ := Real.pi_pos
  have h0 := hasDerivAt_evalB Λ u ht hx x
  have h1 := hasDerivAt_evalB Λ u ht hx (IExpr.dz Λ x)
  have ha : HasDerivAt (fun s : ℝ => 2 * π ^ 2 * s) (2 * π ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π ^ 2)
  have hb : HasDerivAt (fun s : ℝ => π ^ 3 * s ^ 2 / 12) (π ^ 3 * (2 * t) / 12) t :=
    ((hasDerivAt_sq t).const_mul (π ^ 3)).div_const 12
  have et : (axisNEnv u t).t = 1 / (π * t) := rfl
  refine ((ha.mul h0).sub (hb.mul h1)).congr_deriv ?_
  rw [IExpr.hOf, IExpr.evalB_add, IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_mul,
    IExpr.evalB_mul, IExpr.evalB_mul, IExpr.evalB_pow, IExpr.evalB_nat, IExpr.evalB_nat,
    evalB_thE, et]
  have hne : π * t ≠ 0 := (mul_pos hπ ht).ne'
  have hr : (1 : ℝ) / (π * t) * (π * t) = 1 := one_div_mul_cancel hne
  push_cast
  generalize IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u t) = X
  generalize IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u t) = Y
  generalize IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ (IExpr.dz Λ x)) (axisNEnv u t) = Z
  linear_combination
    (-(2 * π ^ 2 * X * (1 + π * t * (1 / (π * t))) - π ^ 3 * t / 3 * Y)) * hr

end E8Leech.Kron
