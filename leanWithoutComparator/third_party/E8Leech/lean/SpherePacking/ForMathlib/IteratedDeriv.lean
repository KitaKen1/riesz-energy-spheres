-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import SpherePacking.ForMathlib.DerivHelpers


/-!
# Iterated derivative helpers

This file collects small lemmas about `iteratedDeriv` and `iteratedFDeriv` that are duplicated
across the project.
-/

namespace SpherePacking.ForMathlib

open scoped Topology
open Filter

/-- If `I (n+1)` is the derivative of `I n` at every point, then the `n`-th iterated derivative of
`I 0` is `I n`. -/
public lemma iteratedDeriv_eq_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => I 0 x) = fun x : ℝ => I n x := by
  induction n with
  | zero => ext x; simp [iteratedDeriv_zero]
  | succ n ih => ext x; simpa [iteratedDeriv_succ, ih] using (hI n x).deriv

/-- Under the same recurrence hypothesis as `iteratedDeriv_eq_of_hasDerivAt_succ`, the iterated
derivative is differentiable. -/
public lemma differentiable_iteratedDeriv_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x) (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n (fun x : ℝ => I 0 x)) := by
  rw [iteratedDeriv_eq_of_hasDerivAt_succ (I := I) hI n]
  exact fun x => (hI n x).differentiableAt

/-- If `I (n+1)` is the derivative of `I n` at every point, then `I 0` is smooth. -/
public theorem contDiff_of_hasDerivAt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ℕ → ℝ → E)
    (hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => I 0 x) :=
  contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞))
    fun m _ => differentiable_iteratedDeriv_of_hasDerivAt_succ (I := I) hI m

/-- If `deriv (G n) = G (n+1)` holds on an open set, then iterated derivatives of `G m` agree with
`G (n+m)` on that set. -/
public lemma eqOn_iteratedDeriv_eq_of_deriv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (hs : IsOpen s) (G : ℕ → ℝ → E)
    (hderiv : ∀ n x, x ∈ s → deriv (G n) x = G (n + 1) x) :
    ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  intro n
  induction n with
  | zero =>
      intro m x hx
      simp [iteratedDeriv_zero]
  | succ n ih =>
      intro m x hx
      have hEq : iteratedDeriv n (G m) =ᶠ[𝓝 x] G (n + m) := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact ih (m := m) (x := y) hy
      simpa [iteratedDeriv_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Filter.EventuallyEq.deriv_eq hEq).trans (hderiv (n + m) x hx)

/-- Closed form for iterated derivatives of `x ↦ exp (x * c)`. -/
public lemma iteratedDeriv_cexp_mul_const (c : ℂ) :
    ∀ m : ℕ,
      iteratedDeriv m (fun x : ℝ ↦ Complex.exp ((x : ℂ) * c)) =
        fun x : ℝ ↦ c ^ m * Complex.exp ((x : ℂ) * c) := by
  intro m
  induction m with
  | zero =>
      funext x
      simp [iteratedDeriv_zero]
  | succ m ih =>
      funext x
      simpa [iteratedDeriv_succ, ih, mul_assoc] using
        (hasDerivAt_pow_mul_mul_cexp_ofReal_mul_const (a := (1 : ℂ)) (c := c) (n := m) x).deriv

/-- Bound the norm of `m`-th iterated derivative of `t ↦ exp (t * π i)` by `π ^ m`. -/
public lemma norm_iteratedFDeriv_cexp_mul_pi_I_le (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x‖ ≤
      Real.pi ^ m := by
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  have hnorm_exp : ‖Complex.exp ((x : ℂ) * c)‖ = 1 := by
    have : ((x : ℂ) * c).re = 0 := by simp [c, mul_left_comm, mul_comm]
    simp [Complex.norm_exp, this]
  have hEq :
      ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * c)) x‖ = Real.pi ^ m := by
    calc
      ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * c)) x‖ =
          ‖iteratedDeriv m (fun t : ℝ ↦ Complex.exp ((t : ℂ) * c)) x‖ :=
            norm_iteratedFDeriv_eq_norm_iteratedDeriv
      _ = ‖c ^ m * Complex.exp ((x : ℂ) * c)‖ := by
            simpa using congrArg (fun F : ℝ → ℂ => ‖F x‖) (iteratedDeriv_cexp_mul_const (c := c) m)
      _ = ‖c ^ m‖ * ‖Complex.exp ((x : ℂ) * c)‖ := by simp
      _ = Real.pi ^ m := by simp [norm_pow, c, abs_of_nonneg Real.pi_pos.le, hnorm_exp]
  simpa [c] using hEq.le

/-- Bound the norm of the `m`-th iterated derivative of `(-1/2) • exp (t * π i)`. -/
public lemma norm_iteratedFDeriv_smul_cexp_mul_pi_I_le (m : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m
        (fun t : ℝ ↦ (-1 / 2 : ℂ) • Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))) x‖ ≤
      (1 / 2 : ℝ) * Real.pi ^ m := by
  let e : ℝ → ℂ := fun t ↦ Complex.exp ((t : ℂ) * ((Real.pi : ℂ) * Complex.I))
  have hiter : ‖iteratedFDeriv ℝ m e x‖ ≤ Real.pi ^ m := by
    simpa [e] using norm_iteratedFDeriv_cexp_mul_pi_I_le (m := m) (x := x)
  have hsmul :
      ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ (-1 / 2 : ℂ) • e t) x‖ =
        ‖(-1 / 2 : ℂ)‖ * ‖iteratedFDeriv ℝ m e x‖ := by
    calc
      ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ (-1 / 2 : ℂ) • e t) x‖ =
          ‖iteratedDeriv m (fun t : ℝ ↦ (-1 / 2 : ℂ) • e t) x‖ :=
            norm_iteratedFDeriv_eq_norm_iteratedDeriv
      _ = ‖(-1 / 2 : ℂ) • iteratedDeriv m e x‖ := by
            simp
      _ = ‖(-1 / 2 : ℂ)‖ * ‖iteratedDeriv m e x‖ := by simp
      _ = ‖(-1 / 2 : ℂ)‖ * ‖iteratedFDeriv ℝ m e x‖ := by
            simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := m) (f := e) (x := x)]
  calc
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ (-1 / 2 : ℂ) • e t) x‖ =
        ‖(-1 / 2 : ℂ)‖ * ‖iteratedFDeriv ℝ m e x‖ := hsmul
    _ ≤ ‖(-1 / 2 : ℂ)‖ * Real.pi ^ m := by gcongr
    _ = (1 / 2 : ℝ) * Real.pi ^ m := by simp

/-- `iteratedFDeriv` of a sum of six terms splits as the sum of the `iteratedFDeriv`'s.

The prime in the name indicates this lemma takes `ContDiffAt` hypotheses to use
`iteratedFDeriv_add_apply'` repeatedly.
-/
public lemma iteratedFDeriv_add₆_apply'
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℂ} (n : ℕ) (x : ℝ)
    (hf₁ : ContDiffAt ℝ n f₁ x) (hf₂ : ContDiffAt ℝ n f₂ x) (hf₃ : ContDiffAt ℝ n f₃ x)
    (hf₄ : ContDiffAt ℝ n f₄ x) (hf₅ : ContDiffAt ℝ n f₅ x) (hf₆ : ContDiffAt ℝ n f₆ x) :
    iteratedFDeriv ℝ n (fun u : ℝ ↦ (((((f₁ u + f₂ u) + f₃ u) + f₄ u) + f₅ u) + f₆ u)) x =
      (((((iteratedFDeriv ℝ n f₁ x + iteratedFDeriv ℝ n f₂ x) + iteratedFDeriv ℝ n f₃ x) +
            iteratedFDeriv ℝ n f₄ x) +
          iteratedFDeriv ℝ n f₅ x) +
        iteratedFDeriv ℝ n f₆ x) := by
  have h12 := hf₁.add hf₂
  have h123 := h12.add hf₃
  have h1234 := h123.add hf₄
  have h12345 := h1234.add hf₅
  simp [fun_iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := x) h12345 hf₆,
    fun_iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := x) h1234 hf₅,
    fun_iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := x) h123 hf₄,
    fun_iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := x) h12 hf₃,
    fun_iteratedFDeriv_add_apply (𝕜 := ℝ) (i := n) (x := x) hf₁ hf₂]

/-- Triangle inequality for the norm of the `iteratedFDeriv` of a sum of six terms. -/
public lemma norm_iteratedFDeriv_add₆_le
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℂ} (n : ℕ) (x : ℝ)
    (hf₁ : ContDiffAt ℝ n f₁ x) (hf₂ : ContDiffAt ℝ n f₂ x) (hf₃ : ContDiffAt ℝ n f₃ x)
    (hf₄ : ContDiffAt ℝ n f₄ x) (hf₅ : ContDiffAt ℝ n f₅ x) (hf₆ : ContDiffAt ℝ n f₆ x) :
    ‖iteratedFDeriv ℝ n (fun u : ℝ ↦ (((((f₁ u + f₂ u) + f₃ u) + f₄ u) + f₅ u) + f₆ u)) x‖ ≤
      ‖iteratedFDeriv ℝ n f₁ x‖ + ‖iteratedFDeriv ℝ n f₂ x‖ + ‖iteratedFDeriv ℝ n f₃ x‖ +
        ‖iteratedFDeriv ℝ n f₄ x‖ + ‖iteratedFDeriv ℝ n f₅ x‖ + ‖iteratedFDeriv ℝ n f₆ x‖ := by
  simpa [iteratedFDeriv_add₆_apply' (n := n) (x := x) hf₁ hf₂ hf₃ hf₄ hf₅ hf₆] using
    (norm_add₆_le (iteratedFDeriv ℝ n f₁ x) (iteratedFDeriv ℝ n f₂ x) (iteratedFDeriv ℝ n f₃ x)
      (iteratedFDeriv ℝ n f₄ x) (iteratedFDeriv ℝ n f₅ x) (iteratedFDeriv ℝ n f₆ x))

/-- Combine decay estimates for six terms into a decay estimate for their sum. -/
public lemma decay_iteratedFDeriv_add₆_of_decay
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℂ} (k n : ℕ) (C₁ C₂ C₃ C₄ C₅ C₆ : ℝ)
    (hdec₁ : ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f₁ x‖ ≤ C₁)
    (hdec₂ : ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f₂ x‖ ≤ C₂)
    (hdec₃ : ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f₃ x‖ ≤ C₃)
    (hdec₄ : ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f₄ x‖ ≤ C₄)
    (hdec₅ : ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f₅ x‖ ≤ C₅)
    (hdec₆ : ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f₆ x‖ ≤ C₆)
    (x : ℝ) (hx : 0 ≤ x)
    (hf₁ : ContDiffAt ℝ n f₁ x) (hf₂ : ContDiffAt ℝ n f₂ x) (hf₃ : ContDiffAt ℝ n f₃ x)
    (hf₄ : ContDiffAt ℝ n f₄ x) (hf₅ : ContDiffAt ℝ n f₅ x) (hf₆ : ContDiffAt ℝ n f₆ x) :
    ‖x‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun u : ℝ ↦ (((((f₁ u + f₂ u) + f₃ u) + f₄ u) + f₅ u) + f₆ u)) x‖ ≤
        C₁ + C₂ + C₃ + C₄ + C₅ + C₆ := by
  let F : ℝ → ℂ := fun u ↦ (((((f₁ u + f₂ u) + f₃ u) + f₄ u) + f₅ u) + f₆ u)
  simpa [F] using
    (mul_le_add₆_of_le_add₆ (x := ‖x‖ ^ k) (a := ‖iteratedFDeriv ℝ n F x‖) (by positivity)
      (by simpa [F] using norm_iteratedFDeriv_add₆_le (n := n) (x := x) hf₁ hf₂ hf₃ hf₄ hf₅ hf₆)
      (hdec₁ x hx) (hdec₂ x hx) (hdec₃ x hx) (hdec₄ x hx) (hdec₅ x hx) (hdec₆ x hx))

/-- `ContDiffOn` for a nested sum, when the rightmost term is only `ContDiffOn`. -/
public lemma contDiffOn_add₆_right_of_contDiff
    {f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℂ} {s : Set ℝ}
    (hf₁ : ContDiff ℝ (⊤ : ℕ∞) f₁) (hf₂ : ContDiff ℝ (⊤ : ℕ∞) f₂) (hf₃ : ContDiff ℝ (⊤ : ℕ∞) f₃)
    (hf₄ : ContDiff ℝ (⊤ : ℕ∞) f₄) (hf₅ : ContDiff ℝ (⊤ : ℕ∞) f₅)
    (hf₆ : ContDiffOn ℝ (⊤ : ℕ∞) f₆ s) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ ↦ f₁ y + (f₂ y + (f₃ y + (f₄ y + (f₅ y + f₆ y))))) s := by
  simpa [add_assoc] using (((((hf₁.add hf₂).add hf₃).add hf₄).add hf₅).contDiffOn.add hf₆)

/-- If `f` has bounded derivatives and `g` has one-sided decay of all derivatives, then the product
`f * g` has one-sided decay for a fixed iterated derivative order. -/
public theorem decay_iteratedFDeriv_mul_of_bound_left
    {f g : ℝ → ℂ} (k n : ℕ) (B : ℕ → ℝ)
    (hf_cont : ContDiff ℝ (⊤ : ℕ∞) f) (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g)
    (hbound_f : ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m f x‖ ≤ B m)
    (hdec_g :
      ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖ ≤ C) :
    ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖ ≤ C := by
  let Cg : ℕ → ℝ := fun m ↦ Classical.choose (hdec_g m)
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Cg (n - i)
  refine ⟨C, ?_⟩
  intro x hx
  have hxk0 : 0 ≤ ‖x‖ ^ k := by positivity
  have hmul :
      ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
    norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞)) hf_cont hg_cont x (n := n)
      (hn :=
        WithTop.coe_le_coe.2 (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  have hmain :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hmul hxk0
  have hterm :
      ∀ i ∈ Finset.range (n + 1),
        ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
          (n.choose i : ℝ) * B i * Cg (n - i) := by
    intro i _
    have hfi : ‖iteratedFDeriv ℝ i f x‖ ≤ B i := hbound_f i x
    have hgi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ Cg (n - i) := by
      simpa [Cg] using (Classical.choose_spec (hdec_g (n - i)) x hx)
    have hchoose0 : 0 ≤ (n.choose i : ℝ) := by positivity
    have hBi0 : 0 ≤ B i := (norm_nonneg _).trans hfi
    have hleft : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ ≤ (n.choose i : ℝ) * B i :=
      mul_le_mul_of_nonneg_left hfi hchoose0
    have hprod := mul_le_mul hleft hgi (by positivity) (mul_nonneg hchoose0 hBi0)
    grind only
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) g x‖)) ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Cg (n - i) :=
    Finset.sum_le_sum fun i hi => hterm i hi
  exact le_trans hmain (by simpa [C] using hsum)

end SpherePacking.ForMathlib
