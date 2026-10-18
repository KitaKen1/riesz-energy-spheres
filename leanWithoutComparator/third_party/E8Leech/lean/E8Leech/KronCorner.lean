import E8Leech.KronDeriv
import E8Leech.KronKernelSign
import E8Leech.CKMRVAxisInversion

/-!
# The corner `u = t = 1`: concavity in the second variable

For fixed `u` the numerator `Φ'(u, ·)` vanishes at `t = u` and at `t = 1/u`. Near the corner both
zeros are close, the divided difference in the nome vanishes at the corner, and no cell bound can
decide its sign. Instead: `G_u(t) = π² t² · kernelE` is a positive multiple of `Φ'(u, t)` and is
strictly concave in `t` on a box around `1`; a strictly concave function with two zeros is positive
between them and negative outside, which is the sign of `Δ(u)Δ(t)(j(u) − j(t))`.

The numerator is a bilinear form `−Σ_k A_k(τ) B_k(z)` of seven `τ`-side and seven `z`-side
factors (`tauPart`, `zPart`), so `G_u'' = −(π⁴t²/144) Σ_k A_k(u) · hOf(B_k)(t)` by the derivation
of `KronDeriv`. The hypothesis `CornerPos` is the positivity of this bilinear form of fourteen
functions of one variable on the box; it is certified separately on a grid of intervals.

For `u = 1` the two zeros coincide; `G_1 ≤ 0` follows by continuity in `u`, and strict concavity
makes the inequality strict away from `t = 1`.

* `evalB_numE_bil`: the bilinear form.
* `CornerPos`: the certificate. `cornerG_strictConcaveOn`: concavity.
* `kernel_pos_of_corner`: (6.4)(1) on the box, off the singular curves.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real Topology

/-! ## The numerator as a bilinear form -/

/-- The `τ`-side factors of the numerator. -/
def tauPart (Λ : ℕ) (E2a Va Wa lA lSA : IExpr) : List IExpr :=
  [.cst (96 * Λ) * t1E E2a Va Wa,
    .cst (-(96 * Λ)) * (d256E Va Wa * (f6E Va Wa - 4 * (E2a - 3 * uhE) * e4E Va Wa)),
    .cst (-(192 * Λ)) * (d256E Va Wa * ((E2a - 3 * uhE) * e4E Va Wa)),
    .cst (96 * Λ) * (d256E Va Wa * f6E Va Wa),
    .cst (-3456) * (d256E Va Wa * e4E Va Wa * uhE),
    3456 * (d256E Va Wa * psi4E Λ Va Wa lA lSA),
    128 * t2E Λ Va Wa lA lSA]

/-- The `z`-side factors of the numerator. -/
def zPart (Λ : ℕ) (E2b Vb Wb lB : IExpr) : List IExpr :=
  [d256E Vb Wb, e4E Vb Wb ^ 3, e4E Vb Wb * f6E Vb Wb * (E2b - 6 * thE),
    e4E Vb Wb ^ 2 * (E2b - 6 * thE) ^ 2, e4E Vb Wb * f6E Vb Wb * (lB * thE - .cst Λ) * thE,
    e4E Vb Wb ^ 2 * Wb * thE ^ 2, xb2E Vb Wb * thE ^ 2]

/-- The pairing of two lists of real numbers. -/
def bil : List ℝ → List ℝ → ℝ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => a * b + bil as bs

theorem bil_map_mul (c : ℝ) :
    ∀ (as : List ℝ) (xs : List IExpr) (f : IExpr → ℝ),
      bil as (xs.map fun x => c * f x) = c * bil as (xs.map f)
  | [], _, _ => by simp [bil]
  | _ :: _, [], _ => by simp [bil]
  | a :: as, x :: xs, f => by
    simp only [List.map_cons, bil, bil_map_mul c as xs f]
    ring

/-- **The numerator is a bilinear form** of the seven `τ`-side and the seven `z`-side factors. -/
theorem evalB_numE_bil (fs : List (ℝ → ℝ)) (Λ : ℕ) (E2a Va Wa lA lSA E2b Vb Wb lB : IExpr)
    (e : NEnv) :
    IExpr.evalB fs (numE Λ E2a Va Wa lA lSA E2b Vb Wb lB) e =
      -bil ((tauPart Λ E2a Va Wa lA lSA).map fun x => IExpr.evalB fs x e)
        ((zPart Λ E2b Vb Wb lB).map fun x => IExpr.evalB fs x e) := by
  simp only [numE, z1E, z2E, tauPart, zPart, List.map_cons, List.map_nil, bil, IExpr.evalB_add,
    IExpr.evalB_sub, IExpr.evalB_mul, IExpr.evalB_neg, IExpr.evalB_nat, IExpr.evalB_pow,
    IExpr.evalB_cst]
  push_cast
  ring

/-- The `τ`-side factors of the kernel. -/
def tauE (Λ : ℕ) : List IExpr := tauPart Λ (.tat 4) vT wT (l0T Λ) lSE

/-- The `z`-side factors of the kernel. -/
def zE (Λ : ℕ) : List IExpr := zPart Λ (.zat 4) vZ wZ (l0Z Λ)

/-! ## Expressions in one of the two variables -/

namespace IExpr

/-- The expression does not involve the second variable. -/
def tauOnly : IExpr → Bool
  | .zat _ => false
  | .tat _ => true
  | .cst _ => true
  | .mono m => m.eb == 0 && m.et == 0
  | .add x y => x.tauOnly && y.tauOnly
  | .sub x y => x.tauOnly && y.tauOnly
  | .mul x y => x.tauOnly && y.tauOnly

/-- The expression does not involve the first variable. -/
def zOnly : IExpr → Bool
  | .zat _ => true
  | .tat _ => false
  | .cst _ => true
  | .mono m => m.ea == 0 && m.eu == 0
  | .add x y => x.zOnly && y.zOnly
  | .sub x y => x.zOnly && y.zOnly
  | .mul x y => x.zOnly && y.zOnly

theorem evalB_congr_tau (fs : List (ℝ → ℝ)) {x : IExpr} (h : x.tauOnly = true) {e e' : NEnv}
    (ha : e.a = e'.a) (hu : e.u = e'.u) (hl : e.l = e'.l) : evalB fs x e = evalB fs x e' := by
  induction x with
  | zat i => simp [tauOnly] at h
  | tat i =>
    show fs.getD i (fun _ => 0) e.a = fs.getD i (fun _ => 0) e'.a
    rw [ha]
  | cst c => rfl
  | mono m =>
    simp only [tauOnly, Bool.and_eq_true, beq_iff_eq] at h
    show m.eval e = m.eval e'
    simp only [NMono.eval, h.1, h.2, pow_zero, mul_one, ha, hu, hl]
  | add x y ihx ihy =>
    simp only [tauOnly, Bool.and_eq_true] at h
    show evalB fs x e + evalB fs y e = evalB fs x e' + evalB fs y e'
    rw [ihx h.1, ihy h.2]
  | sub x y ihx ihy =>
    simp only [tauOnly, Bool.and_eq_true] at h
    show evalB fs x e - evalB fs y e = evalB fs x e' - evalB fs y e'
    rw [ihx h.1, ihy h.2]
  | mul x y ihx ihy =>
    simp only [tauOnly, Bool.and_eq_true] at h
    show evalB fs x e * evalB fs y e = evalB fs x e' * evalB fs y e'
    rw [ihx h.1, ihy h.2]

theorem evalB_congr_z (fs : List (ℝ → ℝ)) {x : IExpr} (h : x.zOnly = true) {e e' : NEnv}
    (hb : e.b = e'.b) (ht : e.t = e'.t) (hl : e.l = e'.l) : evalB fs x e = evalB fs x e' := by
  induction x with
  | zat i =>
    show fs.getD i (fun _ => 0) e.b = fs.getD i (fun _ => 0) e'.b
    rw [hb]
  | tat i => simp [zOnly] at h
  | cst c => rfl
  | mono m =>
    simp only [zOnly, Bool.and_eq_true, beq_iff_eq] at h
    show m.eval e = m.eval e'
    simp only [NMono.eval, h.1, h.2, pow_zero, one_mul, mul_one, hb, ht, hl]
  | add x y ihx ihy =>
    simp only [zOnly, Bool.and_eq_true] at h
    show evalB fs x e + evalB fs y e = evalB fs x e' + evalB fs y e'
    rw [ihx h.1, ihy h.2]
  | sub x y ihx ihy =>
    simp only [zOnly, Bool.and_eq_true] at h
    show evalB fs x e - evalB fs y e = evalB fs x e' - evalB fs y e'
    rw [ihx h.1, ihy h.2]
  | mul x y ihx ihy =>
    simp only [zOnly, Bool.and_eq_true] at h
    show evalB fs x e * evalB fs y e = evalB fs x e' * evalB fs y e'
    rw [ihx h.1, ihy h.2]

end IExpr

/-! ## The two variables exchanged -/

/-- The monomial with the two nomes and the two reciprocals exchanged. -/
def NMono.swap (m : NMono) : NMono := ⟨m.eb, m.ea, m.et, m.eu, m.el⟩

namespace IExpr

/-- The expression with the two variables exchanged. -/
def swap : IExpr → IExpr
  | .zat i => .tat i
  | .tat i => .zat i
  | .cst c => .cst c
  | .mono m => .mono m.swap
  | .add x y => .add (swap x) (swap y)
  | .sub x y => .sub (swap x) (swap y)
  | .mul x y => .mul (swap x) (swap y)

theorem evalB_swap (fs : List (ℝ → ℝ)) (x : IExpr) (a b u t l : ℝ) :
    evalB fs (swap x) ⟨a, b, u, t, l⟩ = evalB fs x ⟨b, a, t, u, l⟩ := by
  induction x with
  | zat i => rfl
  | tat i => rfl
  | cst c => rfl
  | mono m =>
    show m.swap.eval ⟨a, b, u, t, l⟩ = m.eval ⟨b, a, t, u, l⟩
    simp only [NMono.eval, NMono.swap]
    ring
  | add x y ihx ihy =>
    show evalB fs (swap x) ⟨a, b, u, t, l⟩ + evalB fs (swap y) ⟨a, b, u, t, l⟩ =
      evalB fs x ⟨b, a, t, u, l⟩ + evalB fs y ⟨b, a, t, u, l⟩
    rw [ihx, ihy]
  | sub x y ihx ihy =>
    show evalB fs (swap x) ⟨a, b, u, t, l⟩ - evalB fs (swap y) ⟨a, b, u, t, l⟩ =
      evalB fs x ⟨b, a, t, u, l⟩ - evalB fs y ⟨b, a, t, u, l⟩
    rw [ihx, ihy]
  | mul x y ihx ihy =>
    show evalB fs (swap x) ⟨a, b, u, t, l⟩ * evalB fs (swap y) ⟨a, b, u, t, l⟩ =
      evalB fs x ⟨b, a, t, u, l⟩ * evalB fs y ⟨b, a, t, u, l⟩
    rw [ihx, ihy]

end IExpr

/-! ## The function `G_u` and its derivatives -/

section Corner

variable (Λ : ℕ)

/-- `π² s² ·` the numerator, as a function of the second variable. -/
noncomputable def cornerG (v s : ℝ) : ℝ :=
  π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv v s)

/-- `π² s² · x` along the second variable. -/
noncomputable def val0 (u : ℝ) (x : IExpr) (s : ℝ) : ℝ :=
  π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u s)

/-- The derivative of `val0`. -/
noncomputable def val1 (u : ℝ) (x : IExpr) (s : ℝ) : ℝ :=
  2 * π ^ 2 * s * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u s) -
    π ^ 3 * s ^ 2 / 12 * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.dz Λ x) (axisNEnv u s)

/-- The derivative of `val1`. -/
noncomputable def val2 (u : ℝ) (x : IExpr) (s : ℝ) : ℝ :=
  π ^ 4 * s ^ 2 / 144 * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv u s)

/-- The values of the `τ`-side factors at `u`. -/
noncomputable def tauVals (u : ℝ) : List ℝ :=
  (tauE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv u u)

/-- The values at `t` of the second-derivative expressions of the `z`-side factors. -/
noncomputable def zVals (t : ℝ) : List ℝ :=
  (zE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv t t)

/-- **The corner certificate**: the bilinear form of the second derivative is positive on the
box `[1/c₀, c₀]²`. -/
def CornerPos (c₀ : ℝ) : Prop :=
  ∀ u t : ℝ, c₀⁻¹ ≤ u → u ≤ c₀ → c₀⁻¹ ≤ t → t ≤ c₀ → 0 < bil (tauVals Λ u) (zVals Λ t)

theorem hasDerivAt_bil_val0 (u : ℝ) {t : ℝ} (ht : 0 < t) (hx : Real.exp (-π * t) < 1 / 3) :
    ∀ (as : List ℝ) (xs : List IExpr),
      HasDerivAt (fun s => bil as (xs.map fun x => val0 Λ u x s))
        (bil as (xs.map fun x => val1 Λ u x t)) t
  | [], _ => hasDerivAt_const t 0
  | _ :: _, [] => hasDerivAt_const t 0
  | a :: as, x :: xs =>
    ((hasDerivAt_sq_mul_evalB Λ u ht hx x).const_mul a).add (hasDerivAt_bil_val0 u ht hx as xs)

theorem hasDerivAt_bil_val1 (u : ℝ) {t : ℝ} (ht : 0 < t) (hx : Real.exp (-π * t) < 1 / 3) :
    ∀ (as : List ℝ) (xs : List IExpr),
      HasDerivAt (fun s => bil as (xs.map fun x => val1 Λ u x s))
        (bil as (xs.map fun x => val2 Λ u x t)) t
  | [], _ => hasDerivAt_const t 0
  | _ :: _, [] => hasDerivAt_const t 0
  | a :: as, x :: xs =>
    ((hasDerivAt_sq_mul_evalB' Λ u ht hx x).const_mul a).add (hasDerivAt_bil_val1 u ht hx as xs)

variable {Λ}

/-- `G_u` as a bilinear form. -/
theorem cornerG_eq (hτ : ∀ x ∈ tauE Λ, x.tauOnly = true) (v s : ℝ) :
    cornerG Λ v s = -bil (tauVals Λ v) ((zE Λ).map fun x => val0 Λ v x s) := by
  have h : IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv v s) =
      -bil ((tauE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s))
        ((zE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s)) :=
    evalB_numE_bil _ Λ _ _ _ _ _ _ _ _ _ _
  have hmap : ((tauE Λ).map fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s)) =
      tauVals Λ v :=
    List.map_congr_left fun x hx =>
      IExpr.evalB_congr_tau _ (hτ x hx) (e := axisNEnv v s) (e' := axisNEnv v v) rfl rfl rfl
  have hlin := bil_map_mul (π ^ 2 * s ^ 2) (tauVals Λ v) (zE Λ)
    (fun x => IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s))
  show π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv v s) =
    -bil (tauVals Λ v) ((zE Λ).map fun x =>
      π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) x (axisNEnv v s))
  rw [hlin, h, hmap]
  ring

theorem cornerG_hasDerivAt (hτ : ∀ x ∈ tauE Λ, x.tauOnly = true) (v : ℝ) {s : ℝ} (hs : 0 < s)
    (hxs : Real.exp (-π * s) < 1 / 3) :
    HasDerivAt (cornerG Λ v) (-bil (tauVals Λ v) ((zE Λ).map fun x => val1 Λ v x s)) s := by
  have h := (hasDerivAt_bil_val0 Λ v hs hxs (tauVals Λ v) (zE Λ)).neg
  have hfun : cornerG Λ v = fun s => -bil (tauVals Λ v) ((zE Λ).map fun x => val0 Λ v x s) :=
    funext (cornerG_eq hτ v)
  rw [hfun]
  exact h

theorem cornerG1_hasDerivAt (v : ℝ) {s : ℝ} (hs : 0 < s) (hxs : Real.exp (-π * s) < 1 / 3) :
    HasDerivAt (fun s => -bil (tauVals Λ v) ((zE Λ).map fun x => val1 Λ v x s))
      (-bil (tauVals Λ v) ((zE Λ).map fun x => val2 Λ v x s)) s :=
  (hasDerivAt_bil_val1 Λ v hs hxs (tauVals Λ v) (zE Λ)).neg

/-- The second derivative of `G_u` is negative on the box. -/
theorem cornerG2_neg (hz : ∀ x ∈ zE Λ, (IExpr.hOf Λ x).zOnly = true) {c₀ : ℝ}
    (H : CornerPos Λ c₀) {v s : ℝ} (hv : c₀⁻¹ ≤ v) (hv' : v ≤ c₀) (hs : c₀⁻¹ ≤ s) (hs' : s ≤ c₀)
    (hs0 : 0 < s) : -bil (tauVals Λ v) ((zE Λ).map fun x => val2 Λ v x s) < 0 := by
  have hmap : ((zE Λ).map fun x => val2 Λ v x s) =
      (zE Λ).map fun x => π ^ 4 * s ^ 2 / 144 *
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s) :=
    List.map_congr_left fun x hx => by
      show π ^ 4 * s ^ 2 / 144 *
          IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv v s) =
        π ^ 4 * s ^ 2 / 144 * IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s)
      rw [IExpr.evalB_congr_z _ (hz x hx) (e := axisNEnv v s) (e' := axisNEnv s s) rfl rfl rfl]
  have hlin := bil_map_mul (π ^ 4 * s ^ 2 / 144) (tauVals Λ v) (zE Λ)
    (fun x => IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s))
  have hpos : 0 < bil (tauVals Λ v) ((zE Λ).map fun x =>
      IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ x) (axisNEnv s s)) := H v s hv hv' hs hs'
  have hc : 0 < π ^ 4 * s ^ 2 / 144 := by positivity
  rw [hmap, hlin]
  have := mul_pos hc hpos
  linarith

/-- `exp (−π s) < 1/3` on the box. -/
theorem nome_lt_of_ge {c₀ : ℝ} (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) {s : ℝ} (hs : c₀⁻¹ ≤ s) :
    Real.exp (-π * s) < 1 / 3 := by
  have h : -π * s ≤ -π * c₀⁻¹ := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hs)]
  exact lt_of_le_of_lt (Real.exp_le_exp.mpr h) hx₀

/-- **`G_u` is strictly concave on the box.** -/
theorem cornerG_strictConcaveOn (hτ : ∀ x ∈ tauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ zE Λ, (IExpr.hOf Λ x).zOnly = true) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : CornerPos Λ c₀) {v : ℝ} (hv : c₀⁻¹ ≤ v)
    (hv' : v ≤ c₀) : StrictConcaveOn ℝ (Set.Icc c₀⁻¹ c₀) (cornerG Λ v) := by
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀
  have hd : ∀ s : ℝ, c₀⁻¹ ≤ s → HasDerivAt (cornerG Λ v)
      (-bil (tauVals Λ v) ((zE Λ).map fun x => val1 Λ v x s)) s := fun s hs =>
    cornerG_hasDerivAt hτ v (hc0.trans_le hs) (nome_lt_of_ge hx₀ hs)
  refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt) (fun s hs => ?_)
  rw [interior_Icc] at hs
  have hev : deriv (cornerG Λ v) =ᶠ[𝓝 s]
      fun s => -bil (tauVals Λ v) ((zE Λ).map fun x => val1 Λ v x s) := by
    filter_upwards [Ioi_mem_nhds hs.1] with s' hs'
    exact (hd s' (le_of_lt hs')).deriv
  show deriv (deriv (cornerG Λ v)) s < 0
  rw [hev.deriv_eq,
    (cornerG1_hasDerivAt v (hc0.trans hs.1) (nome_lt_of_ge hx₀ hs.1.le)).deriv]
  exact cornerG2_neg hz H hv hv' hs.1.le hs.2.le (hc0.trans hs.1)

/-- `G_u(u) = 0`. -/
theorem cornerG_self (v : ℝ) : cornerG Λ v v = 0 := by
  have h : IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv v v) = 0 := by
    rw [kernelE_evalB]
    exact axE_diag _ _ _ _ _ _ _ _
  show π ^ 2 * v ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv v v) = 0
  rw [h, mul_zero]

/-- `G_u(1/u) = 0`. -/
theorem cornerG_inv {v : ℝ} (hv : 0 < v) : cornerG Λ v v⁻¹ = 0 := by
  have h := kernelE_eval_axis Λ [] hv (inv_pos.mpr hv)
  rw [axE2_inv hv, axV_inv hv, axW_inv hv, axL_inv hv, axPhi_anti, mul_zero] at h
  show π ^ 2 * v⁻¹ ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv v v⁻¹) = 0
  rw [h, mul_zero]

/-- `G_u(t)` is continuous in `u`. -/
theorem continuousAt_cornerG_left (s : ℝ) {v : ℝ} (hv : 0 < v)
    (hxv : Real.exp (-π * v) < 1 / 3) : ContinuousAt (fun w => cornerG Λ w s) v := by
  have h := hasDerivAt_evalB Λ s hv hxv (IExpr.swap (kernelE Λ))
  have hfun : (fun w => cornerG Λ w s) = fun w => π ^ 2 * s ^ 2 *
      IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.swap (kernelE Λ)) (axisNEnv s w) := by
    funext w
    have key : IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv w s) =
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.swap (kernelE Λ)) (axisNEnv s w) :=
      (IExpr.evalB_swap _ (kernelE Λ) (Real.exp (-π * s)) (Real.exp (-π * w)) (1 / (π * s))
        (1 / (π * w)) (Real.log 2)).symm
    show π ^ 2 * s ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv w s) = _
    rw [key]
  rw [hfun]
  exact (h.const_mul (π ^ 2 * s ^ 2)).continuousAt

end Corner

/-! ## A strictly concave function with two zeros -/

theorem convex_comb_eq {x y z : ℝ} (h : x ≠ z) :
    (z - y) / (z - x) + (y - x) / (z - x) = 1 ∧
      (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
  have hd : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  constructor
  · rw [← add_div, div_eq_one_iff_eq hd]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd]
    ring

/-- A strictly concave function with zeros at `p < r` is positive between them and negative
outside. -/
theorem sign_of_two_zeros {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f) {p r t : ℝ}
    (hp : p ∈ S) (hr : r ∈ S) (ht : t ∈ S) (hpr : p < r) (fp : f p = 0) (fr : f r = 0) :
    (p < t → t < r → 0 < f t) ∧ (t < p → f t < 0) ∧ (r < t → f t < 0) := by
  refine ⟨fun h1 h2 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · obtain ⟨hab, hc⟩ := convex_comb_eq (x := p) (y := t) (z := r) hpr.ne
    have hd : 0 < r - p := sub_pos.mpr hpr
    have h := hf.2 hp hr hpr.ne (div_pos (sub_pos.mpr h2) hd) (div_pos (sub_pos.mpr h1) hd) hab
    simp only [smul_eq_mul] at h
    rw [hc, fp, fr] at h
    linarith
  · have htr : t < r := h1.trans hpr
    obtain ⟨hab, hc⟩ := convex_comb_eq (x := t) (y := p) (z := r) htr.ne
    have hd : 0 < r - t := sub_pos.mpr htr
    have ha : 0 < (r - p) / (r - t) := div_pos (sub_pos.mpr hpr) hd
    have h := hf.2 ht hr htr.ne ha (div_pos (sub_pos.mpr h1) hd) hab
    simp only [smul_eq_mul] at h
    rw [hc, fp, fr] at h
    have h2 : (r - p) / (r - t) * f t < 0 := by linarith
    by_contra hcon
    have := mul_nonneg ha.le (not_lt.mp hcon)
    linarith
  · have hpt : p < t := hpr.trans h1
    obtain ⟨hab, hc⟩ := convex_comb_eq (x := p) (y := r) (z := t) hpt.ne
    have hd : 0 < t - p := sub_pos.mpr hpt
    have hb : 0 < (r - p) / (t - p) := div_pos (sub_pos.mpr hpr) hd
    have h := hf.2 hp ht hpt.ne (div_pos (sub_pos.mpr h1) hd) hb hab
    simp only [smul_eq_mul] at h
    rw [hc, fp, fr] at h
    have h2 : (r - p) / (t - p) * f t < 0 := by linarith
    by_contra hcon
    have := mul_nonneg hb.le (not_lt.mp hcon)
    linarith

theorem inv_lt_of_one_lt_mul {a b : ℝ} (ha : 0 < a) (h : 1 < a * b) : a⁻¹ < b := by
  by_contra hcon
  have h2 := mul_inv_cancel₀ ha.ne'
  have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  linarith

theorem lt_inv_of_mul_lt_one {a b : ℝ} (ha : 0 < a) (h : a * b < 1) : b < a⁻¹ := by
  by_contra hcon
  have h2 := mul_inv_cancel₀ ha.ne'
  have := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  linarith

theorem inv_le_one_of_le {a : ℝ} (h : 1 ≤ a) : a⁻¹ ≤ 1 := by
  have ha : 0 < a := one_pos.trans_le h
  by_contra hcon
  have h2 := mul_inv_cancel₀ ha.ne'
  have := mul_lt_mul_of_pos_left (not_le.mp hcon) ha
  linarith

/-! ## The sign of `G_u` on the box -/

section Sign

variable {Λ : ℕ} {c₀ : ℝ}

/-- The sign of `G_u(t)` for `u ≠ 1` on the box: positive strictly between `u` and `1/u`,
negative strictly outside. -/
theorem cornerG_sign (hτ : ∀ x ∈ tauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ zE Λ, (IExpr.hOf Λ x).zOnly = true) (hc₀ : 0 < c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : CornerPos Λ c₀) {v t : ℝ} (hv : c₀⁻¹ ≤ v)
    (hv' : v ≤ c₀) (hv1 : v ≠ 1) (ht : c₀⁻¹ ≤ t) (ht' : t ≤ c₀) :
    (v < t → t < v⁻¹ → 0 < cornerG Λ v t) ∧ (v⁻¹ < t → t < v → 0 < cornerG Λ v t) ∧
      (t < v → t < v⁻¹ → cornerG Λ v t < 0) ∧ (v < t → v⁻¹ < t → cornerG Λ v t < 0) := by
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀
  have hv0 : 0 < v := hc0.trans_le hv
  have hconc := cornerG_strictConcaveOn hτ hz hc₀ hx₀ H hv hv'
  have hvI : v ∈ Set.Icc c₀⁻¹ c₀ := ⟨hv, hv'⟩
  have hiI : v⁻¹ ∈ Set.Icc c₀⁻¹ c₀ := by
    refine ⟨inv_anti₀ hv0 hv', ?_⟩
    have h := inv_anti₀ hc0 hv
    rwa [inv_inv] at h
  have htI : t ∈ Set.Icc c₀⁻¹ c₀ := ⟨ht, ht'⟩
  have hne : v ≠ v⁻¹ := by
    intro h
    have h2 := mul_inv_cancel₀ hv0.ne'
    rw [← h] at h2
    have h3 : (v - 1) * (v + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hv1 (by linarith)
    · linarith
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨s1, s2, s3⟩ := sign_of_two_zeros hconc hvI hiI htI h (cornerG_self v)
      (cornerG_inv hv0)
    exact ⟨fun a b => s1 a b, fun a b => absurd (a.trans b) (not_lt.mpr h.le),
      fun a _ => s2 a, fun _ b => s3 b⟩
  · obtain ⟨s1, s2, s3⟩ := sign_of_two_zeros hconc hiI hvI htI h (cornerG_inv hv0)
      (cornerG_self v)
    exact ⟨fun a b => absurd (a.trans b) (not_lt.mpr h.le), fun a b => s1 a b,
      fun _ b => s2 b, fun a _ => s3 a⟩

/-- `G_1(t) < 0` for `t ≠ 1` on the box. -/
theorem cornerG_one_neg (hτ : ∀ x ∈ tauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ zE Λ, (IExpr.hOf Λ x).zOnly = true) (hc₀ : 1 ≤ c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : CornerPos Λ c₀) {t : ℝ} (ht : c₀⁻¹ ≤ t)
    (ht' : t ≤ c₀) (ht1 : t ≠ 1) : cornerG Λ 1 t < 0 := by
  have hc₀0 : 0 < c₀ := one_pos.trans_le hc₀
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀0
  have h1lo : c₀⁻¹ ≤ 1 := inv_le_one_of_le hc₀
  have h1I : (1 : ℝ) ∈ Set.Icc c₀⁻¹ c₀ := ⟨h1lo, hc₀⟩
  have hconc := cornerG_strictConcaveOn hτ hz hc₀0 hx₀ H h1lo hc₀
  have hG1 : cornerG Λ 1 1 = 0 := cornerG_self 1
  have hle : ∀ s : ℝ, c₀⁻¹ ≤ s → s ≤ c₀ → cornerG Λ 1 s ≤ 0 := by
    intro s hs hs'
    rcases eq_or_ne s 1 with rfl | hs1
    · exact hG1.le
    · have hs0 : 0 < s := hc0.trans_le hs
      have hcont := continuousAt_cornerG_left (Λ := Λ) s one_pos (nome_lt_of_ge hx₀ h1lo)
      obtain ⟨b, hb1, hbc, hb⟩ : ∃ b : ℝ, 1 < b ∧ b ≤ c₀ ∧ ∀ v : ℝ, 1 < v → v < b →
          (v < s ∧ v⁻¹ < s) ∨ (s < v ∧ s < v⁻¹) := by
        rcases lt_or_gt_of_ne hs1 with h | h
        · have hb1 : 1 < s⁻¹ := by
            have := lt_inv_of_mul_lt_one hs0 (by rw [mul_one]; exact h)
            exact this
          have hbc : s⁻¹ ≤ c₀ := by
            have h2 := inv_anti₀ hc0 hs
            rwa [inv_inv] at h2
          refine ⟨s⁻¹, hb1, hbc, fun v hv1 hvb => Or.inr ⟨h.trans hv1, ?_⟩⟩
          have hv0 : 0 < v := one_pos.trans hv1
          have h3 : v * s < 1 := by
            have h4 := mul_lt_mul_of_pos_right hvb hs0
            rw [inv_mul_cancel₀ hs0.ne'] at h4
            exact h4
          exact lt_inv_of_mul_lt_one hv0 h3
        · refine ⟨s, h, hs', fun v hv1 hvb => Or.inl ⟨hvb, ?_⟩⟩
          have hv0 : 0 < v := one_pos.trans hv1
          have h3 : v⁻¹ < 1 := inv_lt_of_one_lt_mul hv0 (by rw [mul_one]; exact hv1)
          exact h3.trans h
      have hev : ∀ᶠ v in 𝓝[>] (1 : ℝ), cornerG Λ v s ≤ 0 := by
        filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hb1).filter_mono nhdsWithin_le_nhds]
          with v hv1 hvb
        have hv1' : (1 : ℝ) < v := hv1
        have hsg := cornerG_sign hτ hz hc₀0 hx₀ H (h1lo.trans hv1'.le) (hvb.le.trans hbc)
          hv1'.ne' hs hs'
        rcases hb v hv1' hvb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hsg.2.2.2 h1 h2).le
        · exact (hsg.2.2.1 h1 h2).le
      exact le_of_tendsto (Filter.Tendsto.mono_left hcont nhdsWithin_le_nhds) hev
  have htI : t ∈ Set.Icc c₀⁻¹ c₀ := ⟨ht, ht'⟩
  have h := hconc.2 h1I htI (Ne.symm ht1) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  rw [hG1] at h
  have hm := hle (1 / 2 * 1 + 1 / 2 * t) (by linarith) (by linarith)
  linarith

end Sign

/-! ## The kernel on the box -/

theorem pos_of_mul_mul {κ K N G : ℝ} (hκ : 0 < κ) (h : G = κ * (K * N))
    (hs : (0 < G ∧ 0 < N) ∨ (G < 0 ∧ N < 0)) : 0 < K := by
  by_contra hK
  have hK' : 0 ≤ -K := neg_nonneg.mpr (not_lt.mp hK)
  rcases hs with ⟨hG, hN⟩ | ⟨hG, hN⟩
  · nlinarith [mul_nonneg hκ.le (mul_nonneg hK' hN.le)]
  · nlinarith [mul_nonneg hκ.le (mul_nonneg hK' (neg_nonneg.mpr hN.le))]

/-- **(6.4)(1) on the corner box.** If the bilinear form of the second derivative is positive on
`[1/c₀, c₀]²`, then the hat kernel is positive there, off the singular curves. -/
theorem kernel_pos_of_corner {Λ : ℕ} (hΛ : 0 < Λ) (hτ : ∀ x ∈ tauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ zE Λ, (IExpr.hOf Λ x).zOnly = true) {c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    (hx₀ : Real.exp (-π * c₀⁻¹) < 1 / 3) (H : CornerPos Λ c₀) {q t : ℝ} (hq : c₀⁻¹ ≤ q)
    (hq' : q ≤ c₀) (ht : c₀⁻¹ ≤ t) (ht' : t ≤ c₀)
    (hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t)) :
    0 < (ckmrvEightHatKernel (imagPt q) (imagPt t)).re := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hc₀0 : 0 < c₀ := one_pos.trans_le hc₀
  have hc0 : 0 < c₀⁻¹ := inv_pos.mpr hc₀0
  have hq0 : 0 < q := hc0.trans_le hq
  have ht0 : 0 < t := hc0.trans_le ht
  have hqt : q ≠ t := fun h => hJ (by rw [h])
  have hJinv : kleinModularJ (imagPt q⁻¹) = kleinModularJ (imagPt q) := by
    rw [← S_smul_imagPt hq0, kleinModularJ_S]
  have hqt' : q⁻¹ ≠ t := fun h => hJ (by rw [← hJinv, h])
  have hprod : q * t ≠ 1 := by
    intro h
    apply hqt'
    have h2 := mul_inv_cancel₀ hq0.ne'
    have h3 : q * (q⁻¹ - t) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hq0.ne'
    · linarith
  -- the numerator and the denominator
  have haxis := ckmrvEightHatKernel_axis hq0 ht0 hJ
  have hG : cornerG Λ q t = π ^ 2 * t ^ 2 *
      (1769472 * Λ * π * (1 / (π * q)) * (1 / (π * t)) ^ 2) * 2 *
      ((ckmrvEightHatKernel (imagPt q) (imagPt t)).re * axNu (axV q) (axW q) (axV t) (axW t)) := by
    show π ^ 2 * t ^ 2 * IExpr.evalB (kernelAtoms Λ ++ []) (kernelE Λ) (axisNEnv q t) = _
    rw [kernelE_eval_axis Λ [] hq0 ht0, ← haxis]
    ring
  have hκ : 0 < π ^ 2 * t ^ 2 * (1769472 * Λ * π * (1 / (π * q)) * (1 / (π * t)) ^ 2) * 2 := by
    positivity
  have hN : ∀ D : ℝ, D ≠ 0 → axNu (axV q) (axW q) (axV t) (axW t) =
      axNu (axV q) (axW q) (axV t) (axW t) / D * D := fun D hD => (div_mul_cancel₀ _ hD).symm
  refine pos_of_mul_mul hκ hG ?_
  rcases lt_or_gt_of_ne hqt with hlt | hlt
  · -- `q < t`: the difference of the nomes is negative
    have hD : Real.exp (-π * t) - Real.exp (-π * q) < 0 :=
      sub_neg.mpr (Real.exp_lt_exp.mpr (by nlinarith))
    rcases lt_or_gt_of_ne hprod with hp | hp
    · -- `q t < 1`: between the zeros
      have hden := ckmrvAxisDividedDenominator_neg hq0 ht0 hqt hp
      have hNpos : 0 < axNu (axV q) (axW q) (axV t) (axW t) := by
        rw [hN _ hD.ne]
        exact mul_pos_of_neg_of_neg hden hD
      have htinv : t < q⁻¹ := lt_inv_of_mul_lt_one hq0 hp
      have hq1 : q ≠ 1 := by
        intro h
        rw [h, inv_one] at htinv
        rw [h] at hlt
        linarith
      exact Or.inl ⟨(cornerG_sign hτ hz hc₀0 hx₀ H hq hq' hq1 ht ht').1 hlt htinv, hNpos⟩
    · -- `1 < q t`: above both zeros
      have hden := ckmrvAxisDividedDenominator_pos hq0 ht0 hqt hp
      have hNneg : axNu (axV q) (axW q) (axV t) (axW t) < 0 := by
        rw [hN _ hD.ne]
        exact mul_neg_of_pos_of_neg hden hD
      have htinv : q⁻¹ < t := inv_lt_of_one_lt_mul hq0 hp
      refine Or.inr ⟨?_, hNneg⟩
      rcases eq_or_ne q 1 with h1 | h1
      · rw [h1]
        refine cornerG_one_neg hτ hz hc₀ hx₀ H ht ht' ?_
        rw [h1] at hlt
        exact hlt.ne'
      · exact (cornerG_sign hτ hz hc₀0 hx₀ H hq hq' h1 ht ht').2.2.2 hlt htinv
  · -- `t < q`: the difference of the nomes is positive
    have hD : 0 < Real.exp (-π * t) - Real.exp (-π * q) :=
      sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith))
    rcases lt_or_gt_of_ne hprod with hp | hp
    · -- `q t < 1`: below both zeros
      have hden := ckmrvAxisDividedDenominator_neg hq0 ht0 hqt hp
      have hNneg : axNu (axV q) (axW q) (axV t) (axW t) < 0 := by
        rw [hN _ hD.ne']
        exact mul_neg_of_neg_of_pos hden hD
      have htinv : t < q⁻¹ := lt_inv_of_mul_lt_one hq0 hp
      refine Or.inr ⟨?_, hNneg⟩
      rcases eq_or_ne q 1 with h1 | h1
      · rw [h1]
        refine cornerG_one_neg hτ hz hc₀ hx₀ H ht ht' ?_
        rw [h1] at hlt
        exact hlt.ne
      · exact (cornerG_sign hτ hz hc₀0 hx₀ H hq hq' h1 ht ht').2.2.1 hlt htinv
    · -- `1 < q t`: between the zeros
      have hden := ckmrvAxisDividedDenominator_pos hq0 ht0 hqt hp
      have hNpos : 0 < axNu (axV q) (axW q) (axV t) (axW t) := by
        rw [hN _ hD.ne']
        exact mul_pos hden hD
      have htinv : q⁻¹ < t := inv_lt_of_one_lt_mul hq0 hp
      have hq1 : q ≠ 1 := by
        intro h
        rw [h, inv_one] at htinv
        rw [h] at hlt
        linarith
      exact Or.inl ⟨(cornerG_sign hτ hz hc₀0 hx₀ H hq hq' hq1 ht ht').2.1 htinv hlt, hNpos⟩

end E8Leech.Kron
