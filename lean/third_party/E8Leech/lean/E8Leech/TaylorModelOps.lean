import E8Leech.TaylorModel
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Taylor-model operations and divided-difference Taylor models

* bounds of monomials and polynomials on a box (`Mono.bound`, `Poly.bound`);
* `TM.add`, `TM.mul` (truncation to nome degree `≤ D`), constants and scaling, with soundness;
* `DD`: triples `(value at a, value at b, divided difference)` closed under `+` and `*` by the
  product rule `(f g)[a,b] = f[a,b]·g(b) + f(a)·g[a,b]`.

The divided-difference triples turn the `z`-side change of nome `a ↦ b` into explicit polynomial
arithmetic, which is how the removable singularity of `𝒦̂` on the diagonal is handled.
-/

namespace E8Leech.Taylor

/-! ## Bounds on a box -/

theorem zpow_le_zpowHi {lo hi : ℚ} {x : ℝ} (hlo : 0 < lo) (hx1 : (lo : ℝ) ≤ x) (hx2 : x ≤ hi)
    (n : ℤ) : x ^ n ≤ (zpowHi lo hi n : ℝ) := by
  have hx : 0 < x := lt_of_lt_of_le (by exact_mod_cast hlo) hx1
  unfold zpowHi
  split_ifs with hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp only [zpow_natCast, Int.toNat_natCast]
    push_cast
    exact pow_le_pow_left₀ hx.le hx2 k
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (not_le.mp hn).le
    subst hk
    simp only [zpow_neg, zpow_natCast]
    push_cast
    exact inv_anti₀ (pow_pos (by exact_mod_cast hlo) k) (pow_le_pow_left₀ (by exact_mod_cast hlo.le) hx1 k)

theorem mul_le_mul_nonneg {a b c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d :=
  mul_le_mul h1 h2 hc (le_trans ha h1)

theorem zpowHi_pos {lo hi : ℚ} (hlo : 0 < lo) (hhi : 0 < hi) (n : ℤ) : 0 < zpowHi lo hi n := by
  unfold zpowHi
  split_ifs
  · exact pow_pos hhi _
  · exact zpow_pos hlo _

theorem Mono.abs_eval_le {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (m : Mono) :
    |m.eval e| ≤ (Mono.bound B m : ℝ) := by
  obtain ⟨ha0, hb0, hu0, ht0, hp0, hl0⟩ := hB
  obtain ⟨ha1, ha2, hb1, hb2, hu1, hu2, ht1, ht2, hp1, hp2, hl1, hl2⟩ := he
  have ha : 0 ≤ e.a := le_trans (by exact_mod_cast ha0) ha1
  have hb : 0 ≤ e.b := le_trans (by exact_mod_cast hb0) hb1
  have hu : 0 < e.u := lt_of_lt_of_le (by exact_mod_cast hu0) hu1
  have ht : 0 < e.t := lt_of_lt_of_le (by exact_mod_cast ht0) ht1
  have hp : 0 < e.p := lt_of_lt_of_le (by exact_mod_cast hp0) hp1
  have hl : 0 < e.l := lt_of_lt_of_le (by exact_mod_cast hl0) hl1
  have hpos : 0 ≤ m.eval e := by
    unfold Mono.eval
    positivity
  rw [abs_of_nonneg hpos]
  have f1 : e.a ^ m.ea ≤ (B.ahi : ℝ) ^ m.ea := pow_le_pow_left₀ ha ha2 _
  have f2 : e.b ^ m.eb ≤ (B.bhi : ℝ) ^ m.eb := pow_le_pow_left₀ hb hb2 _
  have f3 : e.u ^ m.eu ≤ (B.uhi : ℝ) ^ m.eu := pow_le_pow_left₀ hu.le hu2 _
  have f4 := zpow_le_zpowHi ht0 ht1 ht2 m.et
  have f5 := zpow_le_zpowHi hp0 hp1 hp2 m.ep
  have f6 : e.l ^ m.el ≤ (B.lhi : ℝ) ^ m.el := pow_le_pow_left₀ hl.le hl2 _
  unfold Mono.eval Mono.bound
  push_cast
  refine mul_le_mul_nonneg (mul_le_mul_nonneg (mul_le_mul_nonneg (mul_le_mul_nonneg
    (mul_le_mul_nonneg f1 f2 (by positivity) (by positivity)) f3 (by positivity) (by positivity))
    f4 (by positivity) (zpow_pos ht _).le) f5 (by positivity) (zpow_pos hp _).le) f6
    (by positivity) (by positivity)

theorem Poly.abs_eval_le {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (P : Poly) :
    |Poly.eval P e| ≤ (Poly.bound B P : ℝ) := by
  induction P with
  | nil => simp [Poly.bound]
  | cons mc P ih =>
    rw [Poly.eval_cons]
    have hb : Poly.bound B (mc :: P) = |mc.2| * Mono.bound B mc.1 + Poly.bound B P := by
      simp [Poly.bound]
    rw [hb]
    push_cast
    calc |(mc.2 : ℝ) * Mono.eval mc.1 e + Poly.eval P e|
        ≤ |(mc.2 : ℝ)| * |Mono.eval mc.1 e| + |Poly.eval P e| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(mc.2 : ℝ)| * (Mono.bound B mc.1 : ℝ) + (Poly.bound B P : ℝ) := by
          gcongr
          exact Mono.abs_eval_le hB he mc.1

/-! ## Taylor-model arithmetic -/

namespace TM

def add (T₁ T₂ : TM) : TM := ⟨Poly.merge T₁.P T₂.P, T₁.r + T₂.r⟩

def scale (c : ℚ) (T : TM) : TM := ⟨Poly.scale c T.P, |c| * T.r⟩

def sub (T₁ T₂ : TM) : TM := add T₁ (scale (-1) T₂)

def const (c : ℚ) : TM := ⟨[(Mono.one, c)], 0⟩

def mono (m : Mono) (c : ℚ) : TM := ⟨[(m, c)], 0⟩

def zero : TM := ⟨[], 0⟩

/-- Product truncated to nome degree `≤ D`; the dropped part and the remainders go to `r`. -/
def mul (B : Box) (D : ℕ) (T₁ T₂ : TM) : TM :=
  let Q := Poly.mul T₁.P T₂.P
  ⟨Poly.low D Q, Poly.bound B (Poly.high D Q) + T₁.r * (Poly.bound B T₂.P + T₂.r) +
    Poly.bound B T₁.P * T₂.r⟩

variable {B : Box} {S : Env → Prop}

theorem approx_add {T₁ T₂ : TM} {f g : Env → ℝ} (h₁ : T₁.Approx B S f) (h₂ : T₂.Approx B S g) :
    (add T₁ T₂).Approx B S (fun e => f e + g e) := by
  intro e he hs
  simp only [add, Poly.eval_merge]
  push_cast
  calc |f e + g e - (T₁.P.eval e + T₂.P.eval e)|
      = |(f e - T₁.P.eval e) + (g e - T₂.P.eval e)| := by ring_nf
    _ ≤ |f e - T₁.P.eval e| + |g e - T₂.P.eval e| := abs_add_le _ _
    _ ≤ _ := add_le_add (h₁ e he hs) (h₂ e he hs)

theorem approx_scale (c : ℚ) {T : TM} {f : Env → ℝ} (h : T.Approx B S f) :
    (scale c T).Approx B S (fun e => c * f e) := by
  intro e he hs
  simp only [scale, Poly.eval_scale]
  push_cast
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (h e he hs) (abs_nonneg _)

theorem approx_sub {T₁ T₂ : TM} {f g : Env → ℝ} (h₁ : T₁.Approx B S f) (h₂ : T₂.Approx B S g) :
    (sub T₁ T₂).Approx B S (fun e => f e - g e) := by
  intro e he hs
  have h := approx_add h₁ (approx_scale (-1) h₂) e he hs
  have hfg : f e + ((-1 : ℚ) : ℝ) * g e = f e - g e := by push_cast; ring
  dsimp only at h ⊢
  rw [hfg] at h
  exact h

theorem approx_const (c : ℚ) : (const c).Approx B S (fun _ => c) := by
  intro e _ _
  simp [const, Mono.eval_one]

theorem approx_mono (m : Mono) (c : ℚ) : (mono m c).Approx B S (fun e => c * m.eval e) := by
  intro e _ _
  simp [mono]

theorem approx_zero : zero.Approx B S (fun _ => 0) := by
  intro e _ _
  simp [zero]

theorem approx_congr {T : TM} {f g : Env → ℝ} (h : T.Approx B S f)
    (hfg : ∀ e, B.Mem e → S e → f e = g e) : T.Approx B S g := by
  intro e he hs
  rw [← hfg e he hs]
  exact h e he hs

theorem approx_mul (hB : B.Valid) (D : ℕ) {T₁ T₂ : TM} {f g : Env → ℝ}
    (h₁ : T₁.Approx B S f) (h₂ : T₂.Approx B S g) :
    (mul B D T₁ T₂).Approx B S (fun e => f e * g e) := by
  intro e he hs
  have hB' := hB
  obtain ⟨_, _, _, ht0, hp0, _⟩ := hB'
  have he' := he
  obtain ⟨_, _, _, _, _, _, ht1, _, hp1, _, _, _⟩ := he'
  have ht : e.t ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast ht0) ht1).ne'
  have hp : e.p ≠ 0 := (lt_of_lt_of_le (by exact_mod_cast hp0) hp1).ne'
  have hsplit := Poly.eval_low_add_high D (Poly.mul T₁.P T₂.P) e
  rw [Poly.eval_mul _ _ _ ht hp] at hsplit
  have e1 := h₁ e he hs
  have e2 := h₂ e he hs
  have b1 := Poly.abs_eval_le hB he T₁.P
  have b2 := Poly.abs_eval_le hB he T₂.P
  have bh := Poly.abs_eval_le hB he (Poly.high D (Poly.mul T₁.P T₂.P))
  have hr1 : 0 ≤ (T₁.r : ℝ) := le_trans (abs_nonneg _) e1
  have hg : |g e| ≤ (Poly.bound B T₂.P : ℝ) + T₂.r := by
    calc |g e| = |(g e - T₂.P.eval e) + T₂.P.eval e| := by ring_nf
      _ ≤ |g e - T₂.P.eval e| + |T₂.P.eval e| := abs_add_le _ _
      _ ≤ T₂.r + Poly.bound B T₂.P := add_le_add e2 b2
      _ = _ := by ring
  simp only [mul]
  push_cast
  have key : f e * g e - (Poly.low D (Poly.mul T₁.P T₂.P)).eval e =
      (f e - T₁.P.eval e) * g e + T₁.P.eval e * (g e - T₂.P.eval e) +
        (Poly.high D (Poly.mul T₁.P T₂.P)).eval e := by
    linarith [hsplit]
  rw [key]
  calc |(f e - T₁.P.eval e) * g e + T₁.P.eval e * (g e - T₂.P.eval e) +
        (Poly.high D (Poly.mul T₁.P T₂.P)).eval e|
      ≤ |f e - T₁.P.eval e| * |g e| + |T₁.P.eval e| * |g e - T₂.P.eval e| +
          |(Poly.high D (Poly.mul T₁.P T₂.P)).eval e| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
        rw [abs_mul, abs_mul]
    _ ≤ T₁.r * ((Poly.bound B T₂.P : ℝ) + T₂.r) + (Poly.bound B T₁.P : ℝ) * T₂.r +
          (Poly.bound B (Poly.high D (Poly.mul T₁.P T₂.P)) : ℝ) := by
        gcongr
        · exact le_trans (abs_nonneg _) b1
    _ = _ := by ring

end TM

/-! ## Divided-difference Taylor models -/

/-- `(value in the a-version, value in the b-version, divided difference)`. -/
structure DD where
  A : TM
  B : TM
  D : TM

namespace DD

/-- `X` approximates the pair `fa, fb` and the divided difference `(fb − fa)/(b − a)`.
The divided difference is only asked off the diagonal `a = b`. -/
def Approx (Bx : Box) (S : Env → Prop) (X : DD) (fa fb : Env → ℝ) : Prop :=
  X.A.Approx Bx S fa ∧ X.B.Approx Bx S fb ∧
    X.D.Approx Bx (fun e => S e ∧ e.a ≠ e.b) (fun e => (fb e - fa e) / (e.b - e.a))

def add (X Y : DD) : DD := ⟨X.A.add Y.A, X.B.add Y.B, X.D.add Y.D⟩

def sub (X Y : DD) : DD := ⟨X.A.sub Y.A, X.B.sub Y.B, X.D.sub Y.D⟩

def scale (c : ℚ) (X : DD) : DD := ⟨X.A.scale c, X.B.scale c, X.D.scale c⟩

/-- Product rule: `(fg)[a,b] = f[a,b]·g(b) + f(a)·g[a,b]`. -/
def mul (Bx : Box) (Dg : ℕ) (X Y : DD) : DD :=
  ⟨TM.mul Bx Dg X.A Y.A, TM.mul Bx Dg X.B Y.B,
    (TM.mul Bx Dg X.D Y.B).add (TM.mul Bx Dg X.A Y.D)⟩

/-- A quantity that does not change with the `z`-side nome (τ-side or constant). -/
def tau (T : TM) : DD := ⟨T, T, TM.zero⟩

variable {Bx : Box} {S : Env → Prop}

theorem approx_mono_S {T : TM} {S S' : Env → Prop} {f : Env → ℝ} (h : T.Approx Bx S f)
    (hS : ∀ e, S' e → S e) : T.Approx Bx S' f :=
  fun e he hs => h e he (hS e hs)

theorem approx_add {X Y : DD} {fa fb ga gb : Env → ℝ} (hX : X.Approx Bx S fa fb)
    (hY : Y.Approx Bx S ga gb) :
    (add X Y).Approx Bx S (fun e => fa e + ga e) (fun e => fb e + gb e) := by
  refine ⟨TM.approx_add hX.1 hY.1, TM.approx_add hX.2.1 hY.2.1, ?_⟩
  refine TM.approx_congr (TM.approx_add hX.2.2 hY.2.2) fun e _ _ => ?_
  ring

theorem approx_sub {X Y : DD} {fa fb ga gb : Env → ℝ} (hX : X.Approx Bx S fa fb)
    (hY : Y.Approx Bx S ga gb) :
    (sub X Y).Approx Bx S (fun e => fa e - ga e) (fun e => fb e - gb e) := by
  refine ⟨TM.approx_sub hX.1 hY.1, TM.approx_sub hX.2.1 hY.2.1, ?_⟩
  refine TM.approx_congr (TM.approx_sub hX.2.2 hY.2.2) fun e _ _ => ?_
  ring

theorem approx_scale (c : ℚ) {X : DD} {fa fb : Env → ℝ} (hX : X.Approx Bx S fa fb) :
    (scale c X).Approx Bx S (fun e => c * fa e) (fun e => c * fb e) := by
  refine ⟨TM.approx_scale c hX.1, TM.approx_scale c hX.2.1, ?_⟩
  refine TM.approx_congr (TM.approx_scale c hX.2.2) fun e _ _ => ?_
  ring

theorem approx_mul (hB : Bx.Valid) (Dg : ℕ) {X Y : DD} {fa fb ga gb : Env → ℝ}
    (hX : X.Approx Bx S fa fb) (hY : Y.Approx Bx S ga gb) :
    (mul Bx Dg X Y).Approx Bx S (fun e => fa e * ga e) (fun e => fb e * gb e) := by
  refine ⟨TM.approx_mul hB Dg hX.1 hY.1, TM.approx_mul hB Dg hX.2.1 hY.2.1, ?_⟩
  have h1 := TM.approx_mul hB Dg hX.2.2
    (approx_mono_S hY.2.1 (S' := fun e => S e ∧ e.a ≠ e.b) fun e h => h.1)
  have h2 := TM.approx_mul hB Dg (approx_mono_S hX.1 (S' := fun e => S e ∧ e.a ≠ e.b)
    fun e h => h.1) hY.2.2
  refine TM.approx_congr (TM.approx_add h1 h2) fun e _ _ => ?_
  ring

theorem approx_tau {T : TM} {f : Env → ℝ} (h : T.Approx Bx S f) :
    (tau T).Approx Bx S f f := by
  refine ⟨h, h, ?_⟩
  refine TM.approx_congr TM.approx_zero fun e _ _ => ?_
  simp

end DD

end E8Leech.Taylor
