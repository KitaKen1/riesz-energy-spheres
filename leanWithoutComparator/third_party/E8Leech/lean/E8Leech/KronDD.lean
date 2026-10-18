import E8Leech.KronFun
import E8Leech.TaylorModelLogDD

/-!
# Divided-difference triples of Taylor models with majorants

`MDD` is the triple (value in the `a`-version, value in the `b`-version, divided difference
`(f_b − f_a)/(b − a)`) of `KronMajorant` models. The product rule and the logarithm are those of
`TaylorModelOps` and `TaylorModelLogDD`, with polynomial majorants instead of radii. The
logarithm is scaled by `Λ` so that all coefficients are integers.
-/

namespace E8Leech.Kron

/-- `(value in the a-version, value in the b-version, divided difference)`. -/
structure MDD where
  A : MTM
  B : MTM
  D : MTM
  deriving DecidableEq

namespace MDD

/-- `X` approximates the pair `fa, fb` and, off the diagonal `a = b`, their divided
difference. -/
def Approx (Bx : Bounds) (S : NEnv → Prop) (X : MDD) (fa fb : NEnv → ℝ) : Prop :=
  X.A.Approx Bx S fa ∧ X.B.Approx Bx S fb ∧
    X.D.Approx Bx (fun e => S e ∧ e.a ≠ e.b) (fun e => (fb e - fa e) / (e.b - e.a))

def zero : MDD := ⟨MTM.zero, MTM.zero, MTM.zero⟩

def add (X Y : MDD) : MDD := ⟨X.A.add Y.A, X.B.add Y.B, X.D.add Y.D⟩

def sub (X Y : MDD) : MDD := ⟨X.A.sub Y.A, X.B.sub Y.B, X.D.sub Y.D⟩

def scale (c : ℤ) (X : MDD) : MDD := ⟨X.A.scale c, X.B.scale c, X.D.scale c⟩

/-- Product rule: `(fg)[a,b] = f[a,b]·g(b) + f(a)·g[a,b]`. -/
def mul (Bx : Bounds) (D Dcap : ℕ) (X Y : MDD) : MDD :=
  ⟨MTM.mul Bx D Dcap X.A Y.A, MTM.mul Bx D Dcap X.B Y.B,
    (MTM.mul Bx D Dcap X.D Y.B).add (MTM.mul Bx D Dcap X.A Y.D)⟩

/-- A quantity that does not depend on the `z`-side nome. -/
def tau (T : MTM) : MDD := ⟨T, T, MTM.zero⟩

variable {Bx : Bounds} {S : NEnv → Prop}

theorem approx_zero : zero.Approx Bx S (fun _ => 0) (fun _ => 0) := by
  refine ⟨MTM.approx_zero, MTM.approx_zero, ?_⟩
  exact MTM.approx_congr MTM.approx_zero fun e _ _ => by simp

theorem approx_add {X Y : MDD} {fa fb ga gb : NEnv → ℝ} (hX : X.Approx Bx S fa fb)
    (hY : Y.Approx Bx S ga gb) :
    (add X Y).Approx Bx S (fun e => fa e + ga e) (fun e => fb e + gb e) := by
  refine ⟨MTM.approx_add hX.1 hY.1, MTM.approx_add hX.2.1 hY.2.1, ?_⟩
  refine MTM.approx_congr (MTM.approx_add hX.2.2 hY.2.2) fun e _ _ => ?_
  ring

theorem approx_sub {X Y : MDD} {fa fb ga gb : NEnv → ℝ} (hX : X.Approx Bx S fa fb)
    (hY : Y.Approx Bx S ga gb) :
    (sub X Y).Approx Bx S (fun e => fa e - ga e) (fun e => fb e - gb e) := by
  refine ⟨MTM.approx_sub hX.1 hY.1, MTM.approx_sub hX.2.1 hY.2.1, ?_⟩
  refine MTM.approx_congr (MTM.approx_sub hX.2.2 hY.2.2) fun e _ _ => ?_
  ring

theorem approx_scale (c : ℤ) {X : MDD} {fa fb : NEnv → ℝ} (hX : X.Approx Bx S fa fb) :
    (scale c X).Approx Bx S (fun e => c * fa e) (fun e => c * fb e) := by
  refine ⟨MTM.approx_scale c hX.1, MTM.approx_scale c hX.2.1, ?_⟩
  refine MTM.approx_congr (MTM.approx_scale c hX.2.2) fun e _ _ => ?_
  ring

theorem approx_mul (hB : Bx.Valid) (D Dcap : ℕ) {X Y : MDD} {fa fb ga gb : NEnv → ℝ}
    (hX : X.Approx Bx S fa fb) (hY : Y.Approx Bx S ga gb) :
    (mul Bx D Dcap X Y).Approx Bx S (fun e => fa e * ga e) (fun e => fb e * gb e) := by
  have hS : ∀ e, (S e ∧ e.a ≠ e.b) → S e := fun e h => h.1
  refine ⟨MTM.approx_mul hB D Dcap hX.1 hY.1, MTM.approx_mul hB D Dcap hX.2.1 hY.2.1, ?_⟩
  have h1 := MTM.approx_mul hB D Dcap hX.2.2 (MTM.approx_mono_S hY.2.1 hS)
  have h2 := MTM.approx_mul hB D Dcap (MTM.approx_mono_S hX.1 hS) hY.2.2
  refine MTM.approx_congr (MTM.approx_add h1 h2) fun e _ _ => ?_
  ring

theorem approx_tau {T : MTM} {f : NEnv → ℝ} (h : T.Approx Bx S f) : (tau T).Approx Bx S f f := by
  refine ⟨h, h, ?_⟩
  exact MTM.approx_congr MTM.approx_zero fun e _ _ => by simp

theorem approx_congr {X : MDD} {fa fb ga gb : NEnv → ℝ} (h : X.Approx Bx S fa fb)
    (ha : ∀ e, Bx.Mem e → S e → ga e = fa e) (hb : ∀ e, Bx.Mem e → S e → gb e = fb e) :
    X.Approx Bx S ga gb := by
  refine ⟨MTM.approx_congr h.1 ha, MTM.approx_congr h.2.1 hb, ?_⟩
  refine MTM.approx_congr h.2.2 fun e he hs => ?_
  rw [ha e he hs.1, hb e he hs.1]

/-- `b − a` as an exact model. -/
def bmaMTM : MTM := ⟨[(⟨0, 1, 0, 0, 0⟩, 1), (⟨1, 0, 0, 0, 0⟩, -1)], []⟩

theorem approx_bma : bmaMTM.Approx Bx S (fun e => e.b - e.a) := by
  intro e _ _
  have h : IPoly.eval bmaMTM.P e = e.b - e.a := by
    simp only [bmaMTM, IPoly.eval_cons, IPoly.eval_nil, NMono.eval, pow_zero, pow_one, mul_one,
      one_mul]
    push_cast
    ring
  rw [h]
  simp [bmaMTM]

/-- The triple of `Λ log f`. -/
def log (Bx : Bounds) (D Dcap Λ n K : ℕ) (X : MDD) : MDD :=
  ⟨MTM.log1p Bx D Dcap Λ n (X.A.sub (MTM.const 1)), MTM.log1p Bx D Dcap Λ n (X.B.sub (MTM.const 1)),
    MTM.mul Bx D Dcap (MTM.mul Bx D Dcap X.D (MTM.inv1p Bx D Dcap K (X.A.sub (MTM.const 1))))
      (MTM.logRatio Bx D Dcap Λ n (MTM.mul Bx D Dcap bmaMTM
        (MTM.mul Bx D Dcap X.D (MTM.inv1p Bx D Dcap K (X.A.sub (MTM.const 1))))))⟩

/-- The model of `z = (f_b − f_a)/f_a` used inside `MDD.log`. -/
def logZ (Bx : Bounds) (D Dcap K : ℕ) (X : MDD) : MTM :=
  MTM.mul Bx D Dcap bmaMTM (MTM.mul Bx D Dcap X.D (MTM.inv1p Bx D Dcap K (X.A.sub (MTM.const 1))))

/-- The three smallness checks of `MDD.log`. -/
def LogOK (Bx : Bounds) (D Dcap K : ℕ) (X : MDD) : Prop :=
  MTM.HalfOK Bx (X.A.sub (MTM.const 1)) ∧ MTM.HalfOK Bx (X.B.sub (MTM.const 1)) ∧
    MTM.HalfOK Bx (logZ Bx D Dcap K X)

instance (Bx : Bounds) (D Dcap K : ℕ) (X : MDD) : Decidable (LogOK Bx D Dcap K X) := by
  unfold LogOK
  infer_instance

/-- A function within `1/2` of `1` is positive. -/
theorem pos_of_halfOK (hB : Bx.Valid) {T : MTM} {f : NEnv → ℝ}
    (hT : T.Approx Bx S (fun e => f e - ((1 : ℤ) : ℝ))) (hG : MTM.HalfOK Bx T) {e : NEnv}
    (he : Bx.Mem e) (hs : S e) : 0 < f e := by
  have h1 := MTM.abs_le_absMaj hB hT he hs
  have h2 := MTM.absMaj_le_half hB hG he
  have h3 := neg_abs_le (f e - ((1 : ℤ) : ℝ))
  push_cast at h1 h3
  linarith

theorem approx_log (hB : Bx.Valid) (D Dcap : ℕ) {Λ n : ℕ} (K : ℕ)
    (hΛ : ∀ i, i < n → (i + 1) ∣ Λ) {X : MDD} {fa fb : NEnv → ℝ} (hX : X.Approx Bx S fa fb)
    (hOK : LogOK Bx D Dcap K X) :
    (log Bx D Dcap Λ n K X).Approx Bx S (fun e => (Λ : ℝ) * Real.log (fa e))
      (fun e => (Λ : ℝ) * Real.log (fb e)) := by
  obtain ⟨hGa, hGb, hZ⟩ := hOK
  have hga := MTM.approx_sub hX.1 (MTM.approx_const (B := Bx) (S := S) 1)
  have hgb := MTM.approx_sub hX.2.1 (MTM.approx_const (B := Bx) (S := S) 1)
  refine ⟨?_, ?_, ?_⟩
  · refine MTM.approx_congr (MTM.approx_log1p hB D Dcap hΛ hga hGa) fun e _ _ => ?_
    push_cast
    ring_nf
  · refine MTM.approx_congr (MTM.approx_log1p hB D Dcap hΛ hgb hGb) fun e _ _ => ?_
    push_cast
    ring_nf
  · have hS : ∀ e, (S e ∧ e.a ≠ e.b) → S e := fun e h => h.1
    have hinv := MTM.approx_inv1p hB D Dcap K (MTM.approx_mono_S hga hS) hGa
    have hq := MTM.approx_mul hB D Dcap hX.2.2 hinv
    have hz := MTM.approx_mul hB D Dcap
      (approx_bma (Bx := Bx) (S := fun e => S e ∧ e.a ≠ e.b)) hq
    have hL := MTM.approx_logRatio hB D Dcap hΛ hz hZ
    have hD := MTM.approx_mul hB D Dcap hq hL
    refine MTM.approx_congr hD fun e he hs => ?_
    have h1 : 1 + (fa e - ((1 : ℤ) : ℝ)) = fa e := by push_cast; ring
    simp only [h1]
    have hid := Taylor.logRatio_identity hs.2 (pos_of_halfOK hB hga hGa he hs.1)
      (pos_of_halfOK hB hgb hGb he hs.1)
    linear_combination (-(Λ : ℝ)) * hid

end MDD

end E8Leech.Kron
