import E8Leech.TaylorModelFun

/-!
# The divided-difference Taylor model of `log f`

From a triple for a positive function `f ≈ 1`, the triple for `log f` is

* `log f(a) = log1p (f(a) − 1)`, `log f(b) = log1p (f(b) − 1)`,
* `(log f(b) − log f(a))/(b − a) = q · L(z)` with `q = f[a,b]/f(a)`, `z = (b − a) q` and
  `L(z) = log(1 + z)/z`.

No derivative of `log f` is needed; the divided difference of `f` and two scalar series suffice.
-/

namespace E8Leech.Taylor

/-- `b − a` as an exact Taylor model. -/
def bmaTM : TM := ⟨[(⟨0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 0, 0, 0, 0⟩, -1)], 0⟩

theorem approx_bma {B : Box} {S : Env → Prop} : bmaTM.Approx B S (fun e => e.b - e.a) := by
  intro e _ _
  have h : Poly.eval bmaTM.P e = e.b - e.a := by
    simp only [bmaTM, Poly.eval_cons, Poly.eval_nil, Mono.eval, zpow_zero, pow_zero, pow_one,
      mul_one, one_mul]
    push_cast
    ring
  show |e.b - e.a - Poly.eval bmaTM.P e| ≤ ((bmaTM.r : ℚ) : ℝ)
  rw [h]
  simp [bmaTM]

theorem logRatio_identity {a b fa fb : ℝ} (hab : a ≠ b) (hfa : 0 < fa) (hfb : 0 < fb) :
    (fb - fa) / (b - a) * (1 / fa) * TM.logRatio ((b - a) * ((fb - fa) / (b - a) * (1 / fa))) =
      (Real.log fb - Real.log fa) / (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hz : (b - a) * ((fb - fa) / (b - a) * (1 / fa)) = (fb - fa) / fa := by
    field_simp
  rw [hz]
  by_cases hd : fb - fa = 0
  · have : fb = fa := by linarith
    subst this
    simp
  · have hz0 : (fb - fa) / fa ≠ 0 := div_ne_zero hd hfa.ne'
    rw [TM.logRatio, if_neg hz0]
    have h1 : 1 + (fb - fa) / fa = fb / fa := by field_simp; ring
    rw [h1, Real.log_div hfb.ne' hfa.ne']
    field_simp

namespace DD

/-- The triple of `log f`. -/
def log (B : Box) (Dg n K : ℕ) (X : DD) : DD :=
  let ga := X.A.sub (TM.const 1)
  let gb := X.B.sub (TM.const 1)
  let q := TM.mul B Dg X.D (TM.inv1p B Dg K ga)
  let z := TM.mul B Dg bmaTM q
  ⟨TM.log1p B Dg n ga, TM.log1p B Dg n gb, TM.mul B Dg q (TM.logRatioTM B Dg n z)⟩

/-- The `z`-model used inside `DD.log` (for checking `|z| < 1`). -/
def logZ (B : Box) (Dg K : ℕ) (X : DD) : TM :=
  TM.mul B Dg bmaTM (TM.mul B Dg X.D (TM.inv1p B Dg K (X.A.sub (TM.const 1))))

theorem approx_log {B : Box} (hB : B.Valid) (Dg n K : ℕ) {S : Env → Prop} {X : DD}
    {fa fb : Env → ℝ} (hX : X.Approx B S fa fb)
    (hfa : ∀ e, B.Mem e → S e → 0 < fa e) (hfb : ∀ e, B.Mem e → S e → 0 < fb e)
    (hGa : TM.absBound B (X.A.sub (TM.const 1)) < 1)
    (hGb : TM.absBound B (X.B.sub (TM.const 1)) < 1)
    (hZ : TM.absBound B (logZ B Dg K X) < 1) :
    (log B Dg n K X).Approx B S (fun e => Real.log (fa e)) (fun e => Real.log (fb e)) := by
  have hga := TM.approx_sub hX.1 (TM.approx_const (B := B) (S := S) 1)
  have hgb := TM.approx_sub hX.2.1 (TM.approx_const (B := B) (S := S) 1)
  refine ⟨?_, ?_, ?_⟩
  · refine TM.approx_congr (TM.approx_log1p hB Dg n hga hGa) fun e _ _ => ?_
    push_cast
    ring_nf
  · refine TM.approx_congr (TM.approx_log1p hB Dg n hgb hGb) fun e _ _ => ?_
    push_cast
    ring_nf
  · set S' : Env → Prop := fun e => S e ∧ e.a ≠ e.b
    have hga' : (X.A.sub (TM.const 1)).Approx B S' (fun e => fa e - ((1 : ℚ) : ℝ)) :=
      approx_mono_S hga fun e h => h.1
    have hinv := TM.approx_inv1p hB Dg K hga' hGa
    have hq := TM.approx_mul hB Dg hX.2.2 hinv
    have hz := TM.approx_mul hB Dg approx_bma hq
    have hL := TM.approx_logRatio hB Dg n hz hZ
    have hD := TM.approx_mul hB Dg hq hL
    refine TM.approx_congr hD fun e he hs => ?_
    have h1 : 1 + (fa e - ((1 : ℚ) : ℝ)) = fa e := by push_cast; ring
    simp only [h1]
    exact logRatio_identity hs.2 (hfa e he hs.1) (hfb e he hs.1)

end DD

end E8Leech.Taylor
