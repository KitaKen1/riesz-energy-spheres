import E8Leech.KronPivot
import E8Leech.ExpBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cells in reciprocal coordinates and cover trees

With `x = 1/(πu)` the nome of `iu` is `exp (−1/x)`, without `π`. A rectangle of reciprocal
parameters with rational endpoints therefore has certified rational nome bounds from `expNegLo`
and `expNegHi`; the lower endpoint `0` (that is, `u = ∞`) is allowed and gives the nome bound `0`.

* `recNEnv`: the environment `(e^{−1/x}, e^{−1/y}, x, y, log 2)` of two reciprocal parameters.
  `recNEnvS`: the same with the constant `1/π` in the fourth slot, for forms in which the second
  variable has been inverted and no longer carries a reciprocal.
* `CellOK`, `CellOKS`: a cell encloses the image of a rectangle; `CellOK.mem`, `CellOKS.mem`.
* `Cover`: a binary tree of splits whose leaves are cells or the excluded corner.
  `Cover.sound`: a successful check proves a leafwise property on the whole rectangle, outside the
  corner.
-/

namespace E8Leech.Kron

open scoped Real

/-- The environment of the reciprocal axis parameters `x = 1/(πu)` and `y = 1/(πt)`. -/
noncomputable def recNEnv (x y : ℝ) : NEnv :=
  ⟨Real.exp (-x⁻¹), Real.exp (-y⁻¹), x, y, Real.log 2⟩

/-- The environment with the constant `1/π` in place of the second reciprocal parameter. -/
noncomputable def recNEnvS (x y : ℝ) : NEnv :=
  ⟨Real.exp (-x⁻¹), Real.exp (-y⁻¹), x, 1 / π, Real.log 2⟩

/-- Certified bounds `aln/ald ≤ exp (−1/x) ≤ ahn/ahd` on `lo ≤ x ≤ hi`. A zero lower bound
needs no evaluation, so `lo = 0` is allowed. The upper bound is evaluated at `min (1/hi) 2ᵏ`,
so tiny `hi` cost nothing extra. -/
def NomeOK (k n : ℕ) (lo hi : ℚ) (aln ald ahn ahd : ℕ) : Prop :=
  0 < n ∧ 0 < hi ∧ expNegHi (min hi⁻¹ (2 ^ k)) k n * ahd ≤ ahn ∧
    (aln = 0 ∨ (0 < lo ∧ lo⁻¹ ≤ 2 ^ k ∧ (aln : ℚ) ≤ expNegLo lo⁻¹ k n * ald))

instance (k n : ℕ) (lo hi : ℚ) (aln ald ahn ahd : ℕ) :
    Decidable (NomeOK k n lo hi aln ald ahn ahd) := by
  unfold NomeOK
  infer_instance

theorem NomeOK.bounds {k n : ℕ} {lo hi : ℚ} {aln ald ahn ahd : ℕ}
    (h : NomeOK k n lo hi aln ald ahn ahd) {x : ℝ} (hx : 0 < x) (hlo : (lo : ℝ) ≤ x)
    (hhi : x ≤ hi) :
    (aln : ℝ) ≤ Real.exp (-x⁻¹) * ald ∧ Real.exp (-x⁻¹) * ahd ≤ ahn := by
  obtain ⟨hn, hhi0, hH, hL⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hL with h0 | ⟨hlo0, hk', hL⟩
    · rw [h0, Nat.cast_zero]
      exact mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)
    · have hloR : (0 : ℝ) < lo := by exact_mod_cast hlo0
      have hb := (expNeg_bounds (y := lo⁻¹) (inv_nonneg.mpr hlo0.le) hk' hn).1
      have hmono : Real.exp (-((lo⁻¹ : ℚ) : ℝ)) ≤ Real.exp (-x⁻¹) := by
        apply Real.exp_le_exp.mpr
        rw [Rat.cast_inv]
        exact neg_le_neg (inv_anti₀ hloR hlo)
      have hLr : ((aln : ℚ) : ℝ) ≤ ((expNegLo lo⁻¹ k n * ald : ℚ) : ℝ) := Rat.cast_le.mpr hL
      rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast] at hLr
      exact hLr.trans (mul_le_mul_of_nonneg_right (hb.trans hmono) (Nat.cast_nonneg _))
  · have hy0 : (0 : ℚ) ≤ min hi⁻¹ (2 ^ k) := le_min (inv_nonneg.mpr hhi0.le) (by positivity)
    have hb := (expNeg_bounds (y := min hi⁻¹ (2 ^ k)) hy0 (min_le_right _ _) hn).2
    have hmono : Real.exp (-x⁻¹) ≤ Real.exp (-((min hi⁻¹ (2 ^ k) : ℚ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h1 : ((min hi⁻¹ (2 ^ k) : ℚ) : ℝ) ≤ ((hi⁻¹ : ℚ) : ℝ) :=
        Rat.cast_le.mpr (min_le_left _ _)
      rw [Rat.cast_inv] at h1
      exact neg_le_neg (h1.trans (inv_anti₀ hx hhi))
    have hHr : ((expNegHi (min hi⁻¹ (2 ^ k)) k n * ahd : ℚ) : ℝ) ≤ ((ahn : ℚ) : ℝ) :=
      Rat.cast_le.mpr hH
    rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast] at hHr
    exact (mul_le_mul_of_nonneg_right (hmono.trans hb) (Nat.cast_nonneg _)).trans hHr

/-- Rational bounds `uln/uld ≤ x ≤ uhn/uhd` on `lo ≤ x ≤ hi`. -/
def VarOK (lo hi : ℚ) (uln uld uhn uhd : ℕ) : Prop := (uln : ℚ) ≤ lo * uld ∧ hi * uhd ≤ uhn

instance (lo hi : ℚ) (uln uld uhn uhd : ℕ) : Decidable (VarOK lo hi uln uld uhn uhd) := by
  unfold VarOK
  infer_instance

theorem VarOK.bounds {lo hi : ℚ} {uln uld uhn uhd : ℕ} (h : VarOK lo hi uln uld uhn uhd) {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) : (uln : ℝ) ≤ x * uld ∧ x * uhd ≤ uhn := by
  obtain ⟨hul, huh⟩ := h
  have h1 : ((uln : ℚ) : ℝ) ≤ ((lo * uld : ℚ) : ℝ) := Rat.cast_le.mpr hul
  have h2 : ((hi * uhd : ℚ) : ℝ) ≤ ((uhn : ℚ) : ℝ) := Rat.cast_le.mpr huh
  rw [Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast] at h1 h2
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg _)),
    (mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg _)).trans h2⟩

/-- The bounds of `log 2` of a cell contain the interval of Mathlib. -/
def LogTwoOK (C : Cell) : Prop :=
  C.lo.ln * 10000000000 ≤ 6931471803 * C.lo.ld ∧ 6931471808 * C.hi.ld ≤ C.hi.ln * 10000000000

instance (C : Cell) : Decidable (LogTwoOK C) := by
  unfold LogTwoOK
  infer_instance

theorem LogTwoOK.bounds {C : Cell} (h : LogTwoOK C) :
    (C.lo.ln : ℝ) ≤ Real.log 2 * C.lo.ld ∧ Real.log 2 * C.hi.ld ≤ C.hi.ln := by
  obtain ⟨hl0, hl1⟩ := h
  have hlogL : (6931471803 / 10000000000 : ℝ) < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  have hlogH : Real.log 2 < (6931471808 / 10000000000 : ℝ) :=
    lt_of_lt_of_eq Real.log_two_lt_d9 (by norm_num)
  have h3 : ((10000000000 : ℕ) : ℝ) = 10000000000 := by norm_num
  constructor
  · have h1 : ((C.lo.ln * 10000000000 : ℕ) : ℝ) ≤ ((6931471803 * C.lo.ld : ℕ) : ℝ) := by
      exact_mod_cast hl0
    rw [Nat.cast_mul, Nat.cast_mul] at h1
    have h2 : (6931471803 / 10000000000 : ℝ) * C.lo.ld ≤ Real.log 2 * C.lo.ld :=
      mul_le_mul_of_nonneg_right hlogL.le (Nat.cast_nonneg _)
    have h4 : ((6931471803 : ℕ) : ℝ) = 6931471803 := by norm_num
    rw [h3, h4] at h1
    linarith
  · have h1 : ((6931471808 * C.hi.ld : ℕ) : ℝ) ≤ ((C.hi.ln * 10000000000 : ℕ) : ℝ) := by
      exact_mod_cast hl1
    rw [Nat.cast_mul, Nat.cast_mul] at h1
    have h2 : Real.log 2 * C.hi.ld ≤ (6931471808 / 10000000000 : ℝ) * C.hi.ld :=
      mul_le_mul_of_nonneg_right hlogH.le (Nat.cast_nonneg _)
    have h4 : ((6931471808 : ℕ) : ℝ) = 6931471808 := by norm_num
    rw [h3, h4] at h1
    linarith

/-- The fourth-slot bounds of a cell contain `1/π` (six decimals of `π`). -/
def InvPiOK (C : Cell) : Prop :=
  C.lo.tn * 3141593 ≤ 1000000 * C.lo.td ∧ 1000000 * C.hi.td ≤ C.hi.tn * 3141592

instance (C : Cell) : Decidable (InvPiOK C) := by
  unfold InvPiOK
  infer_instance

theorem InvPiOK.bounds {C : Cell} (h : InvPiOK C) :
    (C.lo.tn : ℝ) ≤ 1 / π * C.lo.td ∧ 1 / π * C.hi.td ≤ C.hi.tn := by
  obtain ⟨h0, h1⟩ := h
  have hπ := Real.pi_pos
  have hpL : (3141592 / 1000000 : ℝ) < π := lt_of_eq_of_lt (by norm_num) Real.pi_gt_d6
  have hpH : π < (3141593 / 1000000 : ℝ) := lt_of_lt_of_eq Real.pi_lt_d6 (by norm_num)
  constructor
  · have k : ((C.lo.tn * 3141593 : ℕ) : ℝ) ≤ ((1000000 * C.lo.td : ℕ) : ℝ) := by
      exact_mod_cast h0
    rw [Nat.cast_mul, Nat.cast_mul] at k
    have e1 : ((3141593 : ℕ) : ℝ) = 3141593 := by norm_num
    have e2 : ((1000000 : ℕ) : ℝ) = 1000000 := by norm_num
    rw [e1, e2] at k
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hπ]
    have hn : (0 : ℝ) ≤ C.lo.tn := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hpH.le)]
  · have k : ((1000000 * C.hi.td : ℕ) : ℝ) ≤ ((C.hi.tn * 3141592 : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_mul, Nat.cast_mul] at k
    have e1 : ((3141592 : ℕ) : ℝ) = 3141592 := by norm_num
    have e2 : ((1000000 : ℕ) : ℝ) = 1000000 := by norm_num
    rw [e1, e2] at k
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hπ]
    have hn : (0 : ℝ) ≤ C.hi.tn := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hpL.le)]

/-- A rectangle `[x₀, x₁] × [y₀, y₁]` of reciprocal parameters with rational endpoints. -/
structure Rect where
  x0 : ℚ
  x1 : ℚ
  y0 : ℚ
  y1 : ℚ

def Rect.Mem (r : Rect) (x y : ℝ) : Prop :=
  (r.x0 : ℝ) ≤ x ∧ x ≤ r.x1 ∧ (r.y0 : ℝ) ≤ y ∧ y ≤ r.y1

instance (C : Cell) : Decidable C.Valid := by
  unfold Cell.Valid
  infer_instance

/-- The cell encloses the image of the rectangle under `recNEnv`. -/
def CellOK (k n : ℕ) (r : Rect) (C : Cell) : Prop :=
  C.Valid ∧ NomeOK k n r.x0 r.x1 C.lo.an C.lo.ad C.hi.an C.hi.ad ∧
    VarOK r.x0 r.x1 C.lo.un C.lo.ud C.hi.un C.hi.ud ∧
    NomeOK k n r.y0 r.y1 C.lo.bn C.lo.bd C.hi.bn C.hi.bd ∧
    VarOK r.y0 r.y1 C.lo.tn C.lo.td C.hi.tn C.hi.td ∧ LogTwoOK C

instance (k n : ℕ) (r : Rect) (C : Cell) : Decidable (CellOK k n r C) := by
  unfold CellOK
  infer_instance

theorem CellOK.mem {k n : ℕ} {r : Rect} {C : Cell} (h : CellOK k n r C) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) (hr : r.Mem x y) : C.Mem (recNEnv x y) := by
  obtain ⟨-, hA, hU, hB, hT, hL⟩ := h
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hr
  obtain ⟨a0, a1⟩ := hA.bounds hx hx0 hx1
  obtain ⟨u0, u1⟩ := hU.bounds hx0 hx1
  obtain ⟨b0, b1⟩ := hB.bounds hy hy0 hy1
  obtain ⟨t0, t1⟩ := hT.bounds hy0 hy1
  obtain ⟨l0, l1⟩ := hL.bounds
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact ⟨a0, b0, u0, t0, l0, (Real.exp_pos _).le, a1, (Real.exp_pos _).le, b1, hx.le, u1, hy.le,
    t1, hlog0, l1⟩

/-- The cell encloses the image of the rectangle under `recNEnvS`. -/
def CellOKS (k n : ℕ) (r : Rect) (C : Cell) : Prop :=
  C.Valid ∧ NomeOK k n r.x0 r.x1 C.lo.an C.lo.ad C.hi.an C.hi.ad ∧
    VarOK r.x0 r.x1 C.lo.un C.lo.ud C.hi.un C.hi.ud ∧
    NomeOK k n r.y0 r.y1 C.lo.bn C.lo.bd C.hi.bn C.hi.bd ∧ InvPiOK C ∧ LogTwoOK C

instance (k n : ℕ) (r : Rect) (C : Cell) : Decidable (CellOKS k n r C) := by
  unfold CellOKS
  infer_instance

theorem CellOKS.mem {k n : ℕ} {r : Rect} {C : Cell} (h : CellOKS k n r C) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hr : r.Mem x y) : C.Mem (recNEnvS x y) := by
  obtain ⟨-, hA, hU, hB, hP, hL⟩ := h
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hr
  obtain ⟨a0, a1⟩ := hA.bounds hx hx0 hx1
  obtain ⟨u0, u1⟩ := hU.bounds hx0 hx1
  obtain ⟨b0, b1⟩ := hB.bounds hy hy0 hy1
  obtain ⟨t0, t1⟩ := hP.bounds
  obtain ⟨l0, l1⟩ := hL.bounds
  have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hπ0 : (0 : ℝ) ≤ 1 / π := by positivity
  exact ⟨a0, b0, u0, t0, l0, (Real.exp_pos _).le, a1, (Real.exp_pos _).le, b1, hx.le, u1, hπ0,
    t1, hlog0, l1⟩

/-! ## Cover trees -/

/-- A binary tree of splits of a rectangle. A leaf is a cell, with two auxiliary rational numbers
for the cell test, or the excluded corner. -/
inductive Cover
  | leaf (C : Cell) (aux₁ aux₂ : ℚ)
  | corner
  | splitX (m : ℚ) (l r : Cover)
  | splitY (m : ℚ) (l r : Cover)

namespace Cover

/-- Every cell leaf passes the enclosure test `cellOK` for its rectangle and the test `ok`;
a corner leaf lies in `x, y ≥ c`. -/
def check (cellOK : Rect → Cell → Bool) (ok : Cell → ℚ → ℚ → Bool) (c : ℚ) :
    Cover → Rect → Bool
  | leaf C aux₁ aux₂, r => cellOK r C && ok C aux₁ aux₂
  | corner, r => decide (c ≤ r.x0 ∧ c ≤ r.y0)
  | splitX m l r', r => check cellOK ok c l ⟨r.x0, m, r.y0, r.y1⟩ &&
      check cellOK ok c r' ⟨m, r.x1, r.y0, r.y1⟩
  | splitY m l r', r => check cellOK ok c l ⟨r.x0, r.x1, r.y0, m⟩ &&
      check cellOK ok c r' ⟨r.x0, r.x1, m, r.y1⟩

/-- The number of cell leaves. -/
def leaves : Cover → ℕ
  | leaf _ _ _ => 1
  | corner => 0
  | splitX _ l r => leaves l + leaves r
  | splitY _ l r => leaves l + leaves r

theorem check_splitX {cellOK : Rect → Cell → Bool} {ok : Cell → ℚ → ℚ → Bool} {c m : ℚ}
    {l r' : Cover}
    {r : Rect} (hl : check cellOK ok c l ⟨r.x0, m, r.y0, r.y1⟩ = true)
    (hr : check cellOK ok c r' ⟨m, r.x1, r.y0, r.y1⟩ = true) :
    check cellOK ok c (splitX m l r') r = true := by
  simp only [check, hl, hr, Bool.and_self]

theorem check_splitY {cellOK : Rect → Cell → Bool} {ok : Cell → ℚ → ℚ → Bool} {c m : ℚ}
    {l r' : Cover}
    {r : Rect} (hl : check cellOK ok c l ⟨r.x0, r.x1, r.y0, m⟩ = true)
    (hr : check cellOK ok c r' ⟨r.x0, r.x1, m, r.y1⟩ = true) :
    check cellOK ok c (splitY m l r') r = true := by
  simp only [check, hl, hr, Bool.and_self]

/-- **Soundness of a cover.** A property of all accepted cells holds on the whole rectangle,
outside the corner `x, y ≥ c`. -/
theorem sound {cellOK : Rect → Cell → Bool} {ok : Cell → ℚ → ℚ → Bool} {c : ℚ}
    {env : ℝ → ℝ → NEnv} {P : ℝ → ℝ → Prop}
    (hcell : ∀ (r : Rect) (C : Cell), cellOK r C = true →
      C.Valid ∧ ∀ x y : ℝ, 0 < x → 0 < y → r.Mem x y → C.Mem (env x y))
    (hleaf : ∀ (C : Cell) (aux₁ aux₂ : ℚ), C.Valid → ok C aux₁ aux₂ = true → ∀ x y : ℝ,
      0 < x → 0 < y → C.Mem (env x y) → P x y) :
    ∀ (cov : Cover) (r : Rect), check cellOK ok c cov r = true → ∀ x y : ℝ, 0 < x → 0 < y →
      r.Mem x y → ((c : ℝ) ≤ x ∧ (c : ℝ) ≤ y) ∨ P x y
  | leaf C aux₁ aux₂, r, h, x, y, hx, hy, hr => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨hV, hmem⟩ := hcell r C h.1
    exact Or.inr (hleaf C aux₁ aux₂ hV h.2 x y hx hy (hmem x y hx hy hr))
  | corner, r, h, x, y, _, _, hr => by
    simp only [check, decide_eq_true_eq] at h
    have h1 : (c : ℝ) ≤ r.x0 := by exact_mod_cast h.1
    have h2 : (c : ℝ) ≤ r.y0 := by exact_mod_cast h.2
    exact Or.inl ⟨h1.trans hr.1, h2.trans hr.2.2.1⟩
  | splitX m l r', r, h, x, y, hx, hy, hr => by
    simp only [check, Bool.and_eq_true] at h
    rcases le_total x (m : ℝ) with hm | hm
    · exact sound hcell hleaf l _ h.1 x y hx hy ⟨hr.1, hm, hr.2.2.1, hr.2.2.2⟩
    · exact sound hcell hleaf r' _ h.2 x y hx hy ⟨hm, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  | splitY m l r', r, h, x, y, hx, hy, hr => by
    simp only [check, Bool.and_eq_true] at h
    rcases le_total y (m : ℝ) with hm | hm
    · exact sound hcell hleaf l _ h.1 x y hx hy ⟨hr.1, hr.2.1, hr.2.2.1, hm⟩
    · exact sound hcell hleaf r' _ h.2 x y hx hy ⟨hr.1, hr.2.1, hm, hr.2.2.2⟩

end Cover

/-- The enclosure test of `recNEnv` as a Boolean. -/
def cellOKb (k n : ℕ) (r : Rect) (C : Cell) : Bool := decide (CellOK k n r C)

theorem cellOKb_spec (k n : ℕ) (r : Rect) (C : Cell) (h : cellOKb k n r C = true) :
    C.Valid ∧ ∀ x y : ℝ, 0 < x → 0 < y → r.Mem x y → C.Mem (recNEnv x y) := by
  have h' : CellOK k n r C := of_decide_eq_true h
  exact ⟨h'.1, fun _ _ hx hy hr => h'.mem hx hy hr⟩

/-- The enclosure test of `recNEnvS` as a Boolean. -/
def cellOKSb (k n : ℕ) (r : Rect) (C : Cell) : Bool := decide (CellOKS k n r C)

theorem cellOKSb_spec (k n : ℕ) (r : Rect) (C : Cell) (h : cellOKSb k n r C = true) :
    C.Valid ∧ ∀ x y : ℝ, 0 < x → 0 < y → r.Mem x y → C.Mem (recNEnvS x y) := by
  have h' : CellOKS k n r C := of_decide_eq_true h
  exact ⟨h'.1, fun _ _ hx hy hr => h'.mem hx hy hr⟩

end E8Leech.Kron
