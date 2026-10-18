import E8Leech.KronFun

/-!
# Sign certificates by factoring out the common nome powers

The divided-difference numerator of the hat kernel has the form `a²b · Q₁ + a³ · Q₂` with
quotients `Q₁, Q₂` of size `O(1)` (and `a³b · Q₁ + a²b² · Q₂` after the modular inversion of the
second variable). A termwise lower bound of the polynomial treats the common factor separately in
every term and loses the sign unless the cell is tiny. `IPoly.divQuot` factors the two pivots
`aⁱ bʲ⁺¹` and `aⁱ⁺¹ bʲ` out of the polynomial part and out of the majorant, and `Cell.PosOK`
compares the quotient margins on a cell. The remainder is a polynomial with the same factors, so cells
may reach the nome `0`: the conclusion only needs `a, b > 0`.

* `Cell`: lower and upper bounds of the five variables.
* `IPoly.evalLB`: a termwise lower bound on a cell.
* `Quots`: the four quotient polynomials, computed once for all cells (`MTM.quots`).
* `MTM.lower_of_divisible`: the lower bound `f ≥ aⁱ bʲ (b · marginB + a · marginA)`.
* `Cell.PosOK`, `Cell.pos_of_posOK`: the sign of `b βB + a βA + γ` on a cell.
* `MTM.pos_of_posOK`: a successful check proves positivity on the cell, also with an extra
  term bounded below by `aⁱ bʲ γ`.
-/

namespace E8Leech.Kron

namespace IPoly

/-- The pivot `a^i b^j` divides the monomial. -/
def divides (i j : ℕ) (m : NMono) : Bool := Nat.ble i m.ea && Nat.ble j m.eb

/-- The quotient by the pivot `a^i b^j` of the terms it divides. -/
def divQuot (i j : ℕ) : IPoly → IPoly
  | [] => []
  | x :: P =>
    bif divides i j x.1 then
      (⟨x.1.ea - i, x.1.eb - j, x.1.eu, x.1.et, x.1.el⟩, x.2) :: divQuot i j P
    else divQuot i j P

/-- The terms not divisible by the pivot. -/
def divRest (i j : ℕ) : IPoly → IPoly
  | [] => []
  | x :: P => bif divides i j x.1 then divRest i j P else x :: divRest i j P

theorem eval_div (i j : ℕ) (P : IPoly) (e : NEnv) :
    eval P e = e.a ^ i * e.b ^ j * eval (divQuot i j P) e + eval (divRest i j P) e := by
  induction P with
  | nil => simp [divQuot, divRest]
  | cons x P ih =>
    cases h : divides i j x.1
    · simp only [divQuot, divRest, h, cond_false, eval_cons]
      rw [ih]
      ring
    · simp only [divQuot, divRest, h, cond_true, eval_cons]
      simp only [divides, Bool.and_eq_true, Nat.ble_eq] at h
      have hm : x.1.eval e = e.a ^ i * e.b ^ j *
          (⟨x.1.ea - i, x.1.eb - j, x.1.eu, x.1.et, x.1.el⟩ : NMono).eval e := by
        simp only [NMono.eval]
        have h1 : e.a ^ x.1.ea = e.a ^ i * e.a ^ (x.1.ea - i) := by
          rw [← pow_add, Nat.add_sub_cancel' h.1]
        have h2 : e.b ^ x.1.eb = e.b ^ j * e.b ^ (x.1.eb - j) := by
          rw [← pow_add, Nat.add_sub_cancel' h.2]
        rw [h1, h2]
        ring
      rw [ih, hm]
      ring

end IPoly

/-! ## Cells -/

/-- Lower bounds `lo` and upper bounds `hi` of the five variables. -/
structure Cell where
  lo : Bounds
  hi : Bounds

namespace Cell

def Valid (C : Cell) : Prop := C.lo.Valid ∧ C.hi.Valid

/-- The variables lie between the lower and the upper bounds. -/
def Mem (C : Cell) (e : NEnv) : Prop :=
  (C.lo.an : ℝ) ≤ e.a * C.lo.ad ∧ (C.lo.bn : ℝ) ≤ e.b * C.lo.bd ∧ (C.lo.un : ℝ) ≤ e.u * C.lo.ud ∧
    (C.lo.tn : ℝ) ≤ e.t * C.lo.td ∧ (C.lo.ln : ℝ) ≤ e.l * C.lo.ld ∧ C.hi.Mem e

end Cell

/-- The first bounds are below the second ones. -/
def Bounds.le (B B' : Bounds) : Prop :=
  B.an * B'.ad ≤ B'.an * B.ad ∧ B.bn * B'.bd ≤ B'.bn * B.bd ∧ B.un * B'.ud ≤ B'.un * B.ud ∧
    B.tn * B'.td ≤ B'.tn * B.td ∧ B.ln * B'.ld ≤ B'.ln * B.ld

instance (B B' : Bounds) : Decidable (B.le B') := by
  unfold Bounds.le
  infer_instance

instance (B : Bounds) : Decidable B.Valid := by
  unfold Bounds.Valid
  infer_instance

theorem le_of_frac_le {v : ℝ} {n d n' d' : ℕ} (hd : 0 < d) (hv : v * d ≤ n)
    (h : n * d' ≤ n' * d) : v * d' ≤ n' := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((n * d' : ℕ) : ℝ) ≤ ((n' * d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h1
  have h2 : v * d' * d ≤ n' * d := by
    have := mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg d' : (0 : ℝ) ≤ d')
    nlinarith
  exact le_of_mul_le_mul_right h2 hd'

theorem Bounds.mem_of_le {B B' : Bounds} (hB : B.Valid) (h : B.le B') {e : NEnv} (he : B.Mem e) :
    B'.Mem e := by
  obtain ⟨da, db, du, dt, dl⟩ := hB
  obtain ⟨ha, hb, hu, ht, hl⟩ := h
  obtain ⟨a0, a1, b0, b1, u0, u1, t0, t1, l0, l1⟩ := he
  exact ⟨a0, le_of_frac_le da a1 ha, b0, le_of_frac_le db b1 hb, u0, le_of_frac_le du u1 hu, t0,
    le_of_frac_le dt t1 ht, l0, le_of_frac_le dl l1 hl⟩

namespace IPoly

/-- A lower bound of one term on a cell. -/
def termLB (C : Cell) (x : NMono × ℤ) : ℚ :=
  bif decide (0 ≤ x.2) then
    (x.2 : ℚ) * (((C.lo.an : ℚ) / C.lo.ad) ^ x.1.ea * ((C.lo.bn : ℚ) / C.lo.bd) ^ x.1.eb *
      ((C.lo.un : ℚ) / C.lo.ud) ^ x.1.eu * ((C.lo.tn : ℚ) / C.lo.td) ^ x.1.et *
      ((C.lo.ln : ℚ) / C.lo.ld) ^ x.1.el)
  else
    (x.2 : ℚ) * (((C.hi.an : ℚ) / C.hi.ad) ^ x.1.ea * ((C.hi.bn : ℚ) / C.hi.bd) ^ x.1.eb *
      ((C.hi.un : ℚ) / C.hi.ud) ^ x.1.eu * ((C.hi.tn : ℚ) / C.hi.td) ^ x.1.et *
      ((C.hi.ln : ℚ) / C.hi.ld) ^ x.1.el)

/-- A lower bound of a polynomial on a cell. -/
def evalLB (C : Cell) (P : IPoly) : ℚ := (P.map (termLB C)).sum

theorem div_pow_le_pow {v : ℝ} {n d : ℕ} (hd : 0 < d) (h : (n : ℝ) ≤ v * d) (k : ℕ) :
    ((n : ℝ) / d) ^ k ≤ v ^ k := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg n) hd'.le) ((div_le_iff₀ hd').mpr h) k

theorem termLB_le {C : Cell} (hC : C.Valid) {e : NEnv} (he : C.Mem e) (x : NMono × ℤ) :
    (termLB C x : ℝ) ≤ (x.2 : ℝ) * x.1.eval e := by
  obtain ⟨la, lb, lu, lt, ll, hhi⟩ := he
  obtain ⟨⟨da, db, du, dt, dl⟩, hV⟩ := hC
  cases h : decide (0 ≤ x.2)
  · have hneg : (x.2 : ℝ) ≤ 0 := by
      have : x.2 < 0 := by simpa using h
      exact_mod_cast this.le
    obtain ⟨ha, ha', hb, hb', hu, hu', ht, ht', hl, hl'⟩ := hhi
    obtain ⟨ea, eb, eu, et, el⟩ := hV
    have h1 := pow_le_div_pow ha ea ha' x.1.ea
    have h2 := pow_le_div_pow hb eb hb' x.1.eb
    have h3 := pow_le_div_pow hu eu hu' x.1.eu
    have h4 := pow_le_div_pow ht et ht' x.1.et
    have h5 := pow_le_div_pow hl el hl' x.1.el
    have p1 := pow_nonneg ha x.1.ea
    have p2 := pow_nonneg hb x.1.eb
    have p3 := pow_nonneg hu x.1.eu
    have p4 := pow_nonneg ht x.1.et
    have p5 := pow_nonneg hl x.1.el
    have q1 := p1.trans h1
    have q2 := p2.trans h2
    have q3 := p3.trans h3
    have q4 := p4.trans h4
    have hM : x.1.eval e ≤ ((C.hi.an : ℝ) / C.hi.ad) ^ x.1.ea * ((C.hi.bn : ℝ) / C.hi.bd) ^ x.1.eb *
        ((C.hi.un : ℝ) / C.hi.ud) ^ x.1.eu * ((C.hi.tn : ℝ) / C.hi.td) ^ x.1.et *
          ((C.hi.ln : ℝ) / C.hi.ld) ^ x.1.el := by
      simp only [NMono.eval]
      exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 p2 q1) h3 p3 (mul_nonneg q1 q2))
        h4 p4 (mul_nonneg (mul_nonneg q1 q2) q3)) h5 p5
        (mul_nonneg (mul_nonneg (mul_nonneg q1 q2) q3) q4)
    simp only [termLB, h, cond_false]
    push_cast
    exact mul_le_mul_of_nonpos_left hM hneg
  · have hpos : (0 : ℝ) ≤ x.2 := by
      have : 0 ≤ x.2 := by simpa using h
      exact_mod_cast this
    have h1 := div_pow_le_pow da la x.1.ea
    have h2 := div_pow_le_pow db lb x.1.eb
    have h3 := div_pow_le_pow du lu x.1.eu
    have h4 := div_pow_le_pow dt lt x.1.et
    have h5 := div_pow_le_pow dl ll x.1.el
    have n1 : (0 : ℝ) ≤ ((C.lo.an : ℝ) / C.lo.ad) ^ x.1.ea := by positivity
    have n2 : (0 : ℝ) ≤ ((C.lo.bn : ℝ) / C.lo.bd) ^ x.1.eb := by positivity
    have n3 : (0 : ℝ) ≤ ((C.lo.un : ℝ) / C.lo.ud) ^ x.1.eu := by positivity
    have n4 : (0 : ℝ) ≤ ((C.lo.tn : ℝ) / C.lo.td) ^ x.1.et := by positivity
    have n5 : (0 : ℝ) ≤ ((C.lo.ln : ℝ) / C.lo.ld) ^ x.1.el := by positivity
    have m1 := n1.trans h1
    have m2 := n2.trans h2
    have m3 := n3.trans h3
    have m4 := n4.trans h4
    have hM : ((C.lo.an : ℝ) / C.lo.ad) ^ x.1.ea * ((C.lo.bn : ℝ) / C.lo.bd) ^ x.1.eb *
        ((C.lo.un : ℝ) / C.lo.ud) ^ x.1.eu * ((C.lo.tn : ℝ) / C.lo.td) ^ x.1.et *
          ((C.lo.ln : ℝ) / C.lo.ld) ^ x.1.el ≤ x.1.eval e := by
      simp only [NMono.eval]
      exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 n2 m1) h3 n3 (mul_nonneg m1 m2))
        h4 n4 (mul_nonneg (mul_nonneg m1 m2) m3)) h5 n5
        (mul_nonneg (mul_nonneg (mul_nonneg m1 m2) m3) m4)
    simp only [termLB, h, cond_true]
    push_cast
    exact mul_le_mul_of_nonneg_left hM hpos

theorem evalLB_le {C : Cell} (hC : C.Valid) {e : NEnv} (he : C.Mem e) (P : IPoly) :
    (evalLB C P : ℝ) ≤ eval P e := by
  induction P with
  | nil => simp [evalLB]
  | cons x P ih =>
    simp only [evalLB, List.map_cons, List.sum_cons, eval_cons] at ih ⊢
    rw [Rat.cast_add]
    exact add_le_add (termLB_le hC he x) ih

end IPoly

/-! ## The pivot check -/

/-- The quotients of the polynomial part and of the majorant by the two pivots `aⁱ bʲ⁺¹` and
`aⁱ⁺¹ bʲ`. -/
structure Quots where
  PB : IPoly
  RB : IPoly
  PA : IPoly
  RA : IPoly
  deriving DecidableEq

namespace MTM

open IPoly

/-- The quotients by `aⁱ bʲ⁺¹`, and by `aⁱ⁺¹ bʲ` of the remaining terms. -/
def quots (i j : ℕ) (T : MTM) : Quots :=
  ⟨divQuot i (j + 1) T.P, divQuot i (j + 1) T.R, divQuot (i + 1) j (divRest i (j + 1) T.P),
    divQuot (i + 1) j (divRest i (j + 1) T.R)⟩

/-- All terms are divisible by one of the two pivots. -/
def Divisible (i j : ℕ) (T : MTM) : Prop :=
  divRest (i + 1) j (divRest i (j + 1) T.P) = [] ∧ divRest (i + 1) j (divRest i (j + 1) T.R) = []

instance (i j : ℕ) (T : MTM) : Decidable (Divisible i j T) := by
  unfold Divisible
  infer_instance

end MTM

namespace Quots

open IPoly

/-- Lower bound of `Q − R` for the quotients by the pivot `aⁱ bʲ⁺¹`. -/
def marginB (C : Cell) (Q : Quots) : ℚ := evalLB C Q.PB - evalUB C.hi Q.RB

/-- Lower bound of `Q − R` for the quotients by the pivot `aⁱ⁺¹ bʲ`. -/
def marginA (C : Cell) (Q : Quots) : ℚ := evalLB C Q.PA - evalUB C.hi Q.RA

end Quots

namespace Cell

/-- The weight of a margin: the lower bound of the nome if the margin is nonnegative, the upper
bound otherwise. -/
def weight (lo hi m : ℚ) : ℚ := bif decide (0 ≤ m) then lo else hi

/-- `b · βB + a · βA + γ > 0` on the cell, by signs or by the weighted sum. -/
def PosOK (C : Cell) (βB βA γ : ℚ) : Prop :=
  (0 ≤ βB ∧ 0 ≤ βA ∧ 0 ≤ γ ∧ (0 < βB ∨ 0 < βA ∨ 0 < γ)) ∨
    0 < weight ((C.lo.bn : ℚ) / C.lo.bd) ((C.hi.bn : ℚ) / C.hi.bd) βB * βB +
      weight ((C.lo.an : ℚ) / C.lo.ad) ((C.hi.an : ℚ) / C.hi.ad) βA * βA + γ

instance (C : Cell) (βB βA γ : ℚ) : Decidable (C.PosOK βB βA γ) := by
  unfold PosOK
  infer_instance

theorem weight_mul_le {lo hi m : ℚ} {v : ℝ} (hlo : (lo : ℝ) ≤ v) (hhi : v ≤ hi) :
    ((weight lo hi m * m : ℚ) : ℝ) ≤ v * m := by
  unfold weight
  cases h : decide (0 ≤ m)
  · have hm : (m : ℝ) ≤ 0 := by
      have : m < 0 := by simpa using h
      exact_mod_cast this.le
    simp only [cond_false]
    push_cast
    exact mul_le_mul_of_nonpos_right hhi hm
  · have hm : (0 : ℝ) ≤ m := by
      have : 0 ≤ m := by simpa using h
      exact_mod_cast this
    simp only [cond_true]
    push_cast
    exact mul_le_mul_of_nonneg_right hlo hm

/-- **The sign from margins.** -/
theorem pos_of_posOK {C : Cell} (hC : C.Valid) {βB βA γ : ℚ} (h : C.PosOK βB βA γ) {e : NEnv}
    (he : C.Mem e) (ha : 0 < e.a) (hb : 0 < e.b) :
    0 < e.b * (βB : ℝ) + e.a * (βA : ℝ) + (γ : ℝ) := by
  rcases h with ⟨h1, h2, h3, h4⟩ | h
  · have h1' : (0 : ℝ) ≤ βB := by exact_mod_cast h1
    have h2' : (0 : ℝ) ≤ βA := by exact_mod_cast h2
    have h3' : (0 : ℝ) ≤ γ := by exact_mod_cast h3
    have n1 := mul_nonneg hb.le h1'
    have n2 := mul_nonneg ha.le h2'
    rcases h4 with h4 | h4 | h4
    · have h4' : (0 : ℝ) < βB := by exact_mod_cast h4
      have := mul_pos hb h4'
      linarith
    · have h4' : (0 : ℝ) < βA := by exact_mod_cast h4
      have := mul_pos ha h4'
      linarith
    · have h4' : (0 : ℝ) < γ := by exact_mod_cast h4
      linarith
  · obtain ⟨la, lb, -, -, -, hhi⟩ := he
    obtain ⟨-, ha', -, hb', -⟩ := hhi
    obtain ⟨⟨da, db, -⟩, ⟨ea, eb, -⟩⟩ := hC
    have hda : (0 : ℝ) < C.lo.ad := by exact_mod_cast da
    have hdb : (0 : ℝ) < C.lo.bd := by exact_mod_cast db
    have hea : (0 : ℝ) < C.hi.ad := by exact_mod_cast ea
    have heb : (0 : ℝ) < C.hi.bd := by exact_mod_cast eb
    have wb := weight_mul_le (m := βB) (lo := (C.lo.bn : ℚ) / C.lo.bd)
      (hi := (C.hi.bn : ℚ) / C.hi.bd) (v := e.b)
      (by push_cast; exact (div_le_iff₀ hdb).mpr lb) (by push_cast; exact (le_div_iff₀ heb).mpr hb')
    have wa := weight_mul_le (m := βA) (lo := (C.lo.an : ℚ) / C.lo.ad)
      (hi := (C.hi.an : ℚ) / C.hi.ad) (v := e.a)
      (by push_cast; exact (div_le_iff₀ hda).mpr la) (by push_cast; exact (le_div_iff₀ hea).mpr ha')
    have hsum : (0 : ℝ) <
        ((weight ((C.lo.bn : ℚ) / C.lo.bd) ((C.hi.bn : ℚ) / C.hi.bd) βB * βB +
          weight ((C.lo.an : ℚ) / C.lo.ad) ((C.hi.an : ℚ) / C.hi.ad) βA * βA + γ : ℚ) : ℝ) := by
      exact_mod_cast h
    rw [Rat.cast_add, Rat.cast_add] at hsum
    linarith

end Cell

namespace MTM

open IPoly

/-- **The lower bound in pivot form.** On a cell inside the bounds of the model,
`f ≥ aⁱ bʲ (b · marginB + a · marginA)`. -/
theorem lower_of_divisible {Bx : Bounds} {S : NEnv → Prop} {T : MTM} {f : NEnv → ℝ}
    (hT : T.Approx Bx S f) {i j : ℕ} (hdiv : T.Divisible i j) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) {e : NEnv} (he : C.Mem e) (hs : S e) (ha : 0 ≤ e.a) (hb : 0 ≤ e.b) :
    e.a ^ i * e.b ^ j * (e.b * ((T.quots i j).marginB C : ℝ) +
      e.a * ((T.quots i j).marginA C : ℝ)) ≤ f e := by
  obtain ⟨hP0, hR0⟩ := hdiv
  have heB : Bx.Mem e := Bounds.mem_of_le hC.2 hsub he.2.2.2.2.2
  have happ := hT e heB hs
  have hP := eval_div i (j + 1) T.P e
  have hP2 := eval_div (i + 1) j (divRest i (j + 1) T.P) e
  have hR := eval_div i (j + 1) T.R e
  have hR2 := eval_div (i + 1) j (divRest i (j + 1) T.R) e
  rw [hP0, eval_nil, add_zero] at hP2
  rw [hR0, eval_nil, add_zero] at hR2
  have lB1 := evalLB_le hC he (divQuot i (j + 1) T.P)
  have lA1 := evalLB_le hC he (divQuot (i + 1) j (divRest i (j + 1) T.P))
  have uB1 := eval_le_evalUB hC.2 he.2.2.2.2.2 (divQuot i (j + 1) T.R)
  have uA1 := eval_le_evalUB hC.2 he.2.2.2.2.2 (divQuot (i + 1) j (divRest i (j + 1) T.R))
  have hmB : (((T.quots i j).marginB C : ℚ) : ℝ) ≤
      eval (divQuot i (j + 1) T.P) e - eval (divQuot i (j + 1) T.R) e := by
    simp only [Quots.marginB, quots]
    push_cast
    linarith
  have hmA : (((T.quots i j).marginA C : ℚ) : ℝ) ≤
      eval (divQuot (i + 1) j (divRest i (j + 1) T.P)) e -
        eval (divQuot (i + 1) j (divRest i (j + 1) T.R)) e := by
    simp only [Quots.marginA, quots]
    push_cast
    linarith
  have hab : 0 ≤ e.a ^ i * e.b ^ j := mul_nonneg (pow_nonneg ha i) (pow_nonneg hb j)
  have hPR : eval T.P e - eval T.R e =
      e.a ^ i * e.b ^ j * (e.b * (eval (divQuot i (j + 1) T.P) e - eval (divQuot i (j + 1) T.R) e) +
        e.a * (eval (divQuot (i + 1) j (divRest i (j + 1) T.P)) e -
          eval (divQuot (i + 1) j (divRest i (j + 1) T.R)) e)) := by
    rw [hP, hR, hP2, hR2]
    ring
  have k1 := mul_le_mul_of_nonneg_left hmB hb
  have k2 := mul_le_mul_of_nonneg_left hmA ha
  have k3 : e.a ^ i * e.b ^ j * (e.b * ((T.quots i j).marginB C : ℝ) +
      e.a * ((T.quots i j).marginA C : ℝ)) ≤ eval T.P e - eval T.R e := by
    rw [hPR]
    exact mul_le_mul_of_nonneg_left (by linarith) hab
  have := (abs_le.mp happ).1
  linarith

/-- **Positivity from the pivot check.** The function may carry an extra term
`g ≥ aⁱ bʲ γ`. -/
theorem pos_of_posOK {Bx : Bounds} {S : NEnv → Prop} {T : MTM} {f : NEnv → ℝ}
    (hT : T.Approx Bx S f) {i j : ℕ} (hdiv : T.Divisible i j) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) {γ : ℚ}
    (hOK : C.PosOK ((T.quots i j).marginB C) ((T.quots i j).marginA C) γ) {e : NEnv}
    (he : C.Mem e) (hs : S e) (ha : 0 < e.a) (hb : 0 < e.b) {g : ℝ}
    (hg : e.a ^ i * e.b ^ j * (γ : ℝ) ≤ g) : 0 < f e + g := by
  have hlow := lower_of_divisible hT hdiv hC hsub he hs ha.le hb.le
  have hkey := Cell.pos_of_posOK hC hOK he ha hb
  have hab : 0 < e.a ^ i * e.b ^ j := mul_pos (pow_pos ha i) (pow_pos hb j)
  have hpos := mul_pos hab hkey
  have hsplit : e.a ^ i * e.b ^ j * (e.b * ((T.quots i j).marginB C : ℝ) +
      e.a * ((T.quots i j).marginA C : ℝ) + (γ : ℝ)) =
      e.a ^ i * e.b ^ j * (e.b * ((T.quots i j).marginB C : ℝ) +
        e.a * ((T.quots i j).marginA C : ℝ)) + e.a ^ i * e.b ^ j * (γ : ℝ) := by
    ring
  linarith

end MTM

end E8Leech.Kron
