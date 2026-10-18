import E8Leech.KronKernelSign

/-!
# Cell checks with vertex evaluation in the variables other than the nomes

The termwise lower bound `IPoly.evalLB` treats every monomial of a quotient polynomial separately.
The coefficient of a nome monomial `aⁱ bʲ` is itself a polynomial in `û, t̂` and `log 2`, and near
the corner `u = t = 1` its monomials cancel almost completely; the termwise bound then loses the
sign unless the cell is tiny.

The numerators are affine in each of `û`, `t̂` and `log 2`. A function that is affine in each of
three variables takes its minimum over a box at one of the eight vertices, so it suffices to
bound the polynomial at the vertices; there the terms with the same nome monomial are summed
exactly before the bound in the nomes is taken.

* `AffineFun`, `lt_of_vertices`: the vertex principle.
* `IPoly.MultiAffine`, `IPoly.affine_u`, `IPoly.affine_t`, `IPoly.affine_l`.
* `IPoly.evalLBv`, `IPoly.evalLBv_le`: the lower bound at a vertex.
* `MTM.lower_of_divisible_eval`: the lower bound in pivot form with the quotients unevaluated.
* `Quots.marginBv`, `Quots.marginAv`, `Cell.pos_of_vertices`: the vertex margins and the sign.
* `splitDD_combination_pos_vertex`: positivity of `t̂ · D₁ + b · D₂` on a cell from the vertex
  check; `vertexCellOK` is the corresponding cell test.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## The vertex principle -/

/-- `g` is an affine function. -/
def AffineFun (g : ℝ → ℝ) : Prop := ∃ α β : ℝ, ∀ x, g x = α + β * x

theorem AffineFun.lt_of_endpoints {g : ℝ → ℝ} (hg : AffineFun g) {lo hi x m : ℝ} (h0 : lo ≤ x)
    (h1 : x ≤ hi) (hlo : m < g lo) (hhi : m < g hi) : m < g x := by
  obtain ⟨α, β, h⟩ := hg
  rw [h] at hlo hhi ⊢
  rcases le_total 0 β with hβ | hβ
  · have := mul_le_mul_of_nonneg_left h0 hβ
    linarith
  · have := mul_le_mul_of_nonpos_left h1 hβ
    linarith

theorem AffineFun.comb {g h : ℝ → ℝ} (hg : AffineFun g) (hh : AffineFun h) (c d : ℝ) :
    AffineFun fun x => c * g x + d * h x := by
  obtain ⟨α, β, hg⟩ := hg
  obtain ⟨α', β', hh⟩ := hh
  refine ⟨c * α + d * α', c * β + d * β', fun x => ?_⟩
  show c * g x + d * h x = _
  rw [hg, hh]
  ring

/-- **The vertex principle.** A function that is affine in each of its three variables exceeds
`m` on a box as soon as it does so at the eight vertices. -/
theorem lt_of_vertices {F : ℝ → ℝ → ℝ → ℝ} (h₁ : ∀ t l, AffineFun fun u => F u t l)
    (h₂ : ∀ u l, AffineFun fun t => F u t l) (h₃ : ∀ u t, AffineFun fun l => F u t l)
    {u₀ u₁ t₀ t₁ l₀ l₁ u t l m : ℝ} (hu0 : u₀ ≤ u) (hu1 : u ≤ u₁) (ht0 : t₀ ≤ t) (ht1 : t ≤ t₁)
    (hl0 : l₀ ≤ l) (hl1 : l ≤ l₁)
    (hv : ∀ i j k : Bool,
      m < F (bif i then u₁ else u₀) (bif j then t₁ else t₀) (bif k then l₁ else l₀)) :
    m < F u t l := by
  have step3 : ∀ i j : Bool, m < F (bif i then u₁ else u₀) (bif j then t₁ else t₀) l := fun i j =>
    (h₃ _ _).lt_of_endpoints hl0 hl1 (hv i j false) (hv i j true)
  have step2 : ∀ i : Bool, m < F (bif i then u₁ else u₀) t l := fun i =>
    (h₂ _ _).lt_of_endpoints ht0 ht1 (step3 i false) (step3 i true)
  exact (h₁ _ _).lt_of_endpoints hu0 hu1 (step2 false) (step2 true)

/-! ## Polynomials that are affine in `û`, `t̂` and `log 2` -/

namespace IPoly

/-- The exponents of `u, t, l` are at most one in every term. -/
def MultiAffine (P : IPoly) : Prop := ∀ x ∈ P, x.1.eu ≤ 1 ∧ x.1.et ≤ 1 ∧ x.1.el ≤ 1

instance (P : IPoly) : Decidable (MultiAffine P) := by
  unfold MultiAffine
  infer_instance

theorem MultiAffine.tail {x : NMono × ℤ} {P : IPoly} (h : MultiAffine (x :: P)) :
    MultiAffine P := fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem affine_u {P : IPoly} (h : P.MultiAffine) (a b t l : ℝ) :
    AffineFun fun u => eval P ⟨a, b, u, t, l⟩ := by
  induction P with
  | nil => exact ⟨0, 0, fun x => by simp⟩
  | cons x P ih =>
    obtain ⟨α, β, hP⟩ := ih h.tail
    replace hP : ∀ u, eval P ⟨a, b, u, t, l⟩ = α + β * u := hP
    have hx := (h x List.mem_cons_self).1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h0 | h1
    · refine ⟨α + x.2 * (a ^ x.1.ea * b ^ x.1.eb * t ^ x.1.et * l ^ x.1.el), β, fun u => ?_⟩
      show eval (x :: P) ⟨a, b, u, t, l⟩ = _
      rw [eval_cons, hP]
      simp only [NMono.eval, h0, pow_zero]
      ring
    · refine ⟨α, β + x.2 * (a ^ x.1.ea * b ^ x.1.eb * t ^ x.1.et * l ^ x.1.el), fun u => ?_⟩
      show eval (x :: P) ⟨a, b, u, t, l⟩ = _
      rw [eval_cons, hP]
      simp only [NMono.eval, h1, pow_one]
      ring

theorem affine_t {P : IPoly} (h : P.MultiAffine) (a b u l : ℝ) :
    AffineFun fun t => eval P ⟨a, b, u, t, l⟩ := by
  induction P with
  | nil => exact ⟨0, 0, fun x => by simp⟩
  | cons x P ih =>
    obtain ⟨α, β, hP⟩ := ih h.tail
    replace hP : ∀ t, eval P ⟨a, b, u, t, l⟩ = α + β * t := hP
    have hx := (h x List.mem_cons_self).2.1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h0 | h1
    · refine ⟨α + x.2 * (a ^ x.1.ea * b ^ x.1.eb * u ^ x.1.eu * l ^ x.1.el), β, fun t => ?_⟩
      show eval (x :: P) ⟨a, b, u, t, l⟩ = _
      rw [eval_cons, hP]
      simp only [NMono.eval, h0, pow_zero]
      ring
    · refine ⟨α, β + x.2 * (a ^ x.1.ea * b ^ x.1.eb * u ^ x.1.eu * l ^ x.1.el), fun t => ?_⟩
      show eval (x :: P) ⟨a, b, u, t, l⟩ = _
      rw [eval_cons, hP]
      simp only [NMono.eval, h1, pow_one]
      ring

theorem affine_l {P : IPoly} (h : P.MultiAffine) (a b u t : ℝ) :
    AffineFun fun l => eval P ⟨a, b, u, t, l⟩ := by
  induction P with
  | nil => exact ⟨0, 0, fun x => by simp⟩
  | cons x P ih =>
    obtain ⟨α, β, hP⟩ := ih h.tail
    replace hP : ∀ l, eval P ⟨a, b, u, t, l⟩ = α + β * l := hP
    have hx := (h x List.mem_cons_self).2.2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h0 | h1
    · refine ⟨α + x.2 * (a ^ x.1.ea * b ^ x.1.eb * u ^ x.1.eu * t ^ x.1.et), β, fun l => ?_⟩
      show eval (x :: P) ⟨a, b, u, t, l⟩ = _
      rw [eval_cons, hP]
      simp only [NMono.eval, h0, pow_zero]
      ring
    · refine ⟨α, β + x.2 * (a ^ x.1.ea * b ^ x.1.eb * u ^ x.1.eu * t ^ x.1.et), fun l => ?_⟩
      show eval (x :: P) ⟨a, b, u, t, l⟩ = _
      rw [eval_cons, hP]
      simp only [NMono.eval, h1, pow_one]
      ring

/-! ## The lower bound at a vertex -/

/-- The coefficient of the nome monomial of a term at the vertex `(vu, vt, vl)`. -/
def coeffAt (vu vt vl : ℚ) (x : NMono × ℤ) : ℚ :=
  (x.2 : ℚ) * (vu ^ x.1.eu * vt ^ x.1.et * vl ^ x.1.el)

/-- A lower bound of `q aⁱ bʲ` on the nome box of a cell. -/
def flushLB (C : Cell) (i j : ℕ) (q : ℚ) : ℚ :=
  bif decide (0 ≤ q) then
    q * (((C.lo.an : ℚ) / C.lo.ad) ^ i * ((C.lo.bn : ℚ) / C.lo.bd) ^ j)
  else q * (((C.hi.an : ℚ) / C.hi.ad) ^ i * ((C.hi.bn : ℚ) / C.hi.bd) ^ j)

/-- Consecutive terms with the same nome monomial `aⁱ bʲ` are summed (coefficient `q`) before
the bound in the nomes is taken. -/
def lbAcc (C : Cell) (vu vt vl : ℚ) : IPoly → ℕ → ℕ → ℚ → ℚ
  | [], i, j, q => flushLB C i j q
  | x :: P, i, j, q =>
    bif (x.1.ea == i) && (x.1.eb == j) then lbAcc C vu vt vl P i j (q + coeffAt vu vt vl x)
    else flushLB C i j q + lbAcc C vu vt vl P x.1.ea x.1.eb (coeffAt vu vt vl x)

/-- A lower bound of a polynomial on the nome box of a cell, with `u, t, l` at the vertex
`(vu, vt, vl)`. -/
def evalLBv (C : Cell) (vu vt vl : ℚ) (P : IPoly) : ℚ := lbAcc C vu vt vl P 0 0 0

theorem flushLB_le {C : Cell} (hC : C.Valid) {a b : ℝ} (la : (C.lo.an : ℝ) ≤ a * C.lo.ad)
    (lb : (C.lo.bn : ℝ) ≤ b * C.lo.bd) (ha : 0 ≤ a) (ha' : a * C.hi.ad ≤ C.hi.an) (hb : 0 ≤ b)
    (hb' : b * C.hi.bd ≤ C.hi.bn) (i j : ℕ) (q : ℚ) :
    (flushLB C i j q : ℝ) ≤ q * (a ^ i * b ^ j) := by
  obtain ⟨⟨da, db, -⟩, ⟨ea, eb, -⟩⟩ := hC
  cases h : decide (0 ≤ q)
  · have hq : (q : ℝ) ≤ 0 := by
      have : q < 0 := by simpa using h
      exact_mod_cast this.le
    have h1 := pow_le_div_pow ha ea ha' i
    have h2 := pow_le_div_pow hb eb hb' j
    have hM : a ^ i * b ^ j ≤ ((C.hi.an : ℝ) / C.hi.ad) ^ i * ((C.hi.bn : ℝ) / C.hi.bd) ^ j :=
      mul_le_mul h1 h2 (pow_nonneg hb j) ((pow_nonneg ha i).trans h1)
    simp only [flushLB, h, cond_false]
    push_cast
    exact mul_le_mul_of_nonpos_left hM hq
  · have hq : (0 : ℝ) ≤ q := by
      have : 0 ≤ q := by simpa using h
      exact_mod_cast this
    have h1 := div_pow_le_pow da la i
    have h2 := div_pow_le_pow db lb j
    have n1 : (0 : ℝ) ≤ ((C.lo.an : ℝ) / C.lo.ad) ^ i := by positivity
    have n2 : (0 : ℝ) ≤ ((C.lo.bn : ℝ) / C.lo.bd) ^ j := by positivity
    have hM : ((C.lo.an : ℝ) / C.lo.ad) ^ i * ((C.lo.bn : ℝ) / C.lo.bd) ^ j ≤ a ^ i * b ^ j :=
      mul_le_mul h1 h2 n2 (n1.trans h1)
    simp only [flushLB, h, cond_true]
    push_cast
    exact mul_le_mul_of_nonneg_left hM hq

theorem lbAcc_le {C : Cell} (hC : C.Valid) {a b : ℝ} (la : (C.lo.an : ℝ) ≤ a * C.lo.ad)
    (lb : (C.lo.bn : ℝ) ≤ b * C.lo.bd) (ha : 0 ≤ a) (ha' : a * C.hi.ad ≤ C.hi.an) (hb : 0 ≤ b)
    (hb' : b * C.hi.bd ≤ C.hi.bn) (vu vt vl : ℚ) :
    ∀ (P : IPoly) (i j : ℕ) (q : ℚ),
      (lbAcc C vu vt vl P i j q : ℝ) ≤ q * (a ^ i * b ^ j) + eval P ⟨a, b, vu, vt, vl⟩
  | [], i, j, q => by
    simpa [lbAcc] using flushLB_le hC la lb ha ha' hb hb' i j q
  | x :: P, i, j, q => by
    have hx : (x.2 : ℝ) * x.1.eval ⟨a, b, vu, vt, vl⟩ =
        (coeffAt vu vt vl x : ℝ) * (a ^ x.1.ea * b ^ x.1.eb) := by
      simp only [coeffAt, NMono.eval]
      push_cast
      ring
    cases h : (x.1.ea == i) && (x.1.eb == j)
    · have ih := lbAcc_le hC la lb ha ha' hb hb' vu vt vl P x.1.ea x.1.eb (coeffAt vu vt vl x)
      have hf := flushLB_le hC la lb ha ha' hb hb' i j q
      simp only [lbAcc, h, cond_false, eval_cons]
      push_cast
      rw [hx]
      linarith
    · have ih := lbAcc_le hC la lb ha ha' hb hb' vu vt vl P i j (q + coeffAt vu vt vl x)
      have hij : x.1.ea = i ∧ x.1.eb = j := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using h
      simp only [lbAcc, h, cond_true, eval_cons]
      rw [hx, hij.1, hij.2]
      push_cast at ih
      linarith

/-- **The lower bound at a vertex.** -/
theorem evalLBv_le {C : Cell} (hC : C.Valid) {e : NEnv} (he : C.Mem e) (vu vt vl : ℚ)
    (P : IPoly) : (evalLBv C vu vt vl P : ℝ) ≤ eval P ⟨e.a, e.b, vu, vt, vl⟩ := by
  obtain ⟨la, lb, -, -, -, hhi⟩ := he
  obtain ⟨ha, ha', hb, hb', -⟩ := hhi
  have h := lbAcc_le hC la lb ha ha' hb hb' vu vt vl P 0 0 0
  simpa [evalLBv] using h

end IPoly

/-! ## The vertices of a cell and the vertex margins -/

namespace Cell

/-- The endpoints of `û` on the cell. -/
def vu (C : Cell) (i : Bool) : ℚ :=
  bif i then (C.hi.un : ℚ) / C.hi.ud else (C.lo.un : ℚ) / C.lo.ud

/-- The endpoints of `t̂` on the cell. -/
def vt (C : Cell) (i : Bool) : ℚ :=
  bif i then (C.hi.tn : ℚ) / C.hi.td else (C.lo.tn : ℚ) / C.lo.td

/-- The endpoints of `log 2` on the cell. -/
def vl (C : Cell) (i : Bool) : ℚ :=
  bif i then (C.hi.ln : ℚ) / C.hi.ld else (C.lo.ln : ℚ) / C.lo.ld

end Cell

namespace Quots

open IPoly

/-- Lower bound of `Q − R` at a vertex for the quotients by the pivot `aⁱ bʲ⁺¹`. -/
def marginBv (C : Cell) (Q : Quots) (p q r : Bool) : ℚ :=
  evalLBv C (C.vu p) (C.vt q) (C.vl r) Q.PB - evalUB C.hi Q.RB

/-- Lower bound of `Q − R` at a vertex for the quotients by the pivot `aⁱ⁺¹ bʲ`. -/
def marginAv (C : Cell) (Q : Quots) (p q r : Bool) : ℚ :=
  evalLBv C (C.vu p) (C.vt q) (C.vl r) Q.PA - evalUB C.hi Q.RA

end Quots

namespace MTM

open IPoly

/-- **The lower bound in pivot form with the quotients of the polynomial part unevaluated.** -/
theorem lower_of_divisible_eval {Bx : Bounds} {S : NEnv → Prop} {T : MTM} {f : NEnv → ℝ}
    (hT : T.Approx Bx S f) {i j : ℕ} (hdiv : T.Divisible i j) {C : Cell} (hC : C.Valid)
    (hsub : C.hi.le Bx) {e : NEnv} (he : C.Mem e) (hs : S e) (ha : 0 ≤ e.a) (hb : 0 ≤ e.b) :
    e.a ^ i * e.b ^ j * (e.b * (eval (T.quots i j).PB e - (evalUB C.hi (T.quots i j).RB : ℝ)) +
      e.a * (eval (T.quots i j).PA e - (evalUB C.hi (T.quots i j).RA : ℝ))) ≤ f e := by
  obtain ⟨hP0, hR0⟩ := hdiv
  have heB : Bx.Mem e := Bounds.mem_of_le hC.2 hsub he.2.2.2.2.2
  have happ := hT e heB hs
  have hP := eval_div i (j + 1) T.P e
  have hP2 := eval_div (i + 1) j (divRest i (j + 1) T.P) e
  have hR := eval_div i (j + 1) T.R e
  have hR2 := eval_div (i + 1) j (divRest i (j + 1) T.R) e
  rw [hP0, eval_nil, add_zero] at hP2
  rw [hR0, eval_nil, add_zero] at hR2
  have uB1 := eval_le_evalUB hC.2 he.2.2.2.2.2 (divQuot i (j + 1) T.R)
  have uA1 := eval_le_evalUB hC.2 he.2.2.2.2.2 (divQuot (i + 1) j (divRest i (j + 1) T.R))
  have hab : 0 ≤ e.a ^ i * e.b ^ j := mul_nonneg (pow_nonneg ha i) (pow_nonneg hb j)
  have hPR : eval T.P e - eval T.R e =
      e.a ^ i * e.b ^ j * (e.b * (eval (divQuot i (j + 1) T.P) e - eval (divQuot i (j + 1) T.R) e) +
        e.a * (eval (divQuot (i + 1) j (divRest i (j + 1) T.P)) e -
          eval (divQuot (i + 1) j (divRest i (j + 1) T.R)) e)) := by
    rw [hP, hR, hP2, hR2]
    ring
  have k1 := mul_le_mul_of_nonneg_left (sub_le_sub_left uB1 (eval (divQuot i (j + 1) T.P) e)) hb
  have k2 := mul_le_mul_of_nonneg_left
    (sub_le_sub_left uA1 (eval (divQuot (i + 1) j (divRest i (j + 1) T.P)) e)) ha
  have k3 : e.a ^ i * e.b ^ j * (e.b * (eval (T.quots i j).PB e - (evalUB C.hi (T.quots i j).RB : ℝ)) +
      e.a * (eval (T.quots i j).PA e - (evalUB C.hi (T.quots i j).RA : ℝ))) ≤
      eval T.P e - eval T.R e := by
    rw [hPR]
    exact mul_le_mul_of_nonneg_left (by simpa only [quots] using add_le_add k1 k2) hab
  have := (abs_le.mp happ).1
  linarith

end MTM

namespace Cell

open IPoly

/-- **The sign from the vertex margins.** If the pivot check passes at the eight vertices, with
additional terms `γB, γA`, then the weighted sum of the quotients is positive on the cell. -/
theorem pos_of_vertices {C : Cell} (hC : C.Valid) {Q : Quots} (hPB : Q.PB.MultiAffine)
    (hPA : Q.PA.MultiAffine) {γB γA : ℚ}
    (hOK : ∀ p q r : Bool, C.PosOK (Q.marginBv C p q r + γB) (Q.marginAv C p q r + γA) 0)
    {e : NEnv} (he : C.Mem e) (ha : 0 < e.a) (hb : 0 < e.b) :
    0 < e.b * (eval Q.PB e - (evalUB C.hi Q.RB : ℝ) + γB) +
      e.a * (eval Q.PA e - (evalUB C.hi Q.RA : ℝ) + γA) := by
  have he' := he
  have hC' := hC
  obtain ⟨-, -, lu, lt, ll, hhi⟩ := he
  obtain ⟨-, -, -, -, -, hu', -, ht', -, hl'⟩ := hhi
  obtain ⟨⟨-, -, du, dt, dl⟩, ⟨-, -, eu, et, el⟩⟩ := hC
  have hdu : (0 : ℝ) < C.lo.ud := by exact_mod_cast du
  have hdt : (0 : ℝ) < C.lo.td := by exact_mod_cast dt
  have hdl : (0 : ℝ) < C.lo.ld := by exact_mod_cast dl
  have heu : (0 : ℝ) < C.hi.ud := by exact_mod_cast eu
  have het : (0 : ℝ) < C.hi.td := by exact_mod_cast et
  have hel : (0 : ℝ) < C.hi.ld := by exact_mod_cast el
  -- the function of `(u, t, l)` and the threshold
  set F : ℝ → ℝ → ℝ → ℝ := fun u t l =>
    e.b * eval Q.PB ⟨e.a, e.b, u, t, l⟩ + e.a * eval Q.PA ⟨e.a, e.b, u, t, l⟩ with hF
  have hgoal : e.b * ((evalUB C.hi Q.RB : ℝ) - γB) + e.a * ((evalUB C.hi Q.RA : ℝ) - γA) <
      F e.u e.t e.l := by
    refine lt_of_vertices (F := F)
      (fun t l => (affine_u hPB e.a e.b t l).comb (affine_u hPA e.a e.b t l) e.b e.a)
      (fun u l => (affine_t hPB e.a e.b u l).comb (affine_t hPA e.a e.b u l) e.b e.a)
      (fun u t => (affine_l hPB e.a e.b u t).comb (affine_l hPA e.a e.b u t) e.b e.a)
      (u₀ := ((C.vu false : ℚ) : ℝ)) (u₁ := ((C.vu true : ℚ) : ℝ))
      (t₀ := ((C.vt false : ℚ) : ℝ)) (t₁ := ((C.vt true : ℚ) : ℝ))
      (l₀ := ((C.vl false : ℚ) : ℝ)) (l₁ := ((C.vl true : ℚ) : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [vu, cond_false]
      push_cast
      exact (div_le_iff₀ hdu).mpr lu
    · simp only [vu, cond_true]
      push_cast
      exact (le_div_iff₀ heu).mpr hu'
    · simp only [vt, cond_false]
      push_cast
      exact (div_le_iff₀ hdt).mpr lt
    · simp only [vt, cond_true]
      push_cast
      exact (le_div_iff₀ het).mpr ht'
    · simp only [vl, cond_false]
      push_cast
      exact (div_le_iff₀ hdl).mpr ll
    · simp only [vl, cond_true]
      push_cast
      exact (le_div_iff₀ hel).mpr hl'
    · intro p q r
      have hp : (bif p then ((C.vu true : ℚ) : ℝ) else ((C.vu false : ℚ) : ℝ)) = ((C.vu p : ℚ) : ℝ) := by
        cases p <;> rfl
      have hq : (bif q then ((C.vt true : ℚ) : ℝ) else ((C.vt false : ℚ) : ℝ)) = ((C.vt q : ℚ) : ℝ) := by
        cases q <;> rfl
      have hr : (bif r then ((C.vl true : ℚ) : ℝ) else ((C.vl false : ℚ) : ℝ)) = ((C.vl r : ℚ) : ℝ) := by
        cases r <;> rfl
      rw [hp, hq, hr]
      have hkey := Cell.pos_of_posOK hC' (hOK p q r) he' ha hb
      have lB := evalLBv_le hC' he' (C.vu p) (C.vt q) (C.vl r) Q.PB
      have lA := evalLBv_le hC' he' (C.vu p) (C.vt q) (C.vl r) Q.PA
      simp only [Quots.marginBv, Quots.marginAv] at hkey
      push_cast at hkey
      have kB := mul_le_mul_of_nonneg_left lB hb.le
      have kA := mul_le_mul_of_nonneg_left lA ha.le
      simp only [hF]
      linarith
  have hFe : F e.u e.t e.l = e.b * eval Q.PB e + e.a * eval Q.PA e := rfl
  rw [hFe] at hgoal
  linarith

end Cell

/-! ## The split divided numerator with the vertex check -/

/-- **Positivity of a split divided numerator on a cell, vertex check.** As
`splitDD_combination_pos`, with the margins of the first model taken at the eight vertices of
the cell in `(û, t̂, log 2)`. -/
theorem splitDD_combination_pos_vertex {Bx : Bounds} {Λ : ℕ} {x₁ x₂ : IExpr} {T₁ T₂ : MTM}
    {i : ℕ} (h₁ : T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ x₁))
    (h₂ : T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) (splitDD Λ x₂))
    (hd₁ : T₁.Divisible i 0) (hd₂ : T₂.Divisible i 0)
    (hPB : (T₁.quots i 0).PB.MultiAffine) (hPA : (T₁.quots i 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w : ℚ} (hw : WOK C w)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots i 0).marginBv C p q r + w * min ((T₂.quots i 0).marginB C) 0)
        ((T₁.quots i 0).marginAv C p q r + w * min ((T₂.quots i 0).marginA C) 0) 0)
    {u t : ℝ} (ht : 0 < t) (hut : u ≠ t) (hmem : C.Mem (axisNEnv u t)) :
    0 < (axisNEnv u t).t * splitDD Λ x₁ (axisNEnv u t) +
      (axisNEnv u t).b * splitDD Λ x₂ (axisNEnv u t) := by
  have hπ := Real.pi_pos
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv u t).b := Real.exp_pos _
  have hY : 0 < (axisNEnv u t).t := by
    have h : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [h]
    positivity
  have hab : (axisNEnv u t).a ≠ (axisNEnv u t).b := by
    intro h
    have h' : Real.exp (-π * u) = Real.exp (-π * t) := h
    exact hut (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h'))
  have l₁ := MTM.lower_of_divisible_eval h₁ hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have l₂ := MTM.lower_of_divisible h₂ hd₂ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have hwb : (axisNEnv u t).b ≤ (w : ℝ) * (axisNEnv u t).t := by
    have hmem' : C.Mem (recNEnv (1 / (π * u)) (1 / (π * t))) := by
      rw [← axisNEnv_eq_recNEnv]
      exact hmem
    have h := hw.le hC (y := 1 / (π * t)) (by positivity) hmem'
    have hb' : (axisNEnv u t).b = Real.exp (-(1 / (π * t))⁻¹) := by
      rw [axisNEnv_eq_recNEnv]
      rfl
    have ht' : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [hb', ht']
    exact h
  obtain ⟨W, hWdef, hW0, hWw⟩ : ∃ W : ℝ, W * (axisNEnv u t).t = (axisNEnv u t).b ∧ 0 ≤ W ∧
      W ≤ (w : ℝ) :=
    ⟨(axisNEnv u t).b / (axisNEnv u t).t, div_mul_cancel₀ _ hY.ne', div_nonneg hb.le hY.le,
      (div_le_iff₀ hY).mpr hwb⟩
  have hkey := Cell.pos_of_vertices hC hPB hPA hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots i 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots i 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hpos : 0 < splitDD Λ x₁ (axisNEnv u t) + W * splitDD Λ x₂ (axisNEnv u t) := by
    have hin : 0 < (axisNEnv u t).b * (IPoly.eval (T₁.quots i 0).PB (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RB : ℝ)) +
        (axisNEnv u t).a * (IPoly.eval (T₁.quots i 0).PA (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RA : ℝ)) +
        W * ((axisNEnv u t).b * (((T₂.quots i 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((T₂.quots i 0).marginA C : ℚ) : ℝ)) := by
      nlinarith [hkey, kB, kA]
    have hmul := mul_pos hc hin
    generalize (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 = c at hmul l₁ k2
    nlinarith [hmul, l₁, k2]
  have hlin : (axisNEnv u t).t * splitDD Λ x₁ (axisNEnv u t) +
      (axisNEnv u t).b * splitDD Λ x₂ (axisNEnv u t) =
      (axisNEnv u t).t * (splitDD Λ x₁ (axisNEnv u t) + W * splitDD Λ x₂ (axisNEnv u t)) := by
    rw [← hWdef]
    ring
  rw [hlin]
  exact mul_pos hY hpos

/-- The cell test of a split numerator with the vertex check. `w` bounds `b / t̂` on the cell;
the second auxiliary number of a leaf is not used. -/
def vertexCellOK (Bx : Bounds) (Q₁ Q₂ : Quots) (C : Cell) (w _ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ WOK C w ∧ ∀ p q r : Bool,
    C.PosOK (Q₁.marginBv C p q r + w * min (Q₂.marginB C) 0)
      (Q₁.marginAv C p q r + w * min (Q₂.marginA C) 0) 0)

end E8Leech.Kron
