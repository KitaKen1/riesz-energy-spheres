import E8Leech.KronCells
import E8Leech.KronExpr

/-!
# Interval evaluation of straight-line programs

Rational interval arithmetic for the values of a program on a cell. Unlike the polynomial models
of `KronMajorant`, nothing is truncated: the enclosures of the atoms come from their models once,
and the program is then evaluated exactly on intervals. This is the right tool when the nomes are
not small enough for a truncated expansion in the nomes but the cells are small.

* `QI`, `QI.Mem`, `QI.mem_add`, `QI.mem_sub`, `QI.mem_mul`, `QI.mem_pow`: the arithmetic.
* `IEnv`, `IEnv.Sound`: enclosures of the atoms on both sides and of the five variables.
* `ISLP.runI`, `ISLP.mem_runI`, `ISLP.mem_runI_expr`: the interval run of a program encloses the
  value of the expression that the program computes.
* `MTM.encl`, `MTM.mem_encl`: the enclosure of a model on a cell.
* `IEnv.ofCell`, `IEnv.sound_ofCell`: the enclosures on a cell from the models of the atoms.
-/

namespace E8Leech.Kron

open E8Leech.Taylor

/-- A closed interval with rational endpoints. -/
structure QI where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace QI

/-- A real number lies in the interval. -/
def Mem (I : QI) (v : ℝ) : Prop := (I.lo : ℝ) ≤ v ∧ v ≤ (I.hi : ℝ)

def zero : QI := ⟨0, 0⟩

def const (c : ℤ) : QI := ⟨c, c⟩

def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩

def sub (I J : QI) : QI := ⟨I.lo - J.hi, I.hi - J.lo⟩

def mul (I J : QI) : QI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

def pow (I : QI) : ℕ → QI
  | 0 => const 1
  | n + 1 => (pow I n).mul I

theorem mem_zero : zero.Mem 0 := by
  have h : (((0 : ℚ) : ℝ)) = 0 := Rat.cast_zero
  exact ⟨h.le, h.ge⟩

theorem mem_const (c : ℤ) : (const c).Mem (c : ℝ) := by
  have h : (((c : ℤ) : ℚ) : ℝ) = (c : ℝ) := Rat.cast_intCast c
  exact ⟨h.le, h.ge⟩

theorem mem_add {I J : QI} {v w : ℝ} (hv : I.Mem v) (hw : J.Mem w) : (I.add J).Mem (v + w) := by
  refine ⟨?_, ?_⟩
  · show ((I.lo + J.lo : ℚ) : ℝ) ≤ v + w
    rw [Rat.cast_add]
    exact add_le_add hv.1 hw.1
  · show v + w ≤ ((I.hi + J.hi : ℚ) : ℝ)
    rw [Rat.cast_add]
    exact add_le_add hv.2 hw.2

theorem mem_sub {I J : QI} {v w : ℝ} (hv : I.Mem v) (hw : J.Mem w) : (I.sub J).Mem (v - w) := by
  refine ⟨?_, ?_⟩
  · show ((I.lo - J.hi : ℚ) : ℝ) ≤ v - w
    rw [Rat.cast_sub]
    exact sub_le_sub hv.1 hw.2
  · show v - w ≤ ((I.hi - J.lo : ℚ) : ℝ)
    rw [Rat.cast_sub]
    exact sub_le_sub hv.2 hw.1

/-- A product of two bounded reals lies between the extreme products of the bounds. -/
theorem mul_bounds {a b c d v w : ℝ} (hv : a ≤ v ∧ v ≤ b) (hw : c ≤ w ∧ w ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ v * w ∧
      v * w ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨hav, hvb⟩ := hv
  obtain ⟨hcw, hwd⟩ := hw
  constructor
  · rcases le_total 0 w with h | h
    · have h1 : a * w ≤ v * w := mul_le_mul_of_nonneg_right hav h
      rcases le_total 0 a with ha | ha
      · have h2 : a * c ≤ a * w := mul_le_mul_of_nonneg_left hcw ha
        exact ((min_le_left _ _).trans (min_le_left _ _)).trans (h2.trans h1)
      · have h2 : a * d ≤ a * w := mul_le_mul_of_nonpos_left hwd ha
        exact ((min_le_left _ _).trans (min_le_right _ _)).trans (h2.trans h1)
    · have h1 : b * w ≤ v * w := mul_le_mul_of_nonpos_right hvb h
      rcases le_total 0 b with hb | hb
      · have h2 : b * c ≤ b * w := mul_le_mul_of_nonneg_left hcw hb
        exact ((min_le_right _ _).trans (min_le_left _ _)).trans (h2.trans h1)
      · have h2 : b * d ≤ b * w := mul_le_mul_of_nonpos_left hwd hb
        exact ((min_le_right _ _).trans (min_le_right _ _)).trans (h2.trans h1)
  · rcases le_total 0 w with h | h
    · have h1 : v * w ≤ b * w := mul_le_mul_of_nonneg_right hvb h
      rcases le_total 0 b with hb | hb
      · have h2 : b * w ≤ b * d := mul_le_mul_of_nonneg_left hwd hb
        exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_right _ _))
      · have h2 : b * w ≤ b * c := mul_le_mul_of_nonpos_left hcw hb
        exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_right _ _))
    · have h1 : v * w ≤ a * w := mul_le_mul_of_nonpos_right hav h
      rcases le_total 0 a with ha | ha
      · have h2 : a * w ≤ a * d := mul_le_mul_of_nonneg_left hwd ha
        exact (h1.trans h2).trans ((le_max_right _ _).trans (le_max_left _ _))
      · have h2 : a * w ≤ a * c := mul_le_mul_of_nonpos_left hcw ha
        exact (h1.trans h2).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem mem_mul {I J : QI} {v w : ℝ} (hv : I.Mem v) (hw : J.Mem w) : (I.mul J).Mem (v * w) := by
  have h := mul_bounds hv hw
  refine ⟨?_, ?_⟩
  · show ((min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) : ℚ) : ℝ) ≤
      v * w
    push_cast
    exact h.1
  · show v * w ≤
      ((max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)) : ℚ) : ℝ)
    push_cast
    exact h.2

theorem mem_pow {I : QI} {v : ℝ} (hv : I.Mem v) (n : ℕ) : (I.pow n).Mem (v ^ n) := by
  induction n with
  | zero =>
    have h := mem_const 1
    rw [Int.cast_one] at h
    rw [pow_zero]
    exact h
  | succ n ih =>
    rw [pow_succ]
    exact mem_mul ih hv

/-- A real number in the interval of two fractions. -/
theorem mem_frac {v : ℝ} {n d n' d' : ℕ} (hd : 0 < d) (hd' : 0 < d') (h1 : (n : ℝ) ≤ v * d)
    (h2 : v * d' ≤ n') : (⟨(n : ℚ) / d, (n' : ℚ) / d'⟩ : QI).Mem v := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hdr' : (0 : ℝ) < d' := by exact_mod_cast hd'
  refine ⟨?_, ?_⟩
  · show (((n : ℚ) / d : ℚ) : ℝ) ≤ v
    push_cast
    exact (div_le_iff₀ hdr).mpr h1
  · show v ≤ (((n' : ℚ) / d' : ℚ) : ℝ)
    push_cast
    exact (le_div_iff₀ hdr').mpr h2

end QI

/-! ## Enclosures on a cell -/

/-- Enclosures of the atoms on both sides and of the five variables. -/
structure IEnv where
  za : ℕ → QI
  ta : ℕ → QI
  va : QI
  vb : QI
  vu : QI
  vt : QI
  vl : QI

namespace IEnv

/-- The enclosures are valid at an environment, for atoms with the meanings `fs`. -/
def Sound (E : IEnv) (fs : List (ℝ → ℝ)) (e : NEnv) : Prop :=
  (∀ i, (E.za i).Mem (fs.getD i (fun _ => 0) e.b)) ∧
    (∀ i, (E.ta i).Mem (fs.getD i (fun _ => 0) e.a)) ∧
    E.va.Mem e.a ∧ E.vb.Mem e.b ∧ E.vu.Mem e.u ∧ E.vt.Mem e.t ∧ E.vl.Mem e.l

/-- The enclosure of a monomial. -/
def mono (E : IEnv) (m : NMono) : QI :=
  ((((E.va.pow m.ea).mul (E.vb.pow m.eb)).mul (E.vu.pow m.eu)).mul (E.vt.pow m.et)).mul
    (E.vl.pow m.el)

theorem mem_mono {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e) (m : NMono) :
    (E.mono m).Mem (m.eval e) := by
  obtain ⟨-, -, ha, hb, hu, ht, hl⟩ := hE
  exact QI.mem_mul (QI.mem_mul (QI.mem_mul (QI.mem_mul (QI.mem_pow ha _) (QI.mem_pow hb _))
    (QI.mem_pow hu _)) (QI.mem_pow ht _)) (QI.mem_pow hl _)

end IEnv

namespace ISLP

/-- One instruction on intervals. -/
def stepI (E : IEnv) (regs : List QI) : IInstr → QI
  | .zat i => E.za i
  | .tat i => E.ta i
  | .cst c => QI.const c
  | .mono m => E.mono m
  | .add i j => (regs.getD i QI.zero).add (regs.getD j QI.zero)
  | .sub i j => (regs.getD i QI.zero).sub (regs.getD j QI.zero)
  | .mul i j => (regs.getD i QI.zero).mul (regs.getD j QI.zero)

def runI (E : IEnv) : List IInstr → List QI → List QI
  | [], regs => regs
  | ins :: rest, regs => runI E rest (regs ++ [stepI E regs ins])

theorem mem_stepI {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e)
    {regs : List QI} {rs : List ℝ} (hk : ∀ k, (regs.getD k QI.zero).Mem (rs.getD k 0))
    (ins : IInstr) : (stepI E regs ins).Mem (stepR fs false e rs ins) := by
  cases ins with
  | zat i => simpa [stepI, stepR] using hE.1 i
  | tat i => simpa [stepI, stepR] using hE.2.1 i
  | cst c => simpa [stepI, stepR] using QI.mem_const c
  | mono m => simpa [stepI, stepR] using IEnv.mem_mono hE m
  | add i j => simpa [stepI, stepR] using QI.mem_add (hk i) (hk j)
  | sub i j => simpa [stepI, stepR] using QI.mem_sub (hk i) (hk j)
  | mul i j => simpa [stepI, stepR] using QI.mem_mul (hk i) (hk j)

theorem mem_runI_aux {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e) :
    ∀ (prog : List IInstr) (regs : List QI) (rs : List ℝ), rs.length = regs.length →
      (∀ k, (regs.getD k QI.zero).Mem (rs.getD k 0)) →
      ∀ k, ((runI E prog regs).getD k QI.zero).Mem ((runR fs false e prog rs).getD k 0)
  | [], _, _, _, hk => hk
  | ins :: rest, regs, rs, hlen, hk => by
    simp only [runI, runR]
    refine mem_runI_aux hE rest _ _ (by simp [hlen]) (fun k => ?_)
    rw [SLP.getD_append_single, SLP.getD_append_single, hlen]
    split_ifs with h1 h2
    · exact hk k
    · exact mem_stepI hE hk ins
    · exact QI.mem_zero

/-- **The interval run encloses the real run.** -/
theorem mem_runI {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e)
    (prog : List IInstr) (k : ℕ) :
    ((runI E prog []).getD k QI.zero).Mem ((runR fs false e prog []).getD k 0) :=
  mem_runI_aux hE prog [] [] rfl (fun k => by simpa using QI.mem_zero) k

/-- **The interval run encloses the value of the expression that the program computes.** -/
theorem mem_runI_expr {E : IEnv} {fs : List (ℝ → ℝ)} {e : NEnv} (hE : E.Sound fs e)
    (prog : List IInstr) (k : ℕ) (x : IExpr) (h : (runExpr prog []).getD k (.cst 0) = x) :
    ((runI E prog []).getD k QI.zero).Mem (IExpr.evalB fs x e) := by
  have h1 := mem_runI hE prog k
  rw [← eval_runExpr_getD, h] at h1
  exact h1

end ISLP

/-! ## Enclosures from models -/

namespace MTM

open IPoly

/-- The enclosure of a model on a cell. -/
def encl (T : MTM) (C : Cell) : QI :=
  ⟨evalLB C T.P - evalUB C.hi T.R, evalUB C.hi T.R - evalLB C (IPoly.neg T.P)⟩

theorem mem_encl {Bx : Bounds} {S : NEnv → Prop} {T : MTM} {f : NEnv → ℝ} (hT : T.Approx Bx S f)
    {C : Cell} (hC : C.Valid) (hsub : C.hi.le Bx) {e : NEnv} (he : C.Mem e) (hs : S e) :
    (T.encl C).Mem (f e) := by
  have heB : Bx.Mem e := Bounds.mem_of_le hC.2 hsub he.2.2.2.2.2
  have happ := abs_le.mp (hT e heB hs)
  have l1 := evalLB_le hC he T.P
  have l2 := evalLB_le hC he (IPoly.neg T.P)
  rw [IPoly.eval_neg] at l2
  have u1 := eval_le_evalUB hC.2 he.2.2.2.2.2 T.R
  refine ⟨?_, ?_⟩
  · show ((evalLB C T.P - evalUB C.hi T.R : ℚ) : ℝ) ≤ f e
    rw [Rat.cast_sub]
    linarith [happ.1]
  · show f e ≤ ((evalUB C.hi T.R - evalLB C (IPoly.neg T.P) : ℚ) : ℝ)
    rw [Rat.cast_sub]
    linarith [happ.2]

end MTM

namespace Cell

/-- The bounds of the five variables of a cell as intervals. -/
def ivA (C : Cell) : QI := ⟨(C.lo.an : ℚ) / C.lo.ad, (C.hi.an : ℚ) / C.hi.ad⟩
def ivB (C : Cell) : QI := ⟨(C.lo.bn : ℚ) / C.lo.bd, (C.hi.bn : ℚ) / C.hi.bd⟩
def ivU (C : Cell) : QI := ⟨(C.lo.un : ℚ) / C.lo.ud, (C.hi.un : ℚ) / C.hi.ud⟩
def ivT (C : Cell) : QI := ⟨(C.lo.tn : ℚ) / C.lo.td, (C.hi.tn : ℚ) / C.hi.td⟩
def ivL (C : Cell) : QI := ⟨(C.lo.ln : ℚ) / C.lo.ld, (C.hi.ln : ℚ) / C.hi.ld⟩

theorem mem_iv {C : Cell} (hC : C.Valid) {e : NEnv} (he : C.Mem e) :
    C.ivA.Mem e.a ∧ C.ivB.Mem e.b ∧ C.ivU.Mem e.u ∧ C.ivT.Mem e.t ∧ C.ivL.Mem e.l := by
  obtain ⟨la, lb, lu, lt, ll, hhi⟩ := he
  obtain ⟨-, ha, -, hb, -, hu, -, ht, -, hl⟩ := hhi
  obtain ⟨⟨da, db, du, dt, dl⟩, ⟨ea, eb, eu, et, el⟩⟩ := hC
  exact ⟨QI.mem_frac da ea la ha, QI.mem_frac db eb lb hb, QI.mem_frac du eu lu hu,
    QI.mem_frac dt et lt ht, QI.mem_frac dl el ll hl⟩

end Cell

/-- The enclosures on a cell from the models `At` of the atoms. -/
def IEnv.ofCell (At : List MDD) (C : Cell) : IEnv :=
  ⟨fun i => (At.getD i MDD.zero).B.encl C, fun i => (At.getD i MDD.zero).A.encl C, C.ivA, C.ivB,
    C.ivU, C.ivT, C.ivL⟩

theorem IEnv.sound_ofCell {Bx : Bounds} {At : List MDD} {fs : List (ℝ → ℝ)}
    (hAt : ISLP.AtomsOK Bx (fun _ => True) At fs) {C : Cell} (hC : C.Valid) (hsub : C.hi.le Bx)
    {e : NEnv} (he : C.Mem e) : (IEnv.ofCell At C).Sound fs e := by
  obtain ⟨ha, hb, hu, ht, hl⟩ := Cell.mem_iv hC he
  exact ⟨fun i => MTM.mem_encl (hAt i).2.1 hC hsub he trivial,
    fun i => MTM.mem_encl (hAt i).1 hC hsub he trivial, ha, hb, hu, ht, hl⟩

end E8Leech.Kron
