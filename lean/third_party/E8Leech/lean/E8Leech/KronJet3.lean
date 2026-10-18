import E8Leech.KronExpr

/-!
# Third-order jets of a straight-line program in the nome

A numerator that vanishes to the third order at the cusp of the second variable is the cube of the
nome times a function that the majorants can handle. To obtain that function mechanically, a
program is transformed: every register `v` becomes four registers `(c₀, c₁, c₂, r)` with

`v = c₀ + n c₁ + n² c₂ + n³ r`,

where `n` is the first register of the transformed program (the nome of the side). Sums act
componentwise, products are Cauchy products with the overflow collected in `r`. Trees would grow
exponentially here, so the transformation works on programs: each instruction becomes a block of
instructions built from a template with relocated operands.

* `Ref`, `TInstr`, `evalT`, `runR_reloc`: templates and their real evaluation.
* `jet3Val`, `mulT`, `addT`, `subT` and their block lemmas.
* `Block`, `blockOf`, `tr3Aux`, `tr3`: the transformation.
* `Sim3`, `sim3_tr3`: the transformed program simulates the original one, for both versions.
-/

namespace E8Leech.Kron

namespace ISLP

/-! ## Templates -/

/-- An operand of a template: a register of the program so far, or a register of the block. -/
inductive Ref
  | abs (i : ℕ)
  | loc (i : ℕ)

/-- An instruction of a template. -/
inductive TInstr
  | zat (i : ℕ)
  | tat (i : ℕ)
  | cst (c : ℤ)
  | mono (m : NMono)
  | add (x y : Ref)
  | sub (x y : Ref)
  | mul (x y : Ref)

/-- The register of an operand when the block starts at the register `s`. -/
def Ref.reloc (s : ℕ) : Ref → ℕ
  | .abs i => i
  | .loc i => s + i

/-- The instruction of a template when the block starts at the register `s`. -/
def TInstr.reloc (s : ℕ) : TInstr → IInstr
  | .zat i => .zat i
  | .tat i => .tat i
  | .cst c => .cst c
  | .mono m => .mono m
  | .add x y => .add (x.reloc s) (y.reloc s)
  | .sub x y => .sub (x.reloc s) (y.reloc s)
  | .mul x y => .mul (x.reloc s) (y.reloc s)

/-- The absolute operands refer to registers below `len`. -/
def Ref.OK (len : ℕ) : Ref → Prop
  | .abs i => i < len
  | .loc _ => True

/-- The absolute operands of an instruction refer to registers below `len`. -/
def TInstr.OK (len : ℕ) : TInstr → Prop
  | .add x y => x.OK len ∧ y.OK len
  | .sub x y => x.OK len ∧ y.OK len
  | .mul x y => x.OK len ∧ y.OK len
  | _ => True

/-- The Boolean version of `Ref.OK`. -/
def Ref.okB (len : ℕ) : Ref → Bool
  | .abs i => decide (i < len)
  | .loc _ => true

/-- The Boolean version of `TInstr.OK`. -/
def TInstr.okB (len : ℕ) : TInstr → Bool
  | .add x y => x.okB len && y.okB len
  | .sub x y => x.okB len && y.okB len
  | .mul x y => x.okB len && y.okB len
  | _ => true

theorem Ref.OK_of_okB {len : ℕ} : ∀ {x : Ref}, x.okB len = true → x.OK len
  | .abs i, h => (of_decide_eq_true h : i < len)
  | .loc _, _ => trivial

theorem TInstr.OK_of_okB {len : ℕ} : ∀ {t : TInstr}, t.okB len = true → t.OK len
  | .zat _, _ => trivial
  | .tat _, _ => trivial
  | .cst _, _ => trivial
  | .mono _, _ => trivial
  | .add _ _, h => by
    simp only [TInstr.okB, Bool.and_eq_true] at h
    exact ⟨Ref.OK_of_okB h.1, Ref.OK_of_okB h.2⟩
  | .sub _ _, h => by
    simp only [TInstr.okB, Bool.and_eq_true] at h
    exact ⟨Ref.OK_of_okB h.1, Ref.OK_of_okB h.2⟩
  | .mul _ _, h => by
    simp only [TInstr.okB, Bool.and_eq_true] at h
    exact ⟨Ref.OK_of_okB h.1, Ref.OK_of_okB h.2⟩

/-- A template whose instructions pass the Boolean check. -/
theorem OK_of_all_okB {len : ℕ} {ts : List TInstr} (h : ts.all (TInstr.okB len) = true) :
    ∀ t ∈ ts, t.OK len :=
  fun t ht => TInstr.OK_of_okB (List.all_eq_true.mp h t ht)

theorem Ref.OK.mono {len len' : ℕ} (h : len ≤ len') : ∀ {x : Ref}, x.OK len → x.OK len'
  | .abs _, hx => lt_of_lt_of_le hx h
  | .loc _, _ => trivial

theorem TInstr.OK.mono {len len' : ℕ} (h : len ≤ len') : ∀ {t : TInstr}, t.OK len → t.OK len'
  | .zat _, _ => trivial
  | .tat _, _ => trivial
  | .cst _, _ => trivial
  | .mono _, _ => trivial
  | .add _ _, ht => ⟨ht.1.mono h, ht.2.mono h⟩
  | .sub _ _, ht => ⟨ht.1.mono h, ht.2.mono h⟩
  | .mul _ _, ht => ⟨ht.1.mono h, ht.2.mono h⟩

variable (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv)

/-- The value of an operand: `rs` are the registers before the block, `acc` those of the block. -/
noncomputable def Ref.val (rs acc : List ℝ) : Ref → ℝ
  | .abs i => rs.getD i 0
  | .loc i => acc.getD i 0

/-- The value of an instruction of a template. -/
noncomputable def TInstr.val (rs acc : List ℝ) : TInstr → ℝ
  | .zat i => fs.getD i (fun _ => 0) (if side then e.a else e.b)
  | .tat i => fs.getD i (fun _ => 0) e.a
  | .cst c => c
  | .mono m => m.eval e
  | .add x y => x.val rs acc + y.val rs acc
  | .sub x y => x.val rs acc - y.val rs acc
  | .mul x y => x.val rs acc * y.val rs acc

/-- The registers of a block. -/
noncomputable def evalT (rs : List ℝ) : List TInstr → List ℝ → List ℝ
  | [], acc => acc
  | t :: ts, acc => evalT rs ts (acc ++ [t.val fs side e rs acc])

theorem getD_append_add (rs L : List ℝ) (k : ℕ) : (rs ++ L).getD (rs.length + k) 0 = L.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem Ref.val_reloc {rs acc : List ℝ} : ∀ {x : Ref}, x.OK rs.length →
    (rs ++ acc).getD (x.reloc rs.length) 0 = x.val rs acc
  | .abs _, hx => List.getD_append _ _ _ _ hx
  | .loc i, _ => getD_append_add rs acc i

theorem stepR_reloc {rs acc : List ℝ} : ∀ {t : TInstr}, t.OK rs.length →
    stepR fs side e (rs ++ acc) (t.reloc rs.length) = t.val fs side e rs acc
  | .zat _, _ => rfl
  | .tat _, _ => rfl
  | .cst _, _ => rfl
  | .mono _, _ => rfl
  | .add _ _, ht => by
    show (rs ++ acc).getD _ 0 + (rs ++ acc).getD _ 0 = _
    rw [Ref.val_reloc ht.1, Ref.val_reloc ht.2]
    rfl
  | .sub _ _, ht => by
    show (rs ++ acc).getD _ 0 - (rs ++ acc).getD _ 0 = _
    rw [Ref.val_reloc ht.1, Ref.val_reloc ht.2]
    rfl
  | .mul _ _, ht => by
    show (rs ++ acc).getD _ 0 * (rs ++ acc).getD _ 0 = _
    rw [Ref.val_reloc ht.1, Ref.val_reloc ht.2]
    rfl

/-- **A relocated template runs as its evaluation.** -/
theorem runR_reloc (rs : List ℝ) : ∀ (ts : List TInstr) (acc : List ℝ),
    (∀ t ∈ ts, t.OK rs.length) →
    runR fs side e (ts.map (TInstr.reloc rs.length)) (rs ++ acc) =
      rs ++ evalT fs side e rs ts acc
  | [], _, _ => rfl
  | t :: ts, acc, h => by
    have ht := h t List.mem_cons_self
    have hts : ∀ t' ∈ ts, t'.OK rs.length := fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    show runR fs side e (ts.map (TInstr.reloc rs.length))
        ((rs ++ acc) ++ [stepR fs side e (rs ++ acc) (t.reloc rs.length)]) = _
    rw [stepR_reloc fs side e ht, List.append_assoc]
    exact runR_reloc rs ts _ hts

theorem runR_append : ∀ (p q : List IInstr) (rs : List ℝ),
    runR fs side e (p ++ q) rs = runR fs side e q (runR fs side e p rs)
  | [], _, _ => rfl
  | _ :: p, q, _ => runR_append p q _

/-! ## Jets -/

/-- The value of the jet at the register `p`; the nome is the register `0`. -/
noncomputable def jet3Val (rs : List ℝ) (p : ℕ) : ℝ :=
  rs.getD p 0 + rs.getD 0 0 * rs.getD (p + 1) 0 + rs.getD 0 0 ^ 2 * rs.getD (p + 2) 0 +
    rs.getD 0 0 ^ 3 * rs.getD (p + 3) 0

theorem jet3Val_append {rs : List ℝ} (L : List ℝ) {p : ℕ} (hp : p + 3 < rs.length) :
    jet3Val (rs ++ L) p = jet3Val rs p := by
  unfold jet3Val
  rw [List.getD_append _ _ _ _ (by omega : p < rs.length),
    List.getD_append _ _ _ _ (by omega : 0 < rs.length),
    List.getD_append _ _ _ _ (by omega : p + 1 < rs.length),
    List.getD_append _ _ _ _ (by omega : p + 2 < rs.length),
    List.getD_append _ _ _ _ hp]

theorem jet3Val_block (rs L : List ℝ) (k : ℕ) (h0 : 0 < rs.length) :
    jet3Val (rs ++ L) (rs.length + k) = L.getD k 0 + rs.getD 0 0 * L.getD (k + 1) 0 +
      rs.getD 0 0 ^ 2 * L.getD (k + 2) 0 + rs.getD 0 0 ^ 3 * L.getD (k + 3) 0 := by
  unfold jet3Val
  rw [List.getD_append _ _ _ _ h0, getD_append_add, Nat.add_assoc, getD_append_add, Nat.add_assoc,
    getD_append_add, Nat.add_assoc, getD_append_add]

/-- The block of a sum. -/
def addT (pa pb : ℕ) : List TInstr :=
  [.add (.abs pa) (.abs pb), .add (.abs (pa + 1)) (.abs (pb + 1)),
    .add (.abs (pa + 2)) (.abs (pb + 2)), .add (.abs (pa + 3)) (.abs (pb + 3))]

/-- The block of a difference. -/
def subT (pa pb : ℕ) : List TInstr :=
  [.sub (.abs pa) (.abs pb), .sub (.abs (pa + 1)) (.abs (pb + 1)),
    .sub (.abs (pa + 2)) (.abs (pb + 2)), .sub (.abs (pa + 3)) (.abs (pb + 3))]

/-- The block of a product: the Cauchy product, with the terms of order `≥ 3` collected by the
Horner scheme in the last register. The four outputs are the registers `27, …, 30` of the
block. -/
def mulT (pa pb : ℕ) : List TInstr :=
  [.mul (.abs pa) (.abs (pb + 1)), .mul (.abs (pa + 1)) (.abs pb),
    .mul (.abs pa) (.abs (pb + 2)), .mul (.abs (pa + 1)) (.abs (pb + 1)),
    .mul (.abs (pa + 2)) (.abs pb), .add (.loc 2) (.loc 3),
    .mul (.abs pa) (.abs (pb + 3)), .mul (.abs (pa + 1)) (.abs (pb + 2)),
    .mul (.abs (pa + 2)) (.abs (pb + 1)), .mul (.abs (pa + 3)) (.abs pb),
    .add (.loc 6) (.loc 7), .add (.loc 10) (.loc 8), .add (.loc 11) (.loc 9),
    .mul (.abs (pa + 1)) (.abs (pb + 3)), .mul (.abs (pa + 2)) (.abs (pb + 2)),
    .mul (.abs (pa + 3)) (.abs (pb + 1)), .add (.loc 13) (.loc 14), .add (.loc 16) (.loc 15),
    .mul (.abs (pa + 2)) (.abs (pb + 3)), .mul (.abs (pa + 3)) (.abs (pb + 2)),
    .add (.loc 18) (.loc 19), .mul (.abs (pa + 3)) (.abs (pb + 3)),
    .mul (.abs 0) (.loc 21), .add (.loc 20) (.loc 22), .mul (.abs 0) (.loc 23),
    .add (.loc 17) (.loc 24), .mul (.abs 0) (.loc 25),
    .mul (.abs pa) (.abs pb), .add (.loc 0) (.loc 1), .add (.loc 5) (.loc 4),
    .add (.loc 12) (.loc 26)]

theorem jet3Val_addT (rs : List ℝ) (pa pb : ℕ) (h0 : 0 < rs.length) :
    jet3Val (rs ++ evalT fs side e rs (addT pa pb) []) (rs.length + 0) =
      jet3Val rs pa + jet3Val rs pb := by
  rw [jet3Val_block _ _ _ h0]
  simp only [addT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, jet3Val]
  ring

theorem jet3Val_subT (rs : List ℝ) (pa pb : ℕ) (h0 : 0 < rs.length) :
    jet3Val (rs ++ evalT fs side e rs (subT pa pb) []) (rs.length + 0) =
      jet3Val rs pa - jet3Val rs pb := by
  rw [jet3Val_block _ _ _ h0]
  simp only [subT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, jet3Val]
  ring

theorem jet3Val_mulT (rs : List ℝ) (pa pb : ℕ) (h0 : 0 < rs.length) :
    jet3Val (rs ++ evalT fs side e rs (mulT pa pb) []) (rs.length + 27) =
      jet3Val rs pa * jet3Val rs pb := by
  rw [jet3Val_block _ _ _ h0]
  simp only [mulT, evalT, TInstr.val, Ref.val, List.nil_append, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, jet3Val]
  ring

/-- The block of a leaf whose jet is its value. -/
def leafT (t : TInstr) : List TInstr := [t, .cst 0, .cst 0, .cst 0]

theorem jet3Val_leafT (rs : List ℝ) (t : TInstr) (h0 : 0 < rs.length) :
    jet3Val (rs ++ evalT fs side e rs (leafT t) []) (rs.length + 0) = t.val fs side e rs [] := by
  rw [jet3Val_block _ _ _ h0]
  simp only [leafT, evalT, TInstr.val, List.nil_append, List.cons_append, List.getD_cons_zero,
    List.getD_cons_succ]
  push_cast
  ring

/-! ## The transformation -/

/-- A block: `pre` registers and then the four registers of the jet. -/
structure Block where
  pre : ℕ
  ts : List TInstr

/-- The block of an instruction; `outs` lists the positions of the jets of the earlier
registers, and `zleaf` the blocks of the atoms of the second variable. -/
def blockOf (zleaf : ℕ → Block) (outs : List ℕ) : IInstr → Block
  | .zat i => zleaf i
  | .tat i => ⟨0, leafT (.tat i)⟩
  | .cst c => ⟨0, leafT (.cst c)⟩
  | .mono m => ⟨0, leafT (.mono m)⟩
  | .add i j => ⟨0, addT (outs.getD i 1) (outs.getD j 1)⟩
  | .sub i j => ⟨0, subT (outs.getD i 1) (outs.getD j 1)⟩
  | .mul i j => ⟨27, mulT (outs.getD i 1) (outs.getD j 1)⟩

/-- The transformation with accumulators: the positions of the jets and the program so far. -/
def tr3Aux (zleaf : ℕ → Block) : List IInstr → List ℕ → List IInstr → List IInstr × List ℕ
  | [], outs, acc => (acc, outs)
  | ins :: rest, outs, acc =>
    tr3Aux zleaf rest (outs ++ [acc.length + (blockOf zleaf outs ins).pre])
      (acc ++ (blockOf zleaf outs ins).ts.map (TInstr.reloc acc.length))

/-- The first registers of a transformed program: the nome, and a zero jet at the register `1`
for the registers that do not exist. -/
def prelude3 : List IInstr := [.zat 0, .cst 0, .cst 0, .cst 0, .cst 0]

/-- **The transformed program** and the positions of the jets of the registers. -/
def tr3 (zleaf : ℕ → Block) (prog : List IInstr) : List IInstr × List ℕ :=
  tr3Aux zleaf prog [] prelude3

/-! ## Soundness -/

/-- The registers `R` of the transformed program simulate the registers `ro` of the original
one: the nome is `x`, the register `1` carries a zero jet, and the jets at `outs` have the values
`ro`. -/
def Sim3 (x : ℝ) (R : List ℝ) (outs : List ℕ) (ro : List ℝ) : Prop :=
  4 < R.length ∧ R.getD 0 0 = x ∧ jet3Val R 1 = 0 ∧ outs.length = ro.length ∧
    ∀ j, j < ro.length → outs.getD j 1 + 3 < R.length ∧ jet3Val R (outs.getD j 1) = ro.getD j 0

theorem Sim3.get {x : ℝ} {R : List ℝ} {outs : List ℕ} {ro : List ℝ} (h : Sim3 x R outs ro)
    (j : ℕ) : outs.getD j 1 + 3 < R.length ∧ jet3Val R (outs.getD j 1) = ro.getD j 0 := by
  obtain ⟨h4, -, h1, hlen, hj⟩ := h
  rcases Nat.lt_or_ge j ro.length with hlt | hge
  · exact hj j hlt
  · have e1 : outs.getD j 1 = 1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have e2 : ro.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    rw [e1, e2]
    exact ⟨by omega, h1⟩

/-- One more register. -/
theorem Sim3.extend {x : ℝ} {R : List ℝ} {outs : List ℕ} {ro : List ℝ} (h : Sim3 x R outs ro)
    (L : List ℝ) {p : ℕ} {v : ℝ} (hp : p + 3 < (R ++ L).length) (hv : jet3Val (R ++ L) p = v) :
    Sim3 x (R ++ L) (outs ++ [p]) (ro ++ [v]) := by
  obtain ⟨h4, hx, h1, hlen, hj⟩ := h
  refine ⟨by rw [List.length_append]; omega, ?_, ?_, by simp [hlen], fun j hjlt => ?_⟩
  · rw [List.getD_append _ _ _ _ (by omega : 0 < R.length)]
    exact hx
  · rw [jet3Val_append L (by omega : 1 + 3 < R.length)]
    exact h1
  · rw [E8Leech.Taylor.SLP.getD_append_single, E8Leech.Taylor.SLP.getD_append_single, hlen]
    rw [List.length_append, List.length_singleton] at hjlt
    rcases Nat.lt_or_ge j ro.length with hlt | hge
    · rw [if_pos hlt, if_pos hlt]
      obtain ⟨hb, hval⟩ := hj j hlt
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [jet3Val_append L hb]
      exact hval
    · have hje : j = ro.length := by omega
      rw [if_neg (by omega), if_pos hje, if_neg (by omega), if_pos hje]
      exact ⟨hp, hv⟩

variable {fs side e}

/-- The blocks of the atoms of the second variable are sound: for registers whose first one is
the nome `x`, the jet of the block has the value of the atom. -/
def ZLeafOK (fs : List (ℝ → ℝ)) (side : Bool) (e : NEnv) (x : ℝ) (zleaf : ℕ → Block) : Prop :=
  ∀ i, (∀ t ∈ (zleaf i).ts, t.OK 1) ∧ ∀ rs : List ℝ, 0 < rs.length → rs.getD 0 0 = x →
    ((zleaf i).pre + 3 < (evalT fs side e rs (zleaf i).ts []).length ∧
      jet3Val (rs ++ evalT fs side e rs (zleaf i).ts []) (rs.length + (zleaf i).pre) =
        fs.getD i (fun _ => 0) (if side then e.a else e.b))

theorem length_evalT (rs : List ℝ) : ∀ (ts : List TInstr) (acc : List ℝ),
    (evalT fs side e rs ts acc).length = acc.length + ts.length
  | [], _ => rfl
  | _ :: ts, acc => by
    rw [evalT, length_evalT rs ts, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- **One step of the simulation.** -/
theorem sim3_step {x : ℝ} {zleaf : ℕ → Block} (hz : ZLeafOK fs side e x zleaf) {R : List ℝ}
    {outs : List ℕ} {ro : List ℝ} (h : Sim3 x R outs ro) (ins : IInstr) :
    (∀ t ∈ (blockOf zleaf outs ins).ts, t.OK R.length) ∧
      Sim3 x (R ++ evalT fs side e R (blockOf zleaf outs ins).ts [])
        (outs ++ [R.length + (blockOf zleaf outs ins).pre]) (ro ++ [stepR fs side e ro ins]) := by
  have h4 : 4 < R.length := h.1
  have h0 : 0 < R.length := by omega
  have hx : R.getD 0 0 = x := h.2.1
  cases ins with
  | zat i =>
    obtain ⟨hok, hval⟩ := hz i
    obtain ⟨hlen, hv⟩ := hval R h0 hx
    refine ⟨fun t ht => (hok t ht).mono (by omega), h.extend _ ?_ hv⟩
    show R.length + (zleaf i).pre + 3 < (R ++ evalT fs side e R (zleaf i).ts []).length
    rw [List.length_append]
    omega
  | tat i =>
    refine ⟨fun t ht => ?_, h.extend _ ?_ (jet3Val_leafT fs side e R (.tat i) h0)⟩
    · simp only [blockOf, leafT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> trivial
    · rw [List.length_append, length_evalT]
      show R.length + 0 + 3 < R.length + (0 + 4)
      omega
  | cst c =>
    refine ⟨fun t ht => ?_, h.extend _ ?_ (jet3Val_leafT fs side e R (.cst c) h0)⟩
    · simp only [blockOf, leafT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> trivial
    · rw [List.length_append, length_evalT]
      show R.length + 0 + 3 < R.length + (0 + 4)
      omega
  | mono m =>
    refine ⟨fun t ht => ?_, h.extend _ ?_ (jet3Val_leafT fs side e R (.mono m) h0)⟩
    · simp only [blockOf, leafT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> trivial
    · rw [List.length_append, length_evalT]
      show R.length + 0 + 3 < R.length + (0 + 4)
      omega
  | add i j =>
    obtain ⟨hi, hvi⟩ := h.get i
    obtain ⟨hj, hvj⟩ := h.get j
    refine ⟨fun t ht => ?_, h.extend _ ?_ ?_⟩
    · simp only [blockOf, addT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> exact ⟨by show _ < _; omega, by show _ < _; omega⟩
    · rw [List.length_append, length_evalT]
      show R.length + 0 + 3 < R.length + (0 + 4)
      omega
    · show jet3Val (R ++ evalT fs side e R (addT (outs.getD i 1) (outs.getD j 1)) [])
        (R.length + 0) = ro.getD i 0 + ro.getD j 0
      rw [jet3Val_addT fs side e R _ _ h0, hvi, hvj]
  | sub i j =>
    obtain ⟨hi, hvi⟩ := h.get i
    obtain ⟨hj, hvj⟩ := h.get j
    refine ⟨fun t ht => ?_, h.extend _ ?_ ?_⟩
    · simp only [blockOf, subT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> exact ⟨by show _ < _; omega, by show _ < _; omega⟩
    · rw [List.length_append, length_evalT]
      show R.length + 0 + 3 < R.length + (0 + 4)
      omega
    · show jet3Val (R ++ evalT fs side e R (subT (outs.getD i 1) (outs.getD j 1)) [])
        (R.length + 0) = ro.getD i 0 - ro.getD j 0
      rw [jet3Val_subT fs side e R _ _ h0, hvi, hvj]
  | mul i j =>
    obtain ⟨hi, hvi⟩ := h.get i
    obtain ⟨hj, hvj⟩ := h.get j
    refine ⟨fun t ht => ?_, h.extend _ ?_ ?_⟩
    · simp only [blockOf, mulT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        first
          | exact ⟨trivial, trivial⟩
          | exact ⟨by show _ < _; omega, by show _ < _; omega⟩
          | exact ⟨by show _ < _; omega, trivial⟩
    · rw [List.length_append, length_evalT]
      show R.length + 27 + 3 < R.length + (0 + 31)
      omega
    · show jet3Val (R ++ evalT fs side e R (mulT (outs.getD i 1) (outs.getD j 1)) [])
        (R.length + 27) = ro.getD i 0 * ro.getD j 0
      rw [jet3Val_mulT fs side e R _ _ h0, hvi, hvj]

theorem length_runR : ∀ (p : List IInstr) (rs : List ℝ),
    (runR fs side e p rs).length = rs.length + p.length
  | [], _ => rfl
  | _ :: p, rs => by
    rw [runR, length_runR p, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- **The transformed program simulates the original one.** -/
theorem sim3_tr3Aux {x : ℝ} {zleaf : ℕ → Block} (hz : ZLeafOK fs side e x zleaf) :
    ∀ (prog : List IInstr) (outs : List ℕ) (acc : List IInstr) (ro : List ℝ),
      Sim3 x (runR fs side e acc []) outs ro →
      Sim3 x (runR fs side e (tr3Aux zleaf prog outs acc).1 []) (tr3Aux zleaf prog outs acc).2
        (runR fs side e prog ro)
  | [], _, _, _, h => h
  | ins :: rest, outs, acc, ro, h => by
    obtain ⟨hok, hsim⟩ := sim3_step hz h ins
    have hlen : (runR fs side e acc []).length = acc.length := by
      rw [length_runR]
      simp
    refine sim3_tr3Aux hz rest _ _ _ ?_
    rw [runR_append, ← hlen]
    have hrun := runR_reloc fs side e (runR fs side e acc []) (blockOf zleaf outs ins).ts [] hok
    rw [List.append_nil] at hrun
    rw [hrun]
    exact hsim

/-- The registers of the prelude simulate the empty program. -/
theorem sim3_prelude (hf : fs.getD 0 (fun _ => 0) = id) :
    Sim3 (if side then e.a else e.b) (runR fs side e prelude3 []) [] [] := by
  have hrun : runR fs side e prelude3 [] =
      [fs.getD 0 (fun _ => 0) (if side then e.a else e.b), ((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ),
        ((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ)] := rfl
  rw [hrun, hf]
  refine ⟨by simp, rfl, ?_, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  simp [jet3Val]

/-- The first register of the transformed program is the nome. -/
theorem tr3_nome (hf : fs.getD 0 (fun _ => 0) = id) {zleaf : ℕ → Block}
    (hz : ZLeafOK fs side e (if side then e.a else e.b) zleaf) (prog : List IInstr) :
    (runR fs side e (tr3 zleaf prog).1 []).getD 0 0 = if side then e.a else e.b :=
  (sim3_tr3Aux hz prog [] prelude3 [] (sim3_prelude hf)).2.1

/-- **Soundness of the transformation**: the jet of the register `k` of the transformed program
has the value of the register `k` of the original program. -/
theorem sim3_tr3 (hf : fs.getD 0 (fun _ => 0) = id) {zleaf : ℕ → Block}
    (hz : ZLeafOK fs side e (if side then e.a else e.b) zleaf) (prog : List IInstr) (k : ℕ) :
    jet3Val (runR fs side e (tr3 zleaf prog).1 []) ((tr3 zleaf prog).2.getD k 1) =
      (runR fs side e prog []).getD k 0 :=
  ((sim3_tr3Aux hz prog [] prelude3 [] (sim3_prelude hf)).get k).2

end ISLP

end E8Leech.Kron
