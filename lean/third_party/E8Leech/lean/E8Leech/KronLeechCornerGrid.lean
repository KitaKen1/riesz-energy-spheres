import E8Leech.KronTaylorN
import E8Leech.KronLeechCorner

/-!
# The corner certificate for `d = 24` on a grid

`LeechCornerPos` is the positivity of the bilinear form `Σ_k A_k(u) H_k(t)` of six functions of `u`
and six functions of `t` on a square. Each of the twelve functions loses several digits to
cancellation, so plain interval enclosures on a grid are useless here. Instead every function is
expanded around the centre of an interval of the grid (`KronTaylorN`): its values on the interval
are polynomials in `θ` whose first coefficients lie in narrow intervals (jets on a thin cell around
the centre) and whose last coefficient lies in the enclosure of the next derivation on the
interval. The pairing of two such rows is a polynomial in `θ, η` whose coefficients are pairings of
columns; these are formed first, which keeps the cancellation between the six terms, and are then
multiplied by enclosures of the monomials `θᵖ ηᵠ/(p! q!)`.

The `τ`-side functions are mirrored to the `z`-side (`IExpr.swap`), so that one derivation serves
both sides.

* `bilI`, `col`, `bil_tay`, `pairI`, `mem_pairI`: the pairing of two tables of rows.
* `TCell`, `cellJets`, `rowsT`, `rowsZ`, `forall₂_rowsT`, `forall₂_rowsZ`: an interval of the grid,
  with a cell around the interval and a thin cell around its centre, and the rows of the two sides.
* `intervalOKTC`, `intervalOKTX`, `intervalOKZC`, `intervalOKZX`, `pairRowOK`, `pairOKT`: the checks
  (four per interval, so that each kernel check stays small).
* `leechCornerPos_of_grid`: the certificate.
-/

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## Pairing two tables of rows -/

/-- The interval pairing of two lists of intervals. -/
def bilI : List QI → List QI → QI
  | [], _ => QI.zero
  | _ :: _, [] => QI.zero
  | I :: Is, J :: Js => (I.mul J).add (bilI Is Js)

/-- The entries `p` of the rows of a table. -/
def col (T : List (List QI)) (p : ℕ) : List QI := T.map fun J => J.getD p QI.zero

/-- **The pairing of the values of two tables is a polynomial in `θ`, `η`** whose coefficients lie
in the pairings of the columns. -/
theorem bil_tay {n : ℕ} {θ η : ℝ} : ∀ {TA : List (List QI)} {xs : List ℝ},
    List.Forall₂ (TayMem n θ) TA xs → ∀ {TZ : List (List QI)} {ys : List ℝ},
    List.Forall₂ (TayMem n η) TZ ys →
    ∃ m : ℕ → ℕ → ℝ, (∀ p q, p < n → q < n → (bilI (col TA p) (col TZ q)).Mem (m p q)) ∧
      bil xs ys = ∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
        m p q * ((θ ^ p / (p.factorial : ℝ)) * (η ^ q / (q.factorial : ℝ))) := by
  intro TA xs hA
  induction hA with
  | nil =>
    intro TZ ys _
    exact ⟨fun _ _ => 0, fun p q _ _ => QI.mem_zero, by simp [bil]⟩
  | @cons J x TA' xs' hx _ ih =>
    intro TZ ys hZ
    cases hZ with
    | nil => exact ⟨fun _ _ => 0, fun p q _ _ => QI.mem_zero, by simp [bil]⟩
    | @cons K y TZ' ys' hy hZ' =>
      obtain ⟨m, hm, hbil⟩ := ih hZ'
      obtain ⟨c, hc, hxe⟩ := hx
      obtain ⟨d, hd, hye⟩ := hy
      refine ⟨fun p q => c p * d q + m p q, fun p q hp hq => ?_, ?_⟩
      · show (((J.getD p QI.zero).mul (K.getD q QI.zero)).add
          (bilI (col TA' p) (col TZ' q))).Mem (c p * d q + m p q)
        exact QI.mem_add (QI.mem_mul (hc p hp) (hd q hq)) (hm p q hp hq)
      · show x * y + bil xs' ys' = _
        rw [hbil, hxe, hye, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring

/-- The enclosure of the pairing of two tables with `n` columns; `P` and `Q` enclose the
monomials `θᵖ/p!` and `ηᵠ/q!`. -/
def pairI (n : ℕ) (TA TZ : List (List QI)) (P Q : List QI) : QI :=
  qsum ((List.range n).map fun p => qsum ((List.range n).map fun q =>
    (bilI (col TA p) (col TZ q)).mul ((P.getD p QI.zero).mul (Q.getD q QI.zero))))

theorem list_sum_range_map (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem mem_qsum_range (n : ℕ) {I : ℕ → QI} {v : ℕ → ℝ} (h : ∀ p, p < n → (I p).Mem (v p)) :
    (qsum ((List.range n).map I)).Mem (∑ p ∈ Finset.range n, v p) := by
  rw [← list_sum_range_map]
  refine mem_qsum _ _ ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun p hp => h p (List.mem_range.mp hp)

/-- **The enclosure of the pairing is sound.** -/
theorem mem_pairI {n : ℕ} {θ η : ℝ} {TA TZ : List (List QI)} {xs ys : List ℝ} {P Q : List QI}
    (hA : List.Forall₂ (TayMem n θ) TA xs) (hZ : List.Forall₂ (TayMem n η) TZ ys)
    (hP : ∀ p, p < n → (P.getD p QI.zero).Mem (θ ^ p / (p.factorial : ℝ)))
    (hQ : ∀ q, q < n → (Q.getD q QI.zero).Mem (η ^ q / (q.factorial : ℝ))) :
    (pairI n TA TZ P Q).Mem (bil xs ys) := by
  obtain ⟨m, hm, hbil⟩ := bil_tay hA hZ
  rw [hbil]
  exact mem_qsum_range n fun p hp => mem_qsum_range n fun q hq =>
    QI.mem_mul (hm p q hp hq) (QI.mem_mul (hP p hp) (hQ q hq))

/-! ## Tables that contain the computed rows -/

/-- The entries `≤ N` of `J` lie inside those of `T`. -/
def withinC (N : ℕ) (J T : List QI) : Bool :=
  (List.range (N + 1)).all fun q => (J.getD q QI.zero).within (T.getD q QI.zero)

/-- The entry `N + 1` of `J` lies inside that of `T`. -/
def withinX (N : ℕ) (J T : List QI) : Bool :=
  (J.getD (N + 1) QI.zero).within (T.getD (N + 1) QI.zero)

/-- A row of a table contains the row of the jets: the entries `≤ N` of the jet at the centre and
the entry `N + 1` of the jet on the interval are checked separately. -/
theorem tayMem_of_withinCX {N : ℕ} {θ : ℝ} {JC JX T : List QI} {v : ℝ}
    (hC : withinC N JC T = true) (hX : withinX N JX T = true)
    (h : TayMem (N + 2) θ (tayRow N JC JX) v) : TayMem (N + 2) θ T v := by
  obtain ⟨c, hc, hv⟩ := h
  refine ⟨c, fun q hq => ?_, hv⟩
  have h1 := hc q hq
  rw [tayRow, getD_map_range _ _ hq] at h1
  rcases Nat.lt_or_ge q (N + 1) with hlt | hge
  · rw [if_pos (Nat.lt_succ_iff.mp hlt)] at h1
    exact QI.mem_of_within (List.all_eq_true.mp hC q (List.mem_range.mpr hlt)) h1
  · have hq' : q = N + 1 := by omega
    subst hq'
    rw [if_neg (by omega)] at h1
    exact QI.mem_of_within hX h1

/-- Rowwise `withinC` of two tables with the same number of rows. -/
def rowsOKC (N : ℕ) : List (List QI) → List (List QI) → Bool
  | [], [] => true
  | J :: Js, T :: Ts => withinC N J T && rowsOKC N Js Ts
  | _, _ => false

/-- Rowwise `withinX` of two tables with the same number of rows. -/
def rowsOKX (N : ℕ) : List (List QI) → List (List QI) → Bool
  | [], [] => true
  | J :: Js, T :: Ts => withinX N J T && rowsOKX N Js Ts
  | _, _ => false

theorem forall₂_tayMem_of_rowsOK {N : ℕ} {θ : ℝ} :
    ∀ (JCs JXs Ts : List (List QI)) (vs : List ℝ), rowsOKC N JCs Ts = true →
      rowsOKX N JXs Ts = true →
      List.Forall₂ (TayMem (N + 2) θ) (List.zipWith (tayRow N) JCs JXs) vs →
      List.Forall₂ (TayMem (N + 2) θ) Ts vs
  | [], [], [], _, _, _, h => by
    cases h
    exact List.Forall₂.nil
  | JC :: JCs, JX :: JXs, T :: Ts, _, hC, hX, h => by
    simp only [rowsOKC, rowsOKX, Bool.and_eq_true] at hC hX
    cases h with
    | cons hv h' =>
      exact List.Forall₂.cons (tayMem_of_withinCX hC.1 hX.1 hv)
        (forall₂_tayMem_of_rowsOK JCs JXs Ts _ hC.2 hX.2 h')
  | [], [], _ :: _, _, hC, _, _ => by simp [rowsOKC] at hC
  | [], _ :: _, [], _, _, hX, _ => by simp [rowsOKX] at hX
  | [], _ :: _, _ :: _, _, hC, _, _ => by simp [rowsOKC] at hC
  | _ :: _, [], [], _, hC, _, _ => by simp [rowsOKC] at hC
  | _ :: _, [], _ :: _, _, _, hX, _ => by simp [rowsOKX] at hX
  | _ :: _, _ :: _, [], _, hC, _, _ => by simp [rowsOKC] at hC

/-! ## An interval of the grid -/

/-- An interval `[x0, x1]` of reciprocal parameters with a centre `xc`, a cell that encloses the
diagonal square of the interval and a cell that encloses the centre. -/
structure TCell where
  x0 : ℚ
  x1 : ℚ
  xc : ℚ
  CX : Cell
  CC : Cell

namespace TCell

/-- The enclosure of `θ = (1/xc − 1/x)/12` for `x` in the interval. -/
def theta (g : TCell) : QI := ⟨(g.xc⁻¹ - g.x0⁻¹) / 12, (g.xc⁻¹ - g.x1⁻¹) / 12⟩

theorem mem_theta {g : TCell} (hx0 : (0 : ℝ) < g.x0) {x : ℝ} (hx : x ∈ Set.Icc (g.x0 : ℝ) g.x1) :
    g.theta.Mem (((g.xc : ℝ)⁻¹ - x⁻¹) / 12) := by
  have hxp : 0 < x := lt_of_lt_of_le hx0 hx.1
  have h1 : x⁻¹ ≤ (g.x0 : ℝ)⁻¹ := inv_anti₀ hx0 hx.1
  have h2 : (g.x1 : ℝ)⁻¹ ≤ x⁻¹ := inv_anti₀ hxp hx.2
  refine ⟨?_, ?_⟩
  · show (((g.xc⁻¹ - g.x0⁻¹) / 12 : ℚ) : ℝ) ≤ _
    push_cast
    linarith
  · show _ ≤ (((g.xc⁻¹ - g.x1⁻¹) / 12 : ℚ) : ℝ)
    push_cast
    linarith

end TCell

/-- The enclosures on a cell, the atoms rounded outward to multiples of `2⁻ᵖ`. -/
def cellEnv (p : ℕ) (At : List MDD) (C : Cell) : IEnv := (IEnv.ofCell At C).round p

/-- The jets of order `n` of the registers of a `z`-side program on a cell. -/
def cellJets (n p Λ : ℕ) (At : List MDD) (prog : List IInstr) (C : Cell) : List (List QI) :=
  ISLP.runJN n (cellEnv p At C) (fun j => (atomJets Λ p (cellEnv p At C) n).getD j [])
    (monoJet (cellEnv p At C) n) prog []

/-- The jets at the centre of the listed registers of a `z`-side program. -/
def jetsTC (N p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : TCell) :
    List (List QI) :=
  ks.map fun i => (cellJets N p Λ At prog g.CC).getD i []

/-- The jets on the interval of the listed registers of a `z`-side program. -/
def jetsTX (N p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : TCell) :
    List (List QI) :=
  ks.map fun i => (cellJets (N + 1) p Λ At prog g.CX).getD i []

/-- The jets at the centre of `hOf` of the listed registers of a `z`-side program. -/
def jetsZC (N p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : TCell) :
    List (List QI) :=
  ks.map fun i => jetH N (cellEnv p At g.CC) ((cellJets (N + 2) p Λ At prog g.CC).getD i [])

/-- The jets on the interval of `hOf` of the listed registers of a `z`-side program. -/
def jetsZX (N p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : TCell) :
    List (List QI) :=
  ks.map fun i =>
    jetH (N + 1) (cellEnv p At g.CX) ((cellJets (N + 1 + 2) p Λ At prog g.CX).getD i [])

/-- The rows of the listed registers of a `z`-side program. -/
def rowsT (N p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : TCell) :
    List (List QI) :=
  List.zipWith (tayRow N) (jetsTC N p Λ At prog ks g) (jetsTX N p Λ At prog ks g)

/-- The rows of `hOf` of the listed registers of a `z`-side program. -/
def rowsZ (N p Λ : ℕ) (At : List MDD) (prog : List IInstr) (ks : List ℕ) (g : TCell) :
    List (List QI) :=
  List.zipWith (tayRow N) (jetsZC N p Λ At prog ks g) (jetsZX N p Λ At prog ks g)

/-- The two cells enclose the interval and the centre and lie inside the bounds of the models. -/
def cellsOK (k n : ℕ) (Bx : Bounds) (g : TCell) : Bool :=
  cellOKb k n ⟨g.x0, g.x1, g.x0, g.x1⟩ g.CX && cellOKb k n ⟨g.xc, g.xc, g.xc, g.xc⟩ g.CC &&
    decide (g.CX.hi.le Bx ∧ g.CC.hi.le Bx ∧ 0 < g.x0 ∧ g.x0 ≤ g.xc ∧ g.xc ≤ g.x1)

/-- The table contains the jets at the centre of the `τ`-side program (mirrored to the
`z`-side). The four checks of an interval are separate so that each is a small kernel check. -/
def intervalOKTC (k n p Λ N : ℕ) (Bx : Bounds) (At : List MDD) (progT : List IInstr)
    (kT : List ℕ) (g : TCell) (TA : List (List QI)) : Bool :=
  cellsOK k n Bx g && rowsOKC N (jetsTC N p Λ At progT kT g) TA

/-- The table contains the last entries of the jets on the interval of the `τ`-side program. -/
def intervalOKTX (k n p Λ N : ℕ) (Bx : Bounds) (At : List MDD) (progT : List IInstr)
    (kT : List ℕ) (g : TCell) (TA : List (List QI)) : Bool :=
  cellsOK k n Bx g && rowsOKX N (jetsTX N p Λ At progT kT g) TA

/-- The table contains the jets at the centre of `hOf` of the `z`-side program. -/
def intervalOKZC (k n p Λ N : ℕ) (Bx : Bounds) (At : List MDD) (progZ : List IInstr)
    (kZ : List ℕ) (g : TCell) (TZ : List (List QI)) : Bool :=
  cellsOK k n Bx g && rowsOKC N (jetsZC N p Λ At progZ kZ g) TZ

/-- The table contains the last entries of the jets on the interval of `hOf` of the `z`-side
program. -/
def intervalOKZX (k n p Λ N : ℕ) (Bx : Bounds) (At : List MDD) (progZ : List IInstr)
    (kZ : List ℕ) (g : TCell) (TZ : List (List QI)) : Bool :=
  cellsOK k n Bx g && rowsOKX N (jetsZX N p Λ At progZ kZ g) TZ

section Interval

variable {Bx : Bounds} {At : List MDD} {Λ N p k n : ℕ}

theorem jMem_cellJets {C : Cell} {e : NEnv} (hE : (cellEnv p At C).Sound (kernelAtoms Λ ++ []) e)
    (m : ℕ) (prog : List IInstr) (i : ℕ) :
    JMem Λ (kernelAtoms Λ ++ []) e m ((cellJets m p Λ At prog C).getD i [])
      ((ISLP.runExpr prog []).getD i (.cst 0)) :=
  ISLP.mem_runJN hE (jMem_atomJets hE m) (jMem_monoJet hE m) prog i

/-- What a checked pair of cells provides. -/
theorem cellsOK_spec (hAt : ISLP.AtomsOK Bx (fun _ => True) At (kernelAtoms Λ ++ []))
    (hB3 : 3 * Bx.bn < Bx.bd) {g : TCell} (hok : cellsOK k n Bx g = true) :
    (0 : ℝ) < g.x0 ∧ (g.x0 : ℝ) ≤ g.xc ∧ (g.xc : ℝ) ≤ g.x1 ∧ Real.exp (-(g.x1 : ℝ)⁻¹) < 1 / 3 ∧
      (cellEnv p At g.CC).Sound (kernelAtoms Λ ++ []) (recNEnv g.xc g.xc) ∧
      ∀ s ∈ Set.Icc (g.x0 : ℝ) g.x1,
        (cellEnv p At g.CX).Sound (kernelAtoms Λ ++ []) (recNEnv g.xc s) := by
  simp only [cellsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hX, hC⟩, hsubX, hsubC, h0, h0c, hc1⟩ := hok
  obtain ⟨hXv, hXm⟩ := cellOKb_spec k n _ _ hX
  obtain ⟨hCv, hCm⟩ := cellOKb_spec k n _ _ hC
  have h0' : (0 : ℝ) < g.x0 := by exact_mod_cast h0
  have h0c' : (g.x0 : ℝ) ≤ g.xc := by exact_mod_cast h0c
  have hc1' : (g.xc : ℝ) ≤ g.x1 := by exact_mod_cast hc1
  have hxc : (0 : ℝ) < g.xc := lt_of_lt_of_le h0' h0c'
  have hx1 : (0 : ℝ) < g.x1 := lt_of_lt_of_le hxc hc1'
  have hXmem : ∀ s ∈ Set.Icc (g.x0 : ℝ) g.x1, g.CX.Mem (recNEnv g.xc s) := fun s hs =>
    hXm _ _ hxc (lt_of_lt_of_le h0' hs.1) ⟨h0c', hc1', hs.1, hs.2⟩
  refine ⟨h0', h0c', hc1', ?_, ?_, ?_⟩
  · -- the nome of the right end of the interval is below the bound of the models
    have he := hXmem g.x1 ⟨h0c'.trans hc1', le_rfl⟩
    have hB := Bounds.mem_of_le hXv.2 hsubX he.2.2.2.2.2
    have hb : Real.exp (-(g.x1 : ℝ)⁻¹) * Bx.bd ≤ Bx.bn := hB.2.2.2.1
    have h3 : (3 : ℝ) * Bx.bn < Bx.bd := by exact_mod_cast hB3
    have hbd : (0 : ℝ) < Bx.bd := by
      have : 0 < Bx.bd := by omega
      exact_mod_cast this
    have h4 : Real.exp (-(g.x1 : ℝ)⁻¹) * 3 * Bx.bd < 1 * Bx.bd := by nlinarith
    have h5 := lt_of_mul_lt_mul_right h4 hbd.le
    linarith
  · exact IEnv.sound_round p (IEnv.sound_ofCell hAt hCv hsubC
      (hCm _ _ hxc hxc ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩))
  · exact fun s hs => IEnv.sound_round p (IEnv.sound_ofCell hAt hXv hsubX (hXmem s hs))

/-- **The rows of a program enclose the Taylor coefficients of its registers.** -/
theorem forall₂_rowsT (hAt : ISLP.AtomsOK Bx (fun _ => True) At (kernelAtoms Λ ++ []))
    (hB3 : 3 * Bx.bn < Bx.bd) {g : TCell} (hok : cellsOK k n Bx g = true) (prog : List IInstr)
    {x : ℝ} (hx : x ∈ Set.Icc (g.x0 : ℝ) g.x1) :
    ∀ ks : List ℕ, List.Forall₂ (TayMem (N + 2) (((g.xc : ℝ)⁻¹ - x⁻¹) / 12))
      (rowsT N p Λ At prog ks g)
      (ks.map fun i => IExpr.evalB (kernelAtoms Λ ++ []) ((ISLP.runExpr prog []).getD i (.cst 0))
        (recNEnv g.xc x)) := by
  obtain ⟨h0, h0c, hc1, hnome, hEC, hEX⟩ := cellsOK_spec (p := p) hAt hB3 hok
  intro ks
  induction ks with
  | nil => exact List.Forall₂.nil
  | cons i ks ih =>
    exact List.Forall₂.cons (tayMem_row h0 h0c hc1 hx hnome (jMem_cellJets hEC N prog i)
      (fun s hs => jMem_cellJets (hEX s hs) (N + 1) prog i)) ih

/-- **The rows of `hOf` of the registers of a program.** -/
theorem forall₂_rowsZ (hAt : ISLP.AtomsOK Bx (fun _ => True) At (kernelAtoms Λ ++ []))
    (hB3 : 3 * Bx.bn < Bx.bd) {g : TCell} (hok : cellsOK k n Bx g = true) (prog : List IInstr)
    {x : ℝ} (hx : x ∈ Set.Icc (g.x0 : ℝ) g.x1) :
    ∀ ks : List ℕ, List.Forall₂ (TayMem (N + 2) (((g.xc : ℝ)⁻¹ - x⁻¹) / 12))
      (rowsZ N p Λ At prog ks g)
      (ks.map fun i => IExpr.evalB (kernelAtoms Λ ++ [])
        (IExpr.hOf Λ ((ISLP.runExpr prog []).getD i (.cst 0))) (recNEnv g.xc x)) := by
  obtain ⟨h0, h0c, hc1, hnome, hEC, hEX⟩ := cellsOK_spec (p := p) hAt hB3 hok
  intro ks
  induction ks with
  | nil => exact List.Forall₂.nil
  | cons i ks ih =>
    exact List.Forall₂.cons (tayMem_row h0 h0c hc1 hx hnome
      (jMem_jetH hEC (jMem_cellJets hEC (N + 2) prog i))
      (fun s hs => jMem_jetH (hEX s hs) (jMem_cellJets (hEX s hs) (N + 1 + 2) prog i))) ih

end Interval

/-! ## The values of the two sides -/

section Values

variable {Λ : ℕ} {progT progZ : List IInstr} {kT kZ : List ℕ}

/-- The values of the mirrored `τ`-side program are the values of the `τ`-side factors. -/
theorem tauVals_eq
    (hT : (kT.map fun i => (ISLP.runExpr progT []).getD i (.cst 0)) =
      (leechTauE Λ).map IExpr.swap)
    (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true) (xc u : ℝ) :
    (kT.map fun i => IExpr.evalB (kernelAtoms Λ ++ []) ((ISLP.runExpr progT []).getD i (.cst 0))
      (recNEnv xc (1 / (π * u)))) = leechTauVals Λ u := by
  have e : (kT.map fun i => IExpr.evalB (kernelAtoms Λ ++ [])
      ((ISLP.runExpr progT []).getD i (.cst 0)) (recNEnv xc (1 / (π * u)))) =
      ((kT.map fun i => (ISLP.runExpr progT []).getD i (.cst 0)).map fun y =>
        IExpr.evalB (kernelAtoms Λ ++ []) y (recNEnv xc (1 / (π * u)))) := by
    rw [List.map_map]
    rfl
  rw [e, hT, List.map_map, leechTauVals]
  refine List.map_congr_left fun x hx => ?_
  show IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.swap x)
      ⟨Real.exp (-xc⁻¹), Real.exp (-(1 / (π * u))⁻¹), xc, 1 / (π * u), Real.log 2⟩ = _
  rw [IExpr.evalB_swap]
  refine IExpr.evalB_congr_tau _ (hτ x hx) ?_ rfl rfl
  show Real.exp (-(1 / (π * u))⁻¹) = Real.exp (-π * u)
  rw [one_div, inv_inv, neg_mul]

/-- The values of `hOf` of the `z`-side program are the values of the second-derivative
expressions. -/
theorem zVals_eq
    (hZ : (kZ.map fun i => (ISLP.runExpr progZ []).getD i (.cst 0)) = leechZE Λ)
    (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true) (xc t : ℝ) :
    (kZ.map fun i => IExpr.evalB (kernelAtoms Λ ++ [])
      (IExpr.hOf Λ ((ISLP.runExpr progZ []).getD i (.cst 0))) (recNEnv xc (1 / (π * t)))) =
      leechZVals Λ t := by
  have e : (kZ.map fun i => IExpr.evalB (kernelAtoms Λ ++ [])
      (IExpr.hOf Λ ((ISLP.runExpr progZ []).getD i (.cst 0))) (recNEnv xc (1 / (π * t)))) =
      ((kZ.map fun i => (ISLP.runExpr progZ []).getD i (.cst 0)).map fun y =>
        IExpr.evalB (kernelAtoms Λ ++ []) (IExpr.hOf Λ y) (recNEnv xc (1 / (π * t)))) := by
    rw [List.map_map]
    rfl
  rw [e, hZ, leechZVals]
  refine List.map_congr_left fun x hx => ?_
  refine IExpr.evalB_congr_z _ (hz x hx) ?_ rfl rfl
  show Real.exp (-(1 / (π * t))⁻¹) = Real.exp (-π * t)
  rw [one_div, inv_inv, neg_mul]

end Values

/-! ## The certificate -/

/-- One `τ`-side table against all `z`-side tables: the lower bounds are positive. -/
def pairRowOK (N : ℕ) (a : TCell × List (List QI) × List (List QI))
    (gsZ : List (TCell × List (List QI) × List (List QI))) : Bool :=
  gsZ.all fun z =>
    decide (0 < (pairI (N + 2) a.2.1 z.2.2 (tpows (N + 2) a.1.theta)
      (tpows (N + 2) z.1.theta)).lo)

/-- All pairs of a `τ`-side table and a `z`-side table have a positive lower bound. -/
def pairOKT (N : ℕ) (gsA gsZ : List (TCell × List (List QI) × List (List QI))) : Bool :=
  gsA.all fun a => pairRowOK N a gsZ

theorem pairOKT_of_rows {N : ℕ} {gsA gsZ : List (TCell × List (List QI) × List (List QI))}
    (h : ∀ a ∈ gsA, pairRowOK N a gsZ = true) : pairOKT N gsA gsZ = true :=
  List.all_eq_true.mpr h

/-- **The corner certificate for `d = 24` from a grid.** Every interval carries two cells and two
tables; the intervals cover the reciprocals of `[1/c₀, c₀]`; all pairs of tables are positive. -/
theorem leechCornerPos_of_grid {Bx : Bounds} {At : List MDD} {Λ N p k n : ℕ}
    {progT progZ : List IInstr} {kT kZ : List ℕ}
    (hAt : ISLP.AtomsOK Bx (fun _ => True) At (kernelAtoms Λ ++ []))
    (hB3 : 3 * Bx.bn < Bx.bd)
    (hT : (kT.map fun i => (ISLP.runExpr progT []).getD i (.cst 0)) =
      (leechTauE Λ).map IExpr.swap)
    (hZ : (kZ.map fun i => (ISLP.runExpr progZ []).getD i (.cst 0)) = leechZE Λ)
    (hτ : ∀ x ∈ leechTauE Λ, x.tauOnly = true)
    (hz : ∀ x ∈ leechZE Λ, (IExpr.hOf Λ x).zOnly = true)
    {gs : List (TCell × List (List QI) × List (List QI))}
    (hintTC : ∀ g ∈ gs, intervalOKTC k n p Λ N Bx At progT kT g.1 g.2.1 = true)
    (hintTX : ∀ g ∈ gs, intervalOKTX k n p Λ N Bx At progT kT g.1 g.2.1 = true)
    (hintZC : ∀ g ∈ gs, intervalOKZC k n p Λ N Bx At progZ kZ g.1 g.2.2 = true)
    (hintZX : ∀ g ∈ gs, intervalOKZX k n p Λ N Bx At progZ kZ g.1 g.2.2 = true)
    (hpair : pairOKT N gs gs = true) {lo hi : ℚ}
    (hcov : coverOK hi lo (gs.map fun g => (⟨g.1.x0, g.1.x1, g.1.CX⟩ : GCell)) = true) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hlo : (lo : ℝ) ≤ 1 / (π * c₀)) (hhi : c₀ / π ≤ hi) :
    LeechCornerPos Λ c₀ := by
  have hπ := Real.pi_pos
  have key : ∀ v : ℝ, c₀⁻¹ ≤ v → v ≤ c₀ →
      ∃ g ∈ gs, 1 / (π * v) ∈ Set.Icc (g.1.x0 : ℝ) g.1.x1 := by
    intro v hv hv'
    have hv0 : 0 < v := (inv_pos.mpr hc₀).trans_le hv
    have h1 : (lo : ℝ) ≤ 1 / (π * v) := by
      refine hlo.trans ?_
      exact one_div_le_one_div_of_le (mul_pos hπ hv0) (mul_le_mul_of_nonneg_left hv' hπ.le)
    have h2 : 1 / (π * v) ≤ hi := by
      refine le_trans ?_ hhi
      rw [div_le_div_iff₀ (mul_pos hπ hv0) hπ]
      have h3 : 1 ≤ c₀ * v := by
        have h4 := mul_le_mul_of_nonneg_left hv hc₀.le
        rwa [mul_inv_cancel₀ hc₀.ne'] at h4
      nlinarith [mul_nonneg hπ.le (sub_nonneg.mpr h3)]
    obtain ⟨g0, hg0, hb⟩ := exists_of_coverOK lo _ hcov _ h1 h2
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg0
    exact ⟨g, hg, hb⟩
  intro u t hu hu' ht ht'
  obtain ⟨gu, hgu, hxu⟩ := key u hu hu'
  obtain ⟨gt, hgt, hxt⟩ := key t ht ht'
  have hokT := hintTC gu hgu
  have hokTX := hintTX gu hgu
  have hokZ := hintZC gt hgt
  have hokZX := hintZX gt hgt
  simp only [intervalOKTC, Bool.and_eq_true] at hokT
  simp only [intervalOKTX, Bool.and_eq_true] at hokTX
  simp only [intervalOKZC, Bool.and_eq_true] at hokZ
  simp only [intervalOKZX, Bool.and_eq_true] at hokZX
  have hA : List.Forall₂ (TayMem (N + 2) (((gu.1.xc : ℝ)⁻¹ - (1 / (π * u))⁻¹) / 12)) gu.2.1
      (leechTauVals Λ u) := by
    have h1 := forall₂_rowsT (N := N) (p := p) hAt hB3 hokT.1 progT hxu kT
    rw [tauVals_eq hT hτ] at h1
    exact forall₂_tayMem_of_rowsOK _ _ _ _ hokT.2 hokTX.2 h1
  have hZ' : List.Forall₂ (TayMem (N + 2) (((gt.1.xc : ℝ)⁻¹ - (1 / (π * t))⁻¹) / 12)) gt.2.2
      (leechZVals Λ t) := by
    have h1 := forall₂_rowsZ (N := N) (p := p) hAt hB3 hokZ.1 progZ hxt kZ
    rw [zVals_eq hZ hz] at h1
    exact forall₂_tayMem_of_rowsOK _ _ _ _ hokZ.2 hokZX.2 h1
  have h0u := (cellsOK_spec (p := p) hAt hB3 hokT.1).1
  have h0t := (cellsOK_spec (p := p) hAt hB3 hokZ.1).1
  have hmem := mem_pairI hA hZ'
    (fun q hq => mem_tpows (TCell.mem_theta h0u hxu) hq)
    (fun q hq => mem_tpows (TCell.mem_theta h0t hxt) hq)
  have hp : 0 < (pairI (N + 2) gu.2.1 gt.2.2 (tpows (N + 2) gu.1.theta)
      (tpows (N + 2) gt.1.theta)).lo := by
    simp only [pairOKT, pairRowOK, List.all_eq_true, decide_eq_true_eq] at hpair
    exact hpair gu hgu gt hgt
  have hp' : (0 : ℝ) < ((pairI (N + 2) gu.2.1 gt.2.2 (tpows (N + 2) gu.1.theta)
      (tpows (N + 2) gt.1.theta)).lo : ℝ) := by exact_mod_cast hp
  exact lt_of_lt_of_le hp' hmem.1

end E8Leech.Kron
