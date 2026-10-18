import E8Leech.KronPoly

/-!
# The kernel-fast product of integer polynomials

`IPoly.mulK P Q` multiplies the two base-`2^w` values, reads the digits of the product by binary
splitting and returns the decoded polynomial after the certificate check of `KronPoly`. The
decoder is not trusted: nothing is proved about it, and a wrong candidate is replaced by the
schoolbook product. Hence `eval_mulK` holds for all inputs.

The digit layout is `eu + ru (et + rt (el + rl (ea + ra eb)))`. A block is the group of
`ru rt rl` digits of one pair `(ea, eb)`. The value is kept as a positive and a negative part;
ranges of blocks on which the two parts agree are skipped by one comparison of big numbers, on
every level of the splitting.
-/

namespace E8Leech.Kron

namespace IPoly

/-- Fieldwise maximum of the exponents (a hint for the radices; checked by the certificate). -/
def maxExp : IPoly → NMono → NMono
  | [], b => b
  | (m, _) :: P, b =>
    maxExp P ⟨Nat.max m.ea b.ea, Nat.max m.eb b.eb, Nat.max m.eu b.eu, Nat.max m.et b.et,
      Nat.max m.el b.el⟩

/-- Read the `cnt` digits of one block, highest first, and prepend the nonzero coefficients.
`Mp` and `Mn` are the positive and the negative part of the value; their digits do not carry, so
a coefficient is the difference of two digits. -/
def scanBlock (w : ℕ) (r : Radix) (ea eb : ℕ) : ℕ → ℕ → ℕ → IPoly → IPoly
  | 0, _, _, acc => acc
  | cnt + 1, Mp, Mn, acc =>
    bif Nat.beq (Mp >>> (w * cnt)) (Mn >>> (w * cnt)) then
      scanBlock w r ea eb cnt (Mp % 2 ^ (w * cnt)) (Mn % 2 ^ (w * cnt)) acc
    else scanBlock w r ea eb cnt (Mp % 2 ^ (w * cnt)) (Mn % 2 ^ (w * cnt))
      ((⟨ea, eb, cnt % r.ru, cnt / r.ru % r.rt, cnt / r.ru / r.rt⟩,
        Int.subNatNat (Mp >>> (w * cnt)) (Mn >>> (w * cnt))) :: acc)

/-- Read `n` blocks of `bs` digits starting at block `pos`, by binary splitting. A range on
which the two parts agree has only zero coefficients and is skipped by one comparison. -/
def scanTree (w bs : ℕ) (r : Radix) : ℕ → ℕ → ℕ → ℕ → ℕ → IPoly → IPoly
  | 0, _, _, _, _, acc => acc
  | fuel + 1, n, pos, Mp, Mn, acc =>
    bif Nat.beq n 0 then acc
    else bif Nat.beq Mp Mn then acc
    else bif Nat.beq n 1 then scanBlock w r (pos % r.ra) (pos / r.ra) bs Mp Mn acc
    else
      scanTree w bs r fuel (n / 2) pos (Mp % 2 ^ (w * bs * (n / 2)))
        (Mn % 2 ^ (w * bs * (n / 2)))
        (scanTree w bs r fuel (n - n / 2) (pos + n / 2) (Mp >>> (w * bs * (n / 2)))
          (Mn >>> (w * bs * (n / 2))) acc)

/-- The candidate product: the digits of the positive and the negative part of the product of
the two values. -/
def decodeProduct (w : ℕ) (r : Radix) (rb : ℕ) (P Q : IPoly) : IPoly :=
  scanTree w (r.ru * r.rt * r.rl) r (Nat.log2 (r.ra * rb) + 2) (r.ra * rb) 0
    ((enc w r P).1 * (enc w r Q).1 + (enc w r P).2 * (enc w r Q).2)
    ((enc w r P).1 * (enc w r Q).2 + (enc w r P).2 * (enc w r Q).1) []

/-- A candidate is used only if its certificate check succeeds. -/
theorem eval_cond_cert (w : ℕ) (r : Radix) (bP bQ : NMono) (P Q R : IPoly) (e : NEnv) :
    eval (bif certOK w r bP bQ P Q R then R else mulSlow P Q) e = eval P e * eval Q e := by
  cases h : certOK w r bP bQ P Q R
  · simp only [cond_false]
    exact eval_mulSlow P Q e
  · simp only [cond_true]
    exact eval_of_certOK h e

/-- The radices of a product with exponent bounds `bP, bQ`. -/
def radixOf (bP bQ : NMono) : Radix :=
  ⟨bP.eu + bQ.eu + 1, bP.et + bQ.et + 1, bP.el + bQ.el + 1, bP.ea + bQ.ea + 1⟩

/-- The digit width of a product. -/
def widthOf (P Q : IPoly) : ℕ := Nat.log2 (normN P * normN Q) + 2

/-- **The certified product.** -/
def mulK (P Q : IPoly) : IPoly :=
  bif certOK (widthOf P Q) (radixOf (maxExp P NMono.one) (maxExp Q NMono.one))
      (maxExp P NMono.one) (maxExp Q NMono.one) P Q
      (decodeProduct (widthOf P Q) (radixOf (maxExp P NMono.one) (maxExp Q NMono.one))
        ((maxExp P NMono.one).eb + (maxExp Q NMono.one).eb + 1) P Q)
  then decodeProduct (widthOf P Q) (radixOf (maxExp P NMono.one) (maxExp Q NMono.one))
    ((maxExp P NMono.one).eb + (maxExp Q NMono.one).eb + 1) P Q
  else mulSlow P Q

theorem eval_mulK (P Q : IPoly) (e : NEnv) : eval (mulK P Q) e = eval P e * eval Q e :=
  eval_cond_cert _ _ _ _ P Q _ e

/-- The certificate check of `mulK`, for tests of the decoder. -/
def mulKChecked (P Q : IPoly) : Bool :=
  certOK (widthOf P Q) (radixOf (maxExp P NMono.one) (maxExp Q NMono.one))
    (maxExp P NMono.one) (maxExp Q NMono.one) P Q
    (decodeProduct (widthOf P Q) (radixOf (maxExp P NMono.one) (maxExp Q NMono.one))
      ((maxExp P NMono.one).eb + (maxExp Q NMono.one).eb + 1) P Q)

end IPoly

end E8Leech.Kron
