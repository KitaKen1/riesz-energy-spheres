import E8Leech.KronRedAtoms

/-!
# Staged evaluation of the function models

The kernel keeps its reduction caches for the whole of one declaration, so the memory of a
`decide +kernel` check grows with the work inside that declaration; the model of one logarithm
of a theta function needs several gigabytes when it is evaluated in one piece. The lemmas below
cut the models of `1/(1+g)`, `Λ log(1+g)`, `Λ log(1+z)/z`, of its divided difference, and of the
two logarithm atoms into single products. Every hypothesis is a closed equation between a small
computation on literals and a literal, to be checked by the kernel in its own declaration.

* `IPoly.powMaj_succ_of`, `MTM.horner_cons_of`, `MTM.hsumAux_cons_of`: one step of a chain.
* `MTM.inv1p_eq_of`, `MTM.log1p_eq_of`, `MTM.logRatio_eq_of`, `MTM.logRatioDD_eq_of`: a function
  model from its two chains.
* `MDD.log_eq_of`, `MDD.rlog_eq_of`: a logarithm atom from its parts.
* `kernelAtomModels_eq_of`, `sAtomModels_eq_of`: the lists of atom models from their entries.
-/

namespace E8Leech.Kron

open E8Leech.Taylor IPoly

namespace IPoly

/-- One step of the capped powers of a majorant. -/
theorem powMaj_succ_of {B : Bounds} {Dcap : ℕ} {G : IPoly} {k : ℕ} {P' P : IPoly}
    (h : powMaj B Dcap G k = P') (h' : cap B Dcap (mulK G P') = P) :
    powMaj B Dcap G (k + 1) = P := by
  subst h h'
  rfl

end IPoly

namespace MTM

/-- One Horner step from the value of the tail. -/
theorem horner_cons_of {B : Bounds} {D Dcap : ℕ} {T : MTM} {c : ℤ} {cs : List ℤ} {H' H : MTM}
    (h : horner B D Dcap T cs = H') (h' : (const c).add (mul B D Dcap T H') = H) :
    horner B D Dcap T (c :: cs) = H := by
  subst h h'
  rfl

/-- `1/(1+g)` from its Horner chain and the powers of its majorant. -/
theorem inv1p_eq_of {B : Bounds} {D Dcap K : ℕ} {T H R : MTM} {cs : List ℤ} {G P : IPoly}
    (hc : invCoeffs K = cs) (hH : horner B D Dcap T cs = H) (hG : absMaj B T = G)
    (hP : powMaj B Dcap G K = P)
    (hR : (⟨H.P, IPoly.add H.R (IPoly.scale 2 P)⟩ : MTM) = R) : inv1p B D Dcap K T = R := by
  subst hc hH hG hP hR
  rfl

/-- `Λ log(1+g)` from its Horner chain and the powers of its majorant. -/
theorem log1p_eq_of {B : Bounds} {D Dcap Λ n : ℕ} {T H R : MTM} {cs : List ℤ} {G P : IPoly}
    (hc : logCoeffs Λ n = cs) (hH : horner B D Dcap T cs = H) (hG : absMaj B T = G)
    (hP : powMaj B Dcap G (n + 1) = P)
    (hR : (⟨H.P, IPoly.add H.R (IPoly.scale ((2 * Λ : ℕ) : ℤ) P)⟩ : MTM) = R) :
    log1p B D Dcap Λ n T = R := by
  subst hc hH hG hP hR
  rfl

/-- `Λ log(1+z)/z` from its Horner chain and the powers of its majorant. -/
theorem logRatio_eq_of {B : Bounds} {D Dcap Λ n : ℕ} {T H R : MTM} {cs : List ℤ} {G P : IPoly}
    (hc : logRatioCoeffs Λ n = cs) (hH : horner B D Dcap T cs = H) (hG : absMaj B T = G)
    (hP : powMaj B Dcap G n = P)
    (hR : (⟨H.P, IPoly.add H.R (IPoly.scale ((2 * Λ : ℕ) : ℤ) P)⟩ : MTM) = R) :
    logRatio B D Dcap Λ n T = R := by
  subst hc hH hG hP hR
  rfl

/-- One step of the recurrence of the complete homogeneous sums. -/
theorem hsumAux_cons_of {B : Bounds} {D Dcap : ℕ} {P Q h qp acc h' qp' acc' R : MTM} {c : ℤ}
    {cs : List ℤ} (hq : mul B D Dcap qp Q = qp') (hh : (mul B D Dcap P h).add qp' = h')
    (ha : acc.add (h.scale c) = acc') (hr : hsumAux B D Dcap P Q cs h' qp' acc' = R) :
    hsumAux B D Dcap P Q (c :: cs) h qp acc = R := by
  subst hq hh ha hr
  rfl

/-- The divided difference of `Λ log(1+z)/z` from its chain and the powers of its majorant. -/
theorem logRatioDD_eq_of {B : Bounds} {D Dcap Λ n : ℕ} {P Q H R : MTM} {cs : List ℤ}
    {G M : IPoly} (hc : ((List.range n).map fun k => logRatioCoeffZ Λ (k + 1)) = cs)
    (hH : hsumAux B D Dcap P Q cs (const 1) (const 1) zero = H)
    (hG : IPoly.add (absMaj B P) (absMaj B Q) = G) (hM : powMaj B Dcap G n = M)
    (hR : (⟨H.P, IPoly.add H.R (IPoly.scale ((2 * Λ : ℕ) : ℤ) M)⟩ : MTM) = R) :
    logRatioDD B D Dcap Λ n P Q = R := by
  subst hc hH hG hM hR
  rfl

end MTM

namespace MDD

/-- The logarithm atom from its parts. -/
theorem log_eq_of {Bx : Bounds} {D Dcap Λ n K : ℕ} {X : MDD} {A B I W Z R Dd : MTM}
    (hA : MTM.log1p Bx D Dcap Λ n (X.A.sub (MTM.const 1)) = A)
    (hB : MTM.log1p Bx D Dcap Λ n (X.B.sub (MTM.const 1)) = B)
    (hI : MTM.inv1p Bx D Dcap K (X.A.sub (MTM.const 1)) = I)
    (hW : MTM.mul Bx D Dcap X.D I = W) (hZ : MTM.mul Bx D Dcap bmaMTM W = Z)
    (hR : MTM.logRatio Bx D Dcap Λ n Z = R) (hD : MTM.mul Bx D Dcap W R = Dd) :
    log Bx D Dcap Λ n K X = ⟨A, B, Dd⟩ := by
  subst hA hB hI hW hZ hR hD
  rfl

/-- The reduced logarithm atom from its parts. -/
theorem rlog_eq_of {Bx : Bounds} {D Dcap Λ n : ℕ} {d : MDD}
    {PA PB RA RB A B D1 RD S2 M2 D2 Dd : MTM}
    (hPA : MTM.mul Bx D Dcap nomeA d.A = PA) (hPB : MTM.mul Bx D Dcap nomeB d.B = PB)
    (hRA : MTM.logRatio Bx D Dcap Λ n PA = RA) (hRB : MTM.logRatio Bx D Dcap Λ n PB = RB)
    (hA : MTM.mul Bx D Dcap d.A RA = A) (hB : MTM.mul Bx D Dcap d.B RB = B)
    (hD1 : MTM.mul Bx D Dcap d.D RB = D1) (hRD : MTM.logRatioDD Bx D Dcap Λ n PA PB = RD)
    (hS2 : d.B.add (MTM.mul Bx D Dcap nomeA d.D) = S2) (hM2 : MTM.mul Bx D Dcap S2 RD = M2)
    (hD2 : MTM.mul Bx D Dcap d.A M2 = D2) (hD : D1.add D2 = Dd) :
    rlog Bx D Dcap Λ n d = ⟨A, B, Dd⟩ := by
  subst hPA hPB hRA hRB hA hB hD1 hRD hS2 hM2 hD2 hD
  rfl

end MDD

/-- The eight models of the kernel atoms from their entries. -/
theorem kernelAtomModels_eq_of {Bx : Bounds} {D Dcap Λ n K N NE : ℕ}
    {a0 a1 a2 a3 a4 a5 a6 a7 : MDD} (h0 : generatorMDD Bx N NE 0 = a0)
    (h1 : generatorMDD Bx N NE 1 = a1) (h2 : generatorMDD Bx N NE 2 = a2)
    (h3 : generatorMDD Bx N NE 3 = a3) (h4 : generatorMDD Bx N NE 4 = a4)
    (h5 : logarithmMDD Bx D Dcap Λ n K N NE 0 = a5)
    (h6 : logarithmMDD Bx D Dcap Λ n K N NE 1 = a6)
    (h7 : logarithmMDD Bx D Dcap Λ n K N NE 2 = a7) :
    kernelAtomModels Bx D Dcap Λ n K N NE = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  subst h0 h1 h2 h3 h4 h5 h6 h7
  rfl

/-- The twelve models of the atoms with the second variable inverted from their entries. -/
theorem sAtomModels_eq_of {Bx : Bounds} {D Dcap Λ n K N NE N' NE' : ℕ}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : MDD}
    (h : kernelAtomModels Bx D Dcap Λ n K N NE = [a0, a1, a2, a3, a4, a5, a6, a7])
    (h8 : devTheta4MDD Bx N' = a8) (h9 : devE2MDD Bx NE' = a9)
    (h10 : MDD.rlog Bx D Dcap Λ n (devTheta3MDD Bx N') = a10)
    (h11 : MDD.rlog Bx D Dcap Λ n (devTheta4MDD Bx N') = a11) :
    sAtomModels Bx D Dcap Λ n K N NE N' NE' =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  subst h8 h9 h10 h11
  rw [sAtomModels, h]
  rfl

/-- The logarithm atom `j` is the logarithm of its generator. -/
theorem logarithmMDD_eq_of {Bx : Bounds} {D Dcap Λ n K N NE : ℕ} (j : Fin 3) {X a : MDD}
    (hX : generatorMDD Bx N NE (logarithmIndex j) = X)
    (h : MDD.log Bx D Dcap Λ n K X = a) : logarithmMDD Bx D Dcap Λ n K N NE j = a := by
  subst hX h
  rfl

end E8Leech.Kron
