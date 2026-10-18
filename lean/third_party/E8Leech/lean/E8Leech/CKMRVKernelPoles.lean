import E8Leech.TriangleSqrtJ
import E8Leech.CKMRVKernelResidues
import E8Leech.CKMRVLaplaceAxis
import E8Leech.CKMRVLaplaceAxisMinus
import E8Leech.CKMRVPlusRemovable
import E8Leech.CKMRVCombinedKernels
import E8Leech.CKMRVRightRelations

/-!
# Poles of the CKMRV kernels in the right variable

Known answer first: `K(τ, z) = N(τ, z) / (j(τ) − j(z))` with `N` holomorphic in each variable.
At a simple zero of the denominator, the residue in `τ` (at fixed `z`) and the residue in `z`
(at fixed `τ`) are both `N / j'` up to sign. So the published left residues
`Res_{τ=z} K|T = −1/(2π)` (CKMRV Theorem 4.3(3), `CKMRVKernelResidues`) give the right residues
`Res_{z=τ−1} K(τ, ·) = 1/(2π)` and `Res_{z=Sτ−1} K(τ, ·) = ε (Sτ)⁴ / (2π)` (`ε = ±1` the left
`S`-eigenvalue). Other points are reached through Möbius changes of variable.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Two abstract limit lemmas -/

theorem tendsto_div_sub_of_hasDerivAt {J : ℂ → ℂ} {b d : ℂ} (hJ : HasDerivAt J d b)
    (hd : d ≠ 0) :
    Tendsto (fun w => (w - b) / (J w - J b)) (𝓝[≠] b) (𝓝 d⁻¹) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hJ).inv₀ hd
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [slope_def_field, inv_div]

/-- **Residue transfer.** A residue of `τ ↦ K(M w, b)` in the parametrizing variable `w` at `b`
(with `j ∘ M = j`) is minus the residue of `z ↦ K(M b, z)` at `b`. -/
theorem tendsto_residue_transfer {K N : ℂ → ℂ → ℂ} {J M : ℂ → ℂ} {a b L d : ℂ}
    (hMb : M b = a) (hMc : ContinuousAt M b)
    (hJM : ∀ᶠ w in 𝓝 b, J (M w) = J w) (hJ : HasDerivAt J d b) (hd : d ≠ 0)
    (hKa : ∀ᶠ w in 𝓝[≠] b, K (M w) b = N (M w) b / (J (M w) - J b))
    (hKb : ∀ᶠ z in 𝓝[≠] b, K a z = N a z / (J a - J z))
    (hN1 : ContinuousAt (fun τ => N τ b) a) (hN2 : ContinuousAt (N a) b)
    (hres : Tendsto (fun w => (w - b) * K (M w) b) (𝓝[≠] b) (𝓝 L)) :
    Tendsto (fun z => (z - b) * K a z) (𝓝[≠] b) (𝓝 (-L)) := by
  have hJab : J a = J b := by rw [← hMb]; exact hJM.self_of_nhds
  have hslope := tendsto_div_sub_of_hasDerivAt hJ hd
  have hN1' : Tendsto (fun w => N (M w) b) (𝓝[≠] b) (𝓝 (N a b)) := by
    have h := (hN1.comp_of_eq hMc hMb).tendsto
    simp only [Function.comp_def, hMb] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto (fun w => (w - b) * K (M w) b) (𝓝[≠] b) (𝓝 (N a b * d⁻¹)) := by
    refine (hN1'.mul hslope).congr' ?_
    filter_upwards [hKa, hJM.filter_mono nhdsWithin_le_nhds] with w hw hw'
    rw [hw, hw']
    ring
  have hL : L = N a b * d⁻¹ := tendsto_nhds_unique hres hlim1
  have hN2' : Tendsto (N a) (𝓝[≠] b) (𝓝 (N a b)) := hN2.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z => (z - b) * K a z) (𝓝[≠] b) (𝓝 (-(N a b * d⁻¹))) := by
    refine ((hN2'.mul hslope).neg).congr' ?_
    filter_upwards [hKb] with z hz
    rw [hz, hJab, show J b - J z = -(J z - J b) by ring, div_neg]
    ring
  rw [hL]
  exact hlim2

/-- **Transport.** Composing with a local biholomorphism `M` moves a simple pole (or a removable
point, `R = 0`) of `g` at `M q` to `q`. -/
theorem tendsto_residue_comp {g M h : ℂ → ℂ} {p q R m : ℂ} (hMq : M q = p)
    (hM : HasDerivAt M m q) (hm : m ≠ 0) (hh : ContinuousAt h q)
    (hg : Tendsto (fun u => (u - p) * g u) (𝓝[≠] p) (𝓝 R)) :
    Tendsto (fun w => (w - q) * (h w * g (M w))) (𝓝[≠] q) (𝓝 (h q * m⁻¹ * R)) := by
  have hne : ∀ᶠ w in 𝓝[≠] q, M w ≠ p := hM.eventually_ne (c := p) hm
  have hMt : Tendsto M (𝓝[≠] q) (𝓝[≠] p) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hne
    exact (hMq ▸ hM.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun w => (w - q) / (M w - p)) (𝓝[≠] q) (𝓝 m⁻¹) := by
    have := tendsto_div_sub_of_hasDerivAt hM hm
    simpa [hMq] using this
  have hgM := hg.comp hMt
  have hhq : Tendsto h (𝓝[≠] q) (𝓝 (h q)) := hh.tendsto.mono_left nhdsWithin_le_nhds
  refine ((hhq.mul hslope).mul hgM).congr' ?_
  filter_upwards [hne] with w hw
  have hw' : M w - p ≠ 0 := sub_ne_zero.mpr hw
  simp only [Function.comp]
  field_simp

/-! ## The kernels as functions on `ℂ × ℂ` -/

/-- `j` on `ℂ` (junk off `ℍ`). -/
def kleinJC (z : ℂ) : ℂ := kleinModularJ (ofComplex z)

theorem ofComplex_add_one {w : ℂ} (hw : 0 < w.im) :
    ofComplex (w + 1) = ModularGroup.T • ofComplex w := by
  apply UpperHalfPlane.ext
  rw [coe_T_smul, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos (by simpa using hw)]

theorem im_neg_inv_add_one_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-1 / (w + 1)).im := by
  have h : 0 < (w + 1).im := by simpa using hw
  have hne : w + 1 ≠ 0 := fun h0 => by simp [h0] at h
  rw [neg_div, Complex.neg_im, Complex.div_im]
  simp only [Complex.one_im, zero_mul, zero_div, Complex.one_re, one_mul, zero_sub, neg_neg]
  exact div_pos h (Complex.normSq_pos.mpr hne)

theorem ofComplex_ST {w : ℂ} (hw : 0 < w.im) :
    ofComplex (-1 / (w + 1)) = ModularGroup.S • ModularGroup.T • ofComplex w := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul, coe_T_smul, ofComplex_apply_of_im_pos hw,
    ofComplex_apply_of_im_pos (im_neg_inv_add_one_pos hw)]

theorem kleinJC_add_one {w : ℂ} (hw : 0 < w.im) : kleinJC (w + 1) = kleinJC w := by
  rw [kleinJC, kleinJC, ofComplex_add_one hw, kleinModularJ_T]

theorem kleinJC_ST {w : ℂ} (hw : 0 < w.im) : kleinJC (-1 / (w + 1)) = kleinJC w := by
  rw [kleinJC, kleinJC, ofComplex_ST hw, kleinModularJ_S, kleinModularJ_T]

theorem hasDerivAt_kleinJC (b : ℍ) : HasDerivAt kleinJC (kleinModularJDerivative b) (b : ℂ) :=
  hasDerivAt_kleinModularJ b

theorem continuousAt_comp_ofComplex {F : ℍ → ℂ} (hF : MDiff F) (b : ℍ) :
    ContinuousAt (fun w : ℂ => F (ofComplex w)) (b : ℂ) :=
  (analyticAt_of_upperHalfPlane_mdifferentiable hF b).continuousAt

theorem eventually_im_pos_nhds (b : ℍ) : ∀ᶠ w in 𝓝 (b : ℂ), 0 < w.im :=
  isOpen_upperHalfPlaneSet.mem_nhds b.im_pos

theorem mdifferentiable_eightMinusTauCoeff (j : Fin 3) :
    MDiff (fun τ : ℍ => eightMinusTauCoeff j τ) := by
  unfold eightMinusTauCoeff
  simp only [Fin.sum_univ_three]
  have hJ := mdifferentiable_kleinModularJ
  have hcore : ∀ i : Fin 3, MDiff (fun τ : ℍ => ckmrvEightMinusCore (kleinModularJ τ) i j) := by
    intro i
    fin_cases i <;> fin_cases j <;>
      simp [ckmrvEightMinusCore] <;> first
        | exact mdifferentiable_const
        | exact mdifferentiable_const.sub hJ
        | exact hJ
  exact (((mdifferentiable_ckmrvPsiBasis 0).mul (mdifferentiable_ckmrvModularFactor _)).mul
      (hcore 0)).add (((mdifferentiable_ckmrvPsiBasis 1).mul
      (mdifferentiable_ckmrvModularFactor _)).mul (hcore 1)) |>.add
    (((mdifferentiable_ckmrvPsiBasis 2).mul (mdifferentiable_ckmrvModularFactor _)).mul (hcore 2))

theorem mdifferentiable_eightMinusSingNum_left (z : ℍ) :
    MDiff (fun τ : ℍ => eightMinusSingNum τ z) := by
  unfold eightMinusSingNum
  exact (((mdifferentiable_eightMinusTauCoeff 0).mul mdifferentiable_const).add
    ((mdifferentiable_eightMinusTauCoeff 1).mul mdifferentiable_const)).add
    ((mdifferentiable_eightMinusTauCoeff 2).mul mdifferentiable_const)

/-! ## Right residues of `K₋⁽⁸⁾` at `T` and `ST` -/

/-- The numerator of `K₋⁽⁸⁾` on `ℂ × ℂ`. -/
def eightMinusNumC (τ z : ℂ) : ℂ :=
  ckmrvMinusScale⁻¹ * (eightMinusSingNum (ofComplex τ) (ofComplex z) /
    ModularForm.discriminant (ofComplex z))

theorem ckmrvEightMinusKernel_eq_numC (τ z : ℂ) :
    ckmrvEightMinusKernel (ofComplex τ) (ofComplex z) =
      eightMinusNumC τ z / (kleinJC τ - kleinJC z) := by
  rw [ckmrvEightMinusKernel_eq_sing, eightMinusNumC, kleinJC, kleinJC]
  ring

theorem continuousAt_eightMinusNumC_left (a b : ℍ) :
    ContinuousAt (fun τ => eightMinusNumC τ b) (a : ℂ) := by
  unfold eightMinusNumC
  have h := continuousAt_comp_ofComplex (mdifferentiable_eightMinusSingNum_left (ofComplex b)) a
  exact continuousAt_const.mul (h.div_const _)

theorem continuousAt_eightMinusNumC_right (a b : ℍ) :
    ContinuousAt (eightMinusNumC a) (b : ℂ) := by
  unfold eightMinusNumC
  have h1 := continuousAt_comp_ofComplex (mdifferentiable_eightMinusSingNum (ofComplex a)) b
  have h2 := continuousAt_comp_ofComplex mdifferentiable_modularDiscriminant b
  exact continuousAt_const.mul (h1.div h2 (ModularForm.discriminant_ne_zero _))

theorem tendsto_ckmrvEightMinusKernel_right_residue_T (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) * ckmrvEightMinusKernel (ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (1 / (2 * (π : ℂ)))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have ha : ((ModularGroup.T • b : ℍ) : ℂ) = (b : ℂ) + 1 := coe_T_smul b
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvEightMinusKernel (ofComplex (w + 1)) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
    refine (tendsto_ckmrvEightMinusKernel_residue_T b hA hB).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_add_one hw, UpperHalfPlane.ofComplex_apply]
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvEightMinusKernel (ofComplex τ)
      (ofComplex z)) (N := eightMinusNumC) (J := kleinJC) (M := fun w => w + 1)
    (a := (b : ℂ) + 1) (b := b) (d := kleinModularJDerivative b) rfl (by fun_prop)
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_add_one hw) (hasDerivAt_kleinJC b) hd
    (Eventually.of_forall fun w => ckmrvEightMinusKernel_eq_numC _ _)
    (Eventually.of_forall fun z => ckmrvEightMinusKernel_eq_numC _ _)
    (by rw [← ha]; exact continuousAt_eightMinusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_eightMinusNumC_right _ b) hres
  have e : -(-1 / (2 * (π : ℂ))) = 1 / (2 * (π : ℂ)) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

theorem tendsto_ckmrvEightMinusKernel_right_residue_ST (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) *
      ckmrvEightMinusKernel (ModularGroup.S • ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (((b : ℂ) + 1) ^ 4 / (2 * (π : ℂ)))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have hb1 : (b : ℂ) + 1 ≠ 0 := fun h => by
    have h2 : ((b : ℂ) + 1).im = 0 := by rw [h]; simp
    simp at h2
    linarith [b.im_pos]
  have ha : ((ModularGroup.S • ModularGroup.T • b : ℍ) : ℂ) = -1 / ((b : ℂ) + 1) := by
    rw [coe_S_smul, coe_T_smul]
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvEightMinusKernel (ofComplex (-1 / (w + 1))) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (((b : ℂ) + 1) ^ 4 * (-1 / (2 * (π : ℂ))))) := by
    have hT := tendsto_ckmrvEightMinusKernel_residue_T b hA hB
    have hpow : Tendsto (fun w : ℂ => (w + 1) ^ 4) (𝓝[≠] (b : ℂ)) (𝓝 (((b : ℂ) + 1) ^ 4)) :=
      ((continuous_id.add continuous_const).pow 4).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    refine (hpow.mul hT).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_ST hw, ckmrvEightMinusKernel_S, UpperHalfPlane.ofComplex_apply,
      coe_T_smul, ofComplex_apply_of_im_pos hw]
    ring
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvEightMinusKernel (ofComplex τ)
      (ofComplex z)) (N := eightMinusNumC) (J := kleinJC) (M := fun w => -1 / (w + 1))
    (a := -1 / ((b : ℂ) + 1)) (b := b) (d := kleinModularJDerivative b) rfl
    ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hb1))
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_ST hw) (hasDerivAt_kleinJC b) hd
    (Eventually.of_forall fun w => ckmrvEightMinusKernel_eq_numC _ _)
    (Eventually.of_forall fun z => ckmrvEightMinusKernel_eq_numC _ _)
    (by rw [← ha]; exact continuousAt_eightMinusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_eightMinusNumC_right _ b) hres
  have e : -(((b : ℂ) + 1) ^ 4 * (-1 / (2 * (π : ℂ)))) = ((b : ℂ) + 1) ^ 4 / (2 * (π : ℂ)) := by
    ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

/-! ## Right residues of `K₊⁽⁸⁾` at `T` and `ST` -/

/-- The normalized numerator of `K₊⁽⁸⁾` on `ℂ × ℂ`. -/
def eightPlusNumC (τ z : ℂ) : ℂ := ckmrvEightPlusNormalizedNumerator (ofComplex τ) (ofComplex z)

theorem ckmrvEightPlusKernel_eq_numC {τ z : ℂ} (h : kleinJC τ ≠ kleinJC z) :
    ckmrvEightPlusKernel (ofComplex τ) (ofComplex z) =
      eightPlusNumC τ z / (kleinJC τ - kleinJC z) :=
  ckmrvEightPlusKernel_quotient _ _ (sub_ne_zero.mpr h)

theorem continuousAt_eightPlusNumC_left (a b : ℍ) :
    ContinuousAt (fun τ => eightPlusNumC τ b) (a : ℂ) := by
  have h := mdifferentiable_ckmrvEightPlusNormalizedNumerator.comp
    (mdifferentiable_id.prodMk (mdifferentiable_const (c := ofComplex (b : ℂ))))
  exact continuousAt_comp_ofComplex h a

theorem continuousAt_eightPlusNumC_right (a b : ℍ) :
    ContinuousAt (eightPlusNumC a) (b : ℂ) := by
  have h := mdifferentiable_ckmrvEightPlusNormalizedNumerator.comp
    ((mdifferentiable_const (c := ofComplex (a : ℂ))).prodMk mdifferentiable_id)
  exact continuousAt_comp_ofComplex h b

theorem eventually_kleinJC_ne (b : ℍ) (hd : kleinModularJDerivative b ≠ 0) :
    ∀ᶠ w in 𝓝[≠] (b : ℂ), kleinJC w ≠ kleinJC b :=
  (hasDerivAt_kleinJC b).eventually_ne hd

theorem tendsto_ckmrvEightPlusKernel_right_residue_T (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) * ckmrvEightPlusKernel (ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (1 / (2 * (π : ℂ)))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have ha : ((ModularGroup.T • b : ℍ) : ℂ) = (b : ℂ) + 1 := coe_T_smul b
  have hJa : kleinJC ((b : ℂ) + 1) = kleinJC b := kleinJC_add_one b.im_pos
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvEightPlusKernel (ofComplex (w + 1)) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
    refine (tendsto_ckmrvEightPlusKernel_residue_T b hA hB).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_add_one hw, UpperHalfPlane.ofComplex_apply]
  have hev := eventually_kleinJC_ne b hd
  have hpos := (eventually_im_pos_nhds b).filter_mono (nhdsWithin_le_nhds (s := {(b : ℂ)}ᶜ))
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvEightPlusKernel (ofComplex τ)
      (ofComplex z)) (N := eightPlusNumC) (J := kleinJC) (M := fun w => w + 1)
    (a := (b : ℂ) + 1) (b := b) (d := kleinModularJDerivative b) rfl (by fun_prop)
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_add_one hw) (hasDerivAt_kleinJC b) hd
    (by
      filter_upwards [hev, hpos] with w hw hw'
      exact ckmrvEightPlusKernel_eq_numC (by rw [kleinJC_add_one hw']; exact hw))
    (by
      filter_upwards [hev] with z hz
      exact ckmrvEightPlusKernel_eq_numC (by rw [hJa]; exact hz.symm))
    (by rw [← ha]; exact continuousAt_eightPlusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_eightPlusNumC_right _ b) hres
  have e : -(-1 / (2 * (π : ℂ))) = 1 / (2 * (π : ℂ)) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

theorem tendsto_ckmrvEightPlusKernel_right_residue_ST (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) *
      ckmrvEightPlusKernel (ModularGroup.S • ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (-(((b : ℂ) + 1) ^ 4 / (2 * (π : ℂ))))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have hb1 : (b : ℂ) + 1 ≠ 0 := fun h => by
    have h2 : ((b : ℂ) + 1).im = 0 := by rw [h]; simp
    simp at h2
    linarith [b.im_pos]
  have ha : ((ModularGroup.S • ModularGroup.T • b : ℍ) : ℂ) = -1 / ((b : ℂ) + 1) := by
    rw [coe_S_smul, coe_T_smul]
  have hJa : kleinJC (-1 / ((b : ℂ) + 1)) = kleinJC b := kleinJC_ST b.im_pos
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvEightPlusKernel (ofComplex (-1 / (w + 1))) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (-((b : ℂ) + 1) ^ 4 * (-1 / (2 * (π : ℂ))))) := by
    have hT := tendsto_ckmrvEightPlusKernel_residue_T b hA hB
    have hpow : Tendsto (fun w : ℂ => -(w + 1) ^ 4) (𝓝[≠] (b : ℂ)) (𝓝 (-((b : ℂ) + 1) ^ 4)) :=
      (((continuous_id.add continuous_const).pow 4).neg).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    refine (hpow.mul hT).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_ST hw, ckmrvEightPlusKernel_S,
      UpperHalfPlane.ofComplex_apply, coe_T_smul, ofComplex_apply_of_im_pos hw]
    ring
  have hev := eventually_kleinJC_ne b hd
  have hpos := (eventually_im_pos_nhds b).filter_mono (nhdsWithin_le_nhds (s := {(b : ℂ)}ᶜ))
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvEightPlusKernel (ofComplex τ)
      (ofComplex z)) (N := eightPlusNumC) (J := kleinJC) (M := fun w => -1 / (w + 1))
    (a := -1 / ((b : ℂ) + 1)) (b := b) (d := kleinModularJDerivative b) rfl
    ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hb1))
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_ST hw) (hasDerivAt_kleinJC b) hd
    (by
      filter_upwards [hev, hpos] with w hw hw'
      exact ckmrvEightPlusKernel_eq_numC (by rw [kleinJC_ST hw']; exact hw))
    (by
      filter_upwards [hev] with z hz
      exact ckmrvEightPlusKernel_eq_numC (by rw [hJa]; exact hz.symm))
    (by rw [← ha]; exact continuousAt_eightPlusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_eightPlusNumC_right _ b) hres
  have e : -(-((b : ℂ) + 1) ^ 4 * (-1 / (2 * (π : ℂ)))) =
      -(((b : ℂ) + 1) ^ 4 / (2 * (π : ℂ))) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

/-! ## Simple poles on `ℂ` -/

/-- `f` has a simple pole with residue `R` at `p` (`R = 0`: a removable point). -/
def HasResidueAt (f : ℂ → ℂ) (p R : ℂ) : Prop :=
  Tendsto (fun z => (z - p) * f z) (𝓝[≠] p) (𝓝 R)

theorem HasResidueAt.of_tendsto {f : ℂ → ℂ} {p L : ℂ} (h : Tendsto f (𝓝[≠] p) (𝓝 L)) :
    HasResidueAt f p 0 := by
  have h0 : Tendsto (fun z => z - p) (𝓝[≠] p) (𝓝 0) :=
    ((continuous_sub_right p).tendsto' p 0 (sub_self p)).mono_left nhdsWithin_le_nhds
  unfold HasResidueAt
  simpa using h0.mul h

theorem HasResidueAt.add {f g : ℂ → ℂ} {p R S : ℂ} (hf : HasResidueAt f p R)
    (hg : HasResidueAt g p S) : HasResidueAt (fun z => f z + g z) p (R + S) := by
  unfold HasResidueAt at *
  exact (Tendsto.add hf hg).congr fun z => by ring

theorem HasResidueAt.sub {f g : ℂ → ℂ} {p R S : ℂ} (hf : HasResidueAt f p R)
    (hg : HasResidueAt g p S) : HasResidueAt (fun z => f z - g z) p (R - S) := by
  unfold HasResidueAt at *
  exact (Tendsto.sub hf hg).congr fun z => by ring

theorem HasResidueAt.div_const {f : ℂ → ℂ} {p R : ℂ} (hf : HasResidueAt f p R) (c : ℂ) :
    HasResidueAt (fun z => f z / c) p (R / c) := by
  unfold HasResidueAt at *
  exact (Tendsto.div_const hf c).congr fun z => by ring

theorem HasResidueAt.congr {f g : ℂ → ℂ} {p R : ℂ} (hf : HasResidueAt f p R)
    (h : ∀ᶠ z in 𝓝[≠] p, f z = g z) : HasResidueAt g p R := by
  unfold HasResidueAt at *
  refine Tendsto.congr' ?_ hf
  filter_upwards [h] with z hz
  rw [hz]

/-- Transport of a simple pole through a local biholomorphism. -/
theorem HasResidueAt.comp {g M h f : ℂ → ℂ} {p q R m : ℂ} (hg : HasResidueAt g p R)
    (hMq : M q = p) (hM : HasDerivAt M m q) (hm : m ≠ 0) (hh : ContinuousAt h q)
    (hf : ∀ᶠ w in 𝓝[≠] q, f w = h w * g (M w)) : HasResidueAt f q (h q * m⁻¹ * R) := by
  have := tendsto_residue_comp hMq hM hm hh hg
  refine HasResidueAt.congr (f := fun w => h w * g (M w)) this ?_
  filter_upwards [hf] with w hw
  rw [hw]

/-! ## The combined kernels near the special points of the two triangles -/

theorem eventually_im_pos_nhdsWithin (b : ℍ) : ∀ᶠ w in 𝓝[≠] (b : ℂ), 0 < w.im :=
  (eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds

theorem im_neg_one_div_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hne : z ≠ 0 := fun h => by simp [h] at hz
  rw [neg_div, Complex.neg_im, Complex.div_im]
  simp only [Complex.one_im, zero_mul, zero_div, Complex.one_re, one_mul, zero_sub, neg_neg]
  exact div_pos hz (Complex.normSq_pos.mpr hne)

theorem ofComplex_neg_inv {z : ℂ} (hz : 0 < z.im) :
    ModularGroup.S • ofComplex (-1 / z) = ofComplex z := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul, ofComplex_apply_of_im_pos (im_neg_one_div_pos hz),
    ofComplex_apply_of_im_pos hz]
  have hne : z ≠ 0 := fun h => by simp [h] at hz
  field_simp

theorem hasDerivAt_neg_one_div {x : ℂ} (hx : x ≠ 0) :
    HasDerivAt (fun z : ℂ => -1 / z) (1 / x ^ 2) x := by
  have h := (hasDerivAt_inv hx).const_mul (-1)
  have e1 : (fun y : ℂ => -1 * y⁻¹) = fun z : ℂ => -1 / z := by funext z; ring
  have e2 : (-1 * -(x ^ 2)⁻¹ : ℂ) = 1 / x ^ 2 := by ring
  rw [e1, e2] at h
  exact h

/-- Removability at `Sτ` from the existing limit of `K(τ, S·) z²` at `τ`. -/
theorem hasResidueAt_zero_at_S {K : ℍ → ℍ → ℂ} (τ₀ : ℍ)
    (hlim : ∃ L : ℂ, Tendsto (fun w : ℂ => K τ₀ (ModularGroup.S • ofComplex w) *
      ((ofComplex w : ℍ) : ℂ) ^ 2) (𝓝[≠] (τ₀ : ℂ)) (𝓝 L)) :
    HasResidueAt (fun z => K τ₀ (ofComplex z)) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 := by
  obtain ⟨L, hL⟩ := hlim
  have hσ : ((ModularGroup.S • τ₀ : ℍ) : ℂ) = -1 / (τ₀ : ℂ) := coe_S_smul τ₀
  have hσ0 : ((ModularGroup.S • τ₀ : ℍ) : ℂ) ≠ 0 := ne_zero _
  have hMq : -1 / ((ModularGroup.S • τ₀ : ℍ) : ℂ) = (τ₀ : ℂ) := by
    rw [hσ]; have := ne_zero τ₀; field_simp
  have h := HasResidueAt.comp (h := fun z : ℂ => z ^ 2) (HasResidueAt.of_tendsto hL) hMq
    (hasDerivAt_neg_one_div hσ0) (by simpa using hσ0) (continuous_pow 2).continuousAt
    (f := fun z => K τ₀ (ofComplex z)) (by
      filter_upwards [eventually_im_pos_nhdsWithin (ModularGroup.S • τ₀)] with z hz
      have hz0 : z ≠ 0 := fun h => by simp [h] at hz
      rw [ofComplex_neg_inv hz, ofComplex_apply_of_im_pos (im_neg_one_div_pos hz)]
      field_simp)
  simpa using h

/-! ## The two kernels and their combinations at the special points -/

/-- Right variable of a kernel, read on `ℂ`. -/
def rightC (K : ℍ → ℍ → ℂ) (τ : ℍ) (z : ℂ) : ℂ := K τ (ofComplex z)

theorem rightC_eightKernel (τ : ℍ) (z : ℂ) : rightC ckmrvEightKernel τ z =
    (rightC ckmrvEightPlusKernel τ z + rightC ckmrvEightMinusKernel τ z) / 2 := rfl

theorem rightC_eightHatKernel (τ : ℍ) (z : ℂ) : rightC ckmrvEightHatKernel τ z =
    (rightC ckmrvEightPlusKernel τ z - rightC ckmrvEightMinusKernel τ z) / 2 := rfl

theorem im_sub_one_pos (w : ℍ) : 0 < ((w : ℂ) - 1).im := by simpa using w.im_pos

theorem T_smul_ofComplex_sub_one (w : ℍ) : ModularGroup.T • ofComplex ((w : ℂ) - 1) = w := by
  apply UpperHalfPlane.ext
  rw [coe_T_smul, ofComplex_apply_of_im_pos (im_sub_one_pos w)]
  ring

theorem eisensteinFour_ofComplex_sub_one (w : ℍ) :
    ModularForm.E₄ (ofComplex ((w : ℂ) - 1)) = ModularForm.E₄ w := by
  conv_rhs => rw [← T_smul_ofComplex_sub_one w]
  rw [← vadd_one_eq_T_smul, eisensteinFour_vadd_one]

theorem eisensteinSix_ofComplex_sub_one (w : ℍ) :
    ModularForm.E₆ (ofComplex ((w : ℂ) - 1)) = ModularForm.E₆ w := by
  conv_rhs => rw [← T_smul_ofComplex_sub_one w]
  rw [← vadd_one_eq_T_smul, eisensteinSix_vadd_one]

theorem S_smul_T_smul_ofComplex_S_sub_one (w : ℍ) :
    ModularGroup.S • ModularGroup.T • ofComplex (((ModularGroup.S • w : ℍ) : ℂ) - 1) = w := by
  rw [T_smul_ofComplex_sub_one, S_smul_S_smul]

section SpecialPoints

variable {τ₀ : ℍ} (hA : ModularForm.E₄ τ₀ ≠ 0) (hB : ModularForm.E₆ τ₀ ≠ 0)
include hA hB

theorem hasResidueAt_plus_self : HasResidueAt (rightC ckmrvEightPlusKernel τ₀) τ₀ 0 := by
  obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightPlusKernel_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩)
  exact HasResidueAt.of_tendsto hL

theorem hasResidueAt_minus_self : HasResidueAt (rightC ckmrvEightMinusKernel τ₀) τ₀ 0 := by
  obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightMinusKernel_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩)
  exact HasResidueAt.of_tendsto hL

theorem hasResidueAt_plus_S :
    HasResidueAt (rightC ckmrvEightPlusKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_zero_at_S τ₀ (exists_tendsto_ckmrvEightPlusKernel_S_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩))

theorem hasResidueAt_minus_S :
    HasResidueAt (rightC ckmrvEightMinusKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_zero_at_S τ₀ (exists_tendsto_ckmrvEightMinusKernel_S_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩))

theorem hasResidueAt_T_of {K : ℍ → ℍ → ℂ} {R : ℂ}
    (hK : ∀ b : ℍ, ModularForm.E₄ b ≠ 0 → ModularForm.E₆ b ≠ 0 →
      Tendsto (fun z : ℂ => (z - b) * K (ModularGroup.T • b) (ofComplex z))
        (𝓝[≠] (b : ℂ)) (𝓝 R)) :
    HasResidueAt (rightC K τ₀) ((τ₀ : ℂ) - 1) R := by
  have h := hK (ofComplex ((τ₀ : ℂ) - 1))
    (by rw [eisensteinFour_ofComplex_sub_one]; exact hA)
    (by rw [eisensteinSix_ofComplex_sub_one]; exact hB)
  rw [T_smul_ofComplex_sub_one, ofComplex_apply_of_im_pos (im_sub_one_pos τ₀)] at h
  exact h

theorem hasResidueAt_plus_T : HasResidueAt (rightC ckmrvEightPlusKernel τ₀) ((τ₀ : ℂ) - 1)
    (1 / (2 * (π : ℂ))) :=
  hasResidueAt_T_of hA hB tendsto_ckmrvEightPlusKernel_right_residue_T

theorem hasResidueAt_minus_T : HasResidueAt (rightC ckmrvEightMinusKernel τ₀) ((τ₀ : ℂ) - 1)
    (1 / (2 * (π : ℂ))) :=
  hasResidueAt_T_of hA hB tendsto_ckmrvEightMinusKernel_right_residue_T

theorem hasResidueAt_ST_of {K : ℍ → ℍ → ℂ} {R : ℂ → ℂ}
    (hK : ∀ b : ℍ, ModularForm.E₄ b ≠ 0 → ModularForm.E₆ b ≠ 0 →
      Tendsto (fun z : ℂ => (z - b) * K (ModularGroup.S • ModularGroup.T • b) (ofComplex z))
        (𝓝[≠] (b : ℂ)) (𝓝 (R ((b : ℂ) + 1)))) :
    HasResidueAt (rightC K τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (R ((ModularGroup.S • τ₀ : ℍ) : ℂ)) := by
  have hz := ne_zero τ₀
  have h4 : ModularForm.E₄ (ModularGroup.S • τ₀) ≠ 0 := by
    rw [eisensteinFour_S]; exact mul_ne_zero (pow_ne_zero 4 hz) hA
  have h6 : ModularForm.E₆ (ModularGroup.S • τ₀) ≠ 0 := by
    rw [eisensteinSix_S]; exact mul_ne_zero (pow_ne_zero 6 hz) hB
  have h := hK (ofComplex (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1))
    (by rw [eisensteinFour_ofComplex_sub_one]; exact h4)
    (by rw [eisensteinSix_ofComplex_sub_one]; exact h6)
  rw [S_smul_T_smul_ofComplex_S_sub_one, ofComplex_apply_of_im_pos (im_sub_one_pos _),
    sub_add_cancel] at h
  exact h

theorem hasResidueAt_plus_ST :
    HasResidueAt (rightC ckmrvEightPlusKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (-(((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 4 / (2 * (π : ℂ)))) :=
  hasResidueAt_ST_of hA hB (R := fun x => -(x ^ 4 / (2 * (π : ℂ))))
    tendsto_ckmrvEightPlusKernel_right_residue_ST

theorem hasResidueAt_minus_ST :
    HasResidueAt (rightC ckmrvEightMinusKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 4 / (2 * (π : ℂ))) :=
  hasResidueAt_ST_of hA hB (R := fun x => x ^ 4 / (2 * (π : ℂ)))
    tendsto_ckmrvEightMinusKernel_right_residue_ST

/-! The combined kernels `𝒦 = (K₊ + K₋)/2` and `𝒦̂ = (K₊ − K₋)/2`. -/

omit hA hB in
theorem hasResidueAt_kernel_of {p R S T : ℂ}
    (hp : HasResidueAt (rightC ckmrvEightPlusKernel τ₀) p R)
    (hm : HasResidueAt (rightC ckmrvEightMinusKernel τ₀) p S) (hT : (R + S) / 2 = T) :
    HasResidueAt (rightC ckmrvEightKernel τ₀) p T := by
  have h := (hp.add hm).div_const 2
  rw [hT] at h
  exact h

omit hA hB in
theorem hasResidueAt_hatKernel_of {p R S T : ℂ}
    (hp : HasResidueAt (rightC ckmrvEightPlusKernel τ₀) p R)
    (hm : HasResidueAt (rightC ckmrvEightMinusKernel τ₀) p S) (hT : (R - S) / 2 = T) :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) p T := by
  have h := (hp.sub hm).div_const 2
  rw [hT] at h
  exact h

theorem hasResidueAt_kernel_self : HasResidueAt (rightC ckmrvEightKernel τ₀) τ₀ 0 :=
  hasResidueAt_kernel_of (hasResidueAt_plus_self hA hB) (hasResidueAt_minus_self hA hB)
    (by ring)

theorem hasResidueAt_hatKernel_self : HasResidueAt (rightC ckmrvEightHatKernel τ₀) τ₀ 0 :=
  hasResidueAt_hatKernel_of (hasResidueAt_plus_self hA hB) (hasResidueAt_minus_self hA hB)
    (by ring)

theorem hasResidueAt_kernel_S :
    HasResidueAt (rightC ckmrvEightKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_kernel_of (hasResidueAt_plus_S hA hB) (hasResidueAt_minus_S hA hB) (by ring)

theorem hasResidueAt_hatKernel_S :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_hatKernel_of (hasResidueAt_plus_S hA hB) (hasResidueAt_minus_S hA hB)
    (by ring)

theorem hasResidueAt_kernel_T :
    HasResidueAt (rightC ckmrvEightKernel τ₀) ((τ₀ : ℂ) - 1) (1 / (2 * (π : ℂ))) :=
  hasResidueAt_kernel_of (hasResidueAt_plus_T hA hB) (hasResidueAt_minus_T hA hB) (by ring)

theorem hasResidueAt_hatKernel_T :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) ((τ₀ : ℂ) - 1) 0 :=
  hasResidueAt_hatKernel_of (hasResidueAt_plus_T hA hB) (hasResidueAt_minus_T hA hB)
    (by ring)

theorem hasResidueAt_kernel_ST :
    HasResidueAt (rightC ckmrvEightKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1) 0 :=
  hasResidueAt_kernel_of (hasResidueAt_plus_ST hA hB) (hasResidueAt_minus_ST hA hB)
    (by ring)

theorem hasResidueAt_hatKernel_ST :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (-(((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 4 / (2 * (π : ℂ)))) :=
  hasResidueAt_hatKernel_of (hasResidueAt_plus_ST hA hB) (hasResidueAt_minus_ST hA hB)
    (by ring)

end SpecialPoints

/-! ## The `STS` relation in pointwise form -/

theorem slash_STS_apply (f : ℍ → ℂ) (w : ℍ) :
    (f ∣[(-2 : ℤ)] (ModularGroup.S * ModularGroup.T * ModularGroup.S)) w =
      f (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) * ((w : ℂ) - 1) ^ 2 := by
  have hw := ne_zero w
  rw [slash_STS, ckmrv_slash_S_apply, ckmrv_slash_T_apply_smul, ckmrv_slash_S_apply, coe_T_smul,
    coe_S_smul]
  simp only [neg_neg, zpow_two]
  field_simp
  ring

theorem coe_STS_smul (w : ℍ) :
    ((ModularGroup.S • ModularGroup.T • ModularGroup.S • w : ℍ) : ℂ) = (w : ℂ) / (1 - w) := by
  have hw := ne_zero w
  have hw1 : (1 : ℂ) - w ≠ 0 := fun h => by
    have h2 : ((1 : ℂ) - w).im = 0 := by rw [h]; simp
    simp at h2; linarith [w.im_pos]
  have hwm : (w : ℂ) - 1 ≠ 0 := fun h => hw1 (by linear_combination -h)
  rw [coe_S_smul, coe_T_smul, coe_S_smul]
  have e : (-1 / (w : ℂ) + 1) = ((w : ℂ) - 1) / w := by field_simp; ring
  rw [e, div_div_eq_mul_div, div_eq_div_iff hwm hw1]
  ring

theorem ckmrvEightPlusKernel_STS (τ w : ℍ) :
    ckmrvEightPlusKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) *
      ((w : ℂ) - 1) ^ 2 = ckmrvEightPlusKernel τ w := by
  have h := congrFun (ckmrvEightPlusKernel_right_rel_two τ) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [slash_STS_apply] at h
  linear_combination -h

theorem ckmrvEightMinusKernel_STS (τ w : ℍ) :
    ckmrvEightMinusKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) *
      ((w : ℂ) - 1) ^ 2 = -ckmrvEightMinusKernel τ w := by
  have h := congrFun (ckmrvEightMinusKernel_right_rel_two τ) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, one_mul] at h
  rw [slash_STS_apply] at h
  linear_combination h

/-- `𝒦̂ = 𝒦 |_{−2} STS`. -/
theorem ckmrvEightHatKernel_eq_STS (τ w : ℍ) : ckmrvEightHatKernel τ w =
    ((w : ℂ) - 1) ^ 2 * ckmrvEightKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) := by
  have h1 := ckmrvEightPlusKernel_STS τ w
  have h2 := ckmrvEightMinusKernel_STS τ w
  simp only [ckmrvEightHatKernel, ckmrvEightKernel]
  linear_combination (-h1 - h2) / 2

/-- `𝒦 = 𝒦̂ |_{−2} STS`. -/
theorem ckmrvEightKernel_eq_STS (τ w : ℍ) : ckmrvEightKernel τ w =
    ((w : ℂ) - 1) ^ 2 * ckmrvEightHatKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) := by
  have h1 := ckmrvEightPlusKernel_STS τ w
  have h2 := ckmrvEightMinusKernel_STS τ w
  simp only [ckmrvEightHatKernel, ckmrvEightKernel]
  linear_combination (-h1 + h2) / 2

theorem one_sub_ne_zero_of_im_pos {w : ℂ} (hw : 0 < w.im) : (1 : ℂ) - w ≠ 0 := fun h => by
  have h2 : ((1 : ℂ) - w).im = 0 := by rw [h]; simp
  simp at h2; linarith

theorem add_one_ne_zero_of_im_pos {w : ℂ} (hw : 0 < w.im) : w + 1 ≠ 0 := fun h => by
  have h2 : (w + 1).im = 0 := by rw [h]; simp
  simp at h2; linarith

theorem im_div_one_sub_pos {w : ℂ} (hw : 0 < w.im) : 0 < (w / (1 - w)).im := by
  have hne := one_sub_ne_zero_of_im_pos hw
  rw [Complex.div_im]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  rw [← sub_div]
  apply div_pos _ (Complex.normSq_pos.mpr hne)
  nlinarith

theorem im_div_add_one_pos {w : ℂ} (hw : 0 < w.im) : 0 < (w / (w + 1)).im := by
  have hne := add_one_ne_zero_of_im_pos hw
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
  rw [← sub_div]
  apply div_pos _ (Complex.normSq_pos.mpr hne)
  nlinarith

theorem STS_smul_ofComplex {w : ℂ} (hw : 0 < w.im) :
    ModularGroup.S • ModularGroup.T • ModularGroup.S • ofComplex w = ofComplex (w / (1 - w)) := by
  apply UpperHalfPlane.ext
  rw [coe_STS_smul, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos (im_div_one_sub_pos hw)]

/-- `𝒦̂(w) = (w − 1)² 𝒦(w / (1 − w))` on `ℂ`. -/
theorem rightC_hat_eq_STS {τ : ℍ} {w : ℂ} (hw : 0 < w.im) :
    rightC ckmrvEightHatKernel τ w = (w - 1) ^ 2 * rightC ckmrvEightKernel τ (w / (1 - w)) := by
  simp only [rightC]
  rw [ckmrvEightHatKernel_eq_STS, STS_smul_ofComplex hw, ofComplex_apply_of_im_pos hw]

/-- `𝒦̂(u) = (u + 1)² 𝒦(u / (u + 1))` on `ℂ` (the `TST` form). -/
theorem rightC_hat_eq_TST {τ : ℍ} {u : ℂ} (hu : 0 < u.im) :
    rightC ckmrvEightHatKernel τ u = (u + 1) ^ 2 * rightC ckmrvEightKernel τ (u / (u + 1)) := by
  have hw := im_div_add_one_pos hu
  have hu1 := add_one_ne_zero_of_im_pos hu
  have e : u / (u + 1) / (1 - u / (u + 1)) = u := by field_simp; ring
  have h := ckmrvEightKernel_eq_STS τ (ofComplex (u / (u + 1)))
  rw [STS_smul_ofComplex hw, e] at h
  have hc : ((ofComplex (u / (u + 1)) : ℍ) : ℂ) = u / (u + 1) := by
    rw [ofComplex_apply_of_im_pos hw]
  rw [hc] at h
  simp only [rightC]
  rw [h]
  field_simp
  ring

/-! ## Transported residues -/

theorem hasDerivAt_div_one_sub {q : ℂ} (hq : 1 - q ≠ 0) :
    HasDerivAt (fun w : ℂ => w / (1 - w)) (1 / (1 - q) ^ 2) q := by
  have h := (hasDerivAt_id' q).div ((hasDerivAt_id' q).const_sub 1) hq
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_div_add_one {q : ℂ} (hq : q + 1 ≠ 0) :
    HasDerivAt (fun w : ℂ => w / (w + 1)) (1 / (q + 1) ^ 2) q := by
  have h := (hasDerivAt_id' q).div ((hasDerivAt_id' q).add_const 1) hq
  refine h.congr_deriv ?_
  field_simp
  ring

theorem eventually_im_pos_of_im_pos {q : ℂ} (hq : 0 < q.im) : ∀ᶠ w in 𝓝[≠] q, 0 < w.im :=
  ((Complex.continuous_im.tendsto q).eventually (lt_mem_nhds hq)).filter_mono nhdsWithin_le_nhds

theorem hasResidueAt_hat_of_STS (τ : ℍ) {q p R : ℂ} (hq : 0 < q.im) (hMq : q / (1 - q) = p)
    (hK : HasResidueAt (rightC ckmrvEightKernel τ) p R) :
    HasResidueAt (rightC ckmrvEightHatKernel τ) q ((q - 1) ^ 2 * (1 - q) ^ 2 * R) := by
  have hq1 := one_sub_ne_zero_of_im_pos hq
  have h := HasResidueAt.comp (h := fun w : ℂ => (w - 1) ^ 2) (M := fun w : ℂ => w / (1 - w))
    (q := q) hK hMq (hasDerivAt_div_one_sub hq1)
    (by simpa using pow_ne_zero 2 hq1) (by fun_prop) (f := rightC ckmrvEightHatKernel τ)
    (by
      filter_upwards [eventually_im_pos_of_im_pos hq] with w hw
      exact rightC_hat_eq_STS hw)
  have e : (q - 1) ^ 2 * (1 / (1 - q) ^ 2)⁻¹ * R = (q - 1) ^ 2 * (1 - q) ^ 2 * R := by
    field_simp
  rwa [e] at h

theorem hasResidueAt_hat_of_TST (τ : ℍ) {q p R : ℂ} (hq : 0 < q.im) (hMq : q / (q + 1) = p)
    (hK : HasResidueAt (rightC ckmrvEightKernel τ) p R) :
    HasResidueAt (rightC ckmrvEightHatKernel τ) q ((q + 1) ^ 2 * (q + 1) ^ 2 * R) := by
  have hq1 := add_one_ne_zero_of_im_pos hq
  have h := HasResidueAt.comp (h := fun w : ℂ => (w + 1) ^ 2) (M := fun w : ℂ => w / (w + 1))
    (q := q) hK hMq (hasDerivAt_div_add_one hq1)
    (by simpa using pow_ne_zero 2 hq1) (by fun_prop) (f := rightC ckmrvEightHatKernel τ)
    (by
      filter_upwards [eventually_im_pos_of_im_pos hq] with w hw
      exact rightC_hat_eq_TST hw)
  have e : (q + 1) ^ 2 * (1 / (q + 1) ^ 2)⁻¹ * R = (q + 1) ^ 2 * (q + 1) ^ 2 * R := by
    field_simp
  rwa [e] at h

section SpecialPoints2

variable {τ₀ : ℍ} (hA : ModularForm.E₄ τ₀ ≠ 0) (hB : ModularForm.E₆ τ₀ ≠ 0)
include hA hB

omit hA hB in
theorem coe_S_smul_mul (w : ℍ) : ((ModularGroup.S • w : ℍ) : ℂ) * (w : ℂ) = -1 := by
  rw [coe_S_smul]; field_simp [ne_zero w]

/-- The pole of `𝒦̂(τ, ·)` on the line `Re z = 1`: residue `(Sτ)⁴/(2π)` at `Sτ + 1`. -/
theorem hasResidueAt_hatKernel_S_add_one :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) + 1)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 4 / (2 * (π : ℂ))) := by
  set σ : ℂ := ((ModularGroup.S • τ₀ : ℍ) : ℂ) with hσ
  have hσ0 : σ ≠ 0 := ne_zero _
  have hστ : σ * (τ₀ : ℂ) = -1 := coe_S_smul_mul τ₀
  have hq : 0 < (σ + 1).im := by simpa [hσ] using (ModularGroup.S • τ₀).im_pos
  have hM : (σ + 1) / (1 - (σ + 1)) = (τ₀ : ℂ) - 1 := by
    rw [div_eq_iff (by simpa using hσ0)]
    linear_combination hστ
  have h := hasResidueAt_hat_of_STS τ₀ hq hM (hasResidueAt_kernel_T hA hB)
  have e : (σ + 1 - 1) ^ 2 * (1 - (σ + 1)) ^ 2 * (1 / (2 * (π : ℂ))) = σ ^ 4 / (2 * (π : ℂ)) := by
    ring
  rwa [e] at h

/-- `𝒦̂(τ, ·)` is regular at `τ + 1`. -/
theorem hasResidueAt_hatKernel_add_one :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) ((τ₀ : ℂ) + 1) 0 := by
  have hτ0 : (τ₀ : ℂ) ≠ 0 := ne_zero τ₀
  have hστ : ((ModularGroup.S • τ₀ : ℍ) : ℂ) * (τ₀ : ℂ) = -1 := coe_S_smul_mul τ₀
  have hq : 0 < ((τ₀ : ℂ) + 1).im := by simpa using τ₀.im_pos
  have hM : ((τ₀ : ℂ) + 1) / (1 - ((τ₀ : ℂ) + 1)) = ((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1 := by
    rw [div_eq_iff (by simpa using hτ0)]
    linear_combination hστ
  have h := hasResidueAt_hat_of_STS τ₀ hq hM (hasResidueAt_kernel_ST hA hB)
  simpa using h

/-- `𝒦̂(τ, ·)` is regular at the point `τ/(1 + τ)` of the semicircle `|z − 1/2| = 1/2`. -/
theorem hasResidueAt_hatKernel_semicircle_self :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) ((τ₀ : ℂ) / (1 + τ₀)) 0 := by
  have hq : 0 < ((τ₀ : ℂ) / (1 + τ₀)).im := by
    rw [add_comm]; exact im_div_add_one_pos τ₀.im_pos
  have h1 : (1 : ℂ) + τ₀ ≠ 0 := by rw [add_comm]; exact add_one_ne_zero_of_im_pos τ₀.im_pos
  have hM : (τ₀ : ℂ) / (1 + τ₀) / (1 - (τ₀ : ℂ) / (1 + τ₀)) = τ₀ := by
    field_simp; ring
  have h := hasResidueAt_hat_of_STS τ₀ hq hM (hasResidueAt_kernel_self hA hB)
  simpa using h

/-- `𝒦̂(τ, ·)` is regular at the point `Sτ/(1 + Sτ)` of the semicircle `|z − 1/2| = 1/2`. -/
theorem hasResidueAt_hatKernel_semicircle_S :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) / (1 + ((ModularGroup.S • τ₀ : ℍ) : ℂ))) 0 := by
  set σ := ModularGroup.S • τ₀
  have hq : 0 < ((σ : ℂ) / (1 + σ)).im := by
    rw [add_comm]; exact im_div_add_one_pos σ.im_pos
  have h1 : (1 : ℂ) + σ ≠ 0 := by rw [add_comm]; exact add_one_ne_zero_of_im_pos σ.im_pos
  have hM : (σ : ℂ) / (1 + σ) / (1 - (σ : ℂ) / (1 + σ)) = σ := by
    field_simp; ring
  have h := hasResidueAt_hat_of_STS τ₀ hq hM (hasResidueAt_kernel_S hA hB)
  simpa using h

/-- `𝒦̂(τ, ·)` is regular at the point `τ/(1 − τ)` of the semicircle `|z + 1/2| = 1/2`. -/
theorem hasResidueAt_hatKernel_semicircle'_self :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀) ((τ₀ : ℂ) / (1 - τ₀)) 0 := by
  have hq : 0 < ((τ₀ : ℂ) / (1 - τ₀)).im := im_div_one_sub_pos τ₀.im_pos
  have h1 : (1 : ℂ) - τ₀ ≠ 0 := one_sub_ne_zero_of_im_pos τ₀.im_pos
  have hM : (τ₀ : ℂ) / (1 - τ₀) / ((τ₀ : ℂ) / (1 - τ₀) + 1) = τ₀ := by
    field_simp; ring
  have h := hasResidueAt_hat_of_TST τ₀ hq hM (hasResidueAt_kernel_self hA hB)
  simpa using h

/-- `𝒦̂(τ, ·)` is regular at the point `Sτ/(1 − Sτ)` of the semicircle `|z + 1/2| = 1/2`. -/
theorem hasResidueAt_hatKernel_semicircle'_S :
    HasResidueAt (rightC ckmrvEightHatKernel τ₀)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) / (1 - ((ModularGroup.S • τ₀ : ℍ) : ℂ))) 0 := by
  set σ := ModularGroup.S • τ₀
  have hq : 0 < ((σ : ℂ) / (1 - σ)).im := im_div_one_sub_pos σ.im_pos
  have h1 : (1 : ℂ) - σ ≠ 0 := one_sub_ne_zero_of_im_pos σ.im_pos
  have hM : (σ : ℂ) / (1 - σ) / ((σ : ℂ) / (1 - σ) + 1) = σ := by
    field_simp; ring
  have h := hasResidueAt_hat_of_TST τ₀ hq hM (hasResidueAt_kernel_S hA hB)
  simpa using h

end SpecialPoints2

end E8Leech
