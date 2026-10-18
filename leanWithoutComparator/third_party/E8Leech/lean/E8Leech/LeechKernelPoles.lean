import E8Leech.CKMRVKernelPoles

/-!
# Poles of the Leech CKMRV kernels in the right variable

The dimension-24 analogue of the kernel-specific half of `CKMRVKernelPoles`. The generic material
of that file is reused as it is: the residue transfer `tendsto_residue_transfer`, the transport
`HasResidueAt.comp`, `kleinJC`, `rightC`, and the reductions `hasResidueAt_T_of`,
`hasResidueAt_ST_of`, `hasResidueAt_zero_at_S` at the points `τ − 1`, `Sτ − 1`, `Sτ`.

Known answer first: `K⁽²⁴⁾(τ, z) = N(τ, z) / (j(τ) − j(z))` with `N` holomorphic in each variable
(`leechMinusSingNum / Δ(z)²` for `K₋`, `ckmrvLeechPlusNormalizedNumerator` for `K₊`). At a simple
zero of the denominator the residues in `τ` and in `z` are both `N / j'` up to sign. So the
published left residues `Res_{τ=z} K|₁₂T = −1/(2π)` (CKMRV Theorem 4.3(3), `CKMRVKernelResidues`)
give the right residues `Res_{z=τ−1} K(τ, ·) = 1/(2π)` and
`Res_{z=Sτ−1} K(τ, ·) = ε (Sτ)¹² / (2π)`, where `ε` is the left `S`-eigenvalue at weight `12`
(`+1` for `K₋`, `−1` for `K₊`). The points `τ` and `Sτ` are removable (`CKMRVLaplaceAxis`,
`CKMRVLaplaceAxisMinus`). Hence `𝒦 = (K₊ + K₋)/2` has the residues `1/(2π)` at `τ − 1` and `0` at
`Sτ − 1`, and `𝒦̂ = (K₊ − K₋)/2` has `0` at `τ − 1` and `−(Sτ)¹²/(2π)` at `Sτ − 1`.

The right relation `I ∓ STS` at weight `−10` (`CKMRVRightRelations`) exchanges `𝒦` and `𝒦̂`:
`𝒦̂(τ, w) = (w − 1)¹⁰ 𝒦(τ, w / (1 − w))`. Through this Möbius change of variable the residues of
`𝒦` at `τ`, `Sτ`, `τ − 1`, `Sτ − 1` give those of `𝒦̂` at `Sτ + 1` (a pole, residue
`(Sτ)¹²/(2π)`), at `τ + 1` and at the points `τ/(1 ± τ)`, `Sτ/(1 ± Sτ)` of the two semicircles
(all regular).

Compared with dimension eight only two exponents change: `4 → 12` (left weight) and `2 → 10`
(right weight). All signs, and the values `1/(2π)` at `T`, are the same.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The numerator of `K₋⁽²⁴⁾` in the left variable -/

/-- The numerator `N(τ, z)` of `K₋⁽²⁴⁾` is holomorphic in the left variable: it depends on `τ`
through `Δ(τ)`, `j(τ)` and the three row constants `α`, `β`, `γ` only. -/
theorem mdifferentiable_leechMinusSingNum_left (z : ℍ) :
    MDiff (fun τ : ℍ => leechMinusSingNum τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  have hJ := mdifferentiable_kleinModularJ
  have hα : MDiff (fun τ : ℍ => leechMinusAlpha τ) :=
    ((mdifferentiable_ckmrvPsiBasis 1).mul (h4.mul h6)).sub
      ((mdifferentiable_ckmrvPsiBasis 2).mul (h4.pow 2))
  have hβ : MDiff (fun τ : ℍ => leechMinusBeta τ) :=
    (mdifferentiable_const.mul hα).sub (mdifferentiable_const.mul hΔ)
  have hγ : MDiff (fun τ : ℍ => leechMinusGamma τ) :=
    (hJ.mul hα).add (mdifferentiable_const.mul ((mdifferentiable_ckmrvPsiBasis 2).mul (h4.pow 2)))
  have hD : MDiff (fun τ : ℍ => eightMinusDenZ τ z) :=
    (mdifferentiable_const.mul hJ).sub mdifferentiable_const
  have hNEll : MDiff (fun τ : ℍ => leechMinusNEll τ z) :=
    (mdifferentiable_const.mul hΔ).mul mdifferentiable_const
  have hNZero : MDiff (fun τ : ℍ => leechMinusNZero τ z) :=
    ((((mdifferentiable_const.mul hΔ).mul mdifferentiable_const).add
      ((mdifferentiable_const.mul hD).mul hβ)).add (mdifferentiable_const.mul hγ)).sub
        (hα.mul mdifferentiable_const)
  exact (mdifferentiable_const.mul hNEll).add hNZero

/-! ## Right residues of `K₋⁽²⁴⁾` at `T` and `ST` -/

/-- The numerator of `K₋⁽²⁴⁾` on `ℂ × ℂ`. -/
def leechMinusNumC (τ z : ℂ) : ℂ :=
  ckmrvMinusScale⁻¹ * (leechMinusSingNum (ofComplex τ) (ofComplex z) /
    ModularForm.discriminant (ofComplex z) ^ 2)

theorem ckmrvLeechMinusKernel_eq_numC (τ z : ℂ) :
    ckmrvLeechMinusKernel (ofComplex τ) (ofComplex z) =
      leechMinusNumC τ z / (kleinJC τ - kleinJC z) := by
  rw [ckmrvLeechMinusKernel_eq_sing, leechMinusNumC, kleinJC, kleinJC]
  ring

theorem continuousAt_leechMinusNumC_left (a b : ℍ) :
    ContinuousAt (fun τ => leechMinusNumC τ b) (a : ℂ) := by
  unfold leechMinusNumC
  have h := continuousAt_comp_ofComplex (mdifferentiable_leechMinusSingNum_left (ofComplex b)) a
  exact continuousAt_const.mul (h.div_const _)

theorem continuousAt_leechMinusNumC_right (a b : ℍ) :
    ContinuousAt (leechMinusNumC a) (b : ℂ) := by
  unfold leechMinusNumC
  have h1 := continuousAt_comp_ofComplex (mdifferentiable_leechMinusSingNum (ofComplex a)) b
  have h2 := continuousAt_comp_ofComplex mdifferentiable_modularDiscriminant b
  exact continuousAt_const.mul (h1.div (h2.pow 2)
    (pow_ne_zero 2 (ModularForm.discriminant_ne_zero _)))

/-- `Res_{z=b} K₋⁽²⁴⁾(Tb, z) = 1/(2π)`: the right residue at `T`, from the left residue
`Res_{τ=z} K₋|₁₂T = −1/(2π)`. -/
theorem tendsto_ckmrvLeechMinusKernel_right_residue_T (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) * ckmrvLeechMinusKernel (ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (1 / (2 * (π : ℂ)))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have ha : ((ModularGroup.T • b : ℍ) : ℂ) = (b : ℂ) + 1 := coe_T_smul b
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvLeechMinusKernel (ofComplex (w + 1)) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
    refine (tendsto_ckmrvLeechMinusKernel_residue_T b hA hB).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_add_one hw, UpperHalfPlane.ofComplex_apply]
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvLeechMinusKernel (ofComplex τ)
      (ofComplex z)) (N := leechMinusNumC) (J := kleinJC) (M := fun w => w + 1)
    (a := (b : ℂ) + 1) (b := b) (d := kleinModularJDerivative b) rfl (by fun_prop)
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_add_one hw) (hasDerivAt_kleinJC b) hd
    (Eventually.of_forall fun w => ckmrvLeechMinusKernel_eq_numC _ _)
    (Eventually.of_forall fun z => ckmrvLeechMinusKernel_eq_numC _ _)
    (by rw [← ha]; exact continuousAt_leechMinusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_leechMinusNumC_right _ b) hres
  have e : -(-1 / (2 * (π : ℂ))) = 1 / (2 * (π : ℂ)) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

/-- `Res_{z=b} K₋⁽²⁴⁾(STb, z) = (b + 1)¹² / (2π)`: the right residue at `ST`, from the left
`S`-eigenvalue `+1` at weight `12`. -/
theorem tendsto_ckmrvLeechMinusKernel_right_residue_ST (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) *
      ckmrvLeechMinusKernel (ModularGroup.S • ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (((b : ℂ) + 1) ^ 12 / (2 * (π : ℂ)))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have hb1 : (b : ℂ) + 1 ≠ 0 := add_one_ne_zero_of_im_pos b.im_pos
  have ha : ((ModularGroup.S • ModularGroup.T • b : ℍ) : ℂ) = -1 / ((b : ℂ) + 1) := by
    rw [coe_S_smul, coe_T_smul]
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvLeechMinusKernel (ofComplex (-1 / (w + 1))) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (((b : ℂ) + 1) ^ 12 * (-1 / (2 * (π : ℂ))))) := by
    have hT := tendsto_ckmrvLeechMinusKernel_residue_T b hA hB
    have hpow : Tendsto (fun w : ℂ => (w + 1) ^ 12) (𝓝[≠] (b : ℂ)) (𝓝 (((b : ℂ) + 1) ^ 12)) :=
      ((continuous_id.add continuous_const).pow 12).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    refine (hpow.mul hT).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_ST hw, ckmrvLeechMinusKernel_S,
      UpperHalfPlane.ofComplex_apply, coe_T_smul, ofComplex_apply_of_im_pos hw]
    ring
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvLeechMinusKernel (ofComplex τ)
      (ofComplex z)) (N := leechMinusNumC) (J := kleinJC) (M := fun w => -1 / (w + 1))
    (a := -1 / ((b : ℂ) + 1)) (b := b) (d := kleinModularJDerivative b) rfl
    ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hb1))
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_ST hw) (hasDerivAt_kleinJC b) hd
    (Eventually.of_forall fun w => ckmrvLeechMinusKernel_eq_numC _ _)
    (Eventually.of_forall fun z => ckmrvLeechMinusKernel_eq_numC _ _)
    (by rw [← ha]; exact continuousAt_leechMinusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_leechMinusNumC_right _ b) hres
  have e : -(((b : ℂ) + 1) ^ 12 * (-1 / (2 * (π : ℂ)))) =
      ((b : ℂ) + 1) ^ 12 / (2 * (π : ℂ)) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

/-! ## Right residues of `K₊⁽²⁴⁾` at `T` and `ST` -/

/-- The normalized numerator of `K₊⁽²⁴⁾` on `ℂ × ℂ`. -/
def leechPlusNumC (τ z : ℂ) : ℂ := ckmrvLeechPlusNormalizedNumerator (ofComplex τ) (ofComplex z)

theorem ckmrvLeechPlusKernel_eq_numC {τ z : ℂ} (h : kleinJC τ ≠ kleinJC z) :
    ckmrvLeechPlusKernel (ofComplex τ) (ofComplex z) =
      leechPlusNumC τ z / (kleinJC τ - kleinJC z) :=
  ckmrvLeechPlusKernel_quotient _ _ (sub_ne_zero.mpr h)

theorem continuousAt_leechPlusNumC_left (a b : ℍ) :
    ContinuousAt (fun τ => leechPlusNumC τ b) (a : ℂ) := by
  have h := mdifferentiable_ckmrvLeechPlusNormalizedNumerator.comp
    (mdifferentiable_id.prodMk (mdifferentiable_const (c := ofComplex (b : ℂ))))
  exact continuousAt_comp_ofComplex h a

theorem continuousAt_leechPlusNumC_right (a b : ℍ) :
    ContinuousAt (leechPlusNumC a) (b : ℂ) := by
  have h := mdifferentiable_ckmrvLeechPlusNormalizedNumerator.comp
    ((mdifferentiable_const (c := ofComplex (a : ℂ))).prodMk mdifferentiable_id)
  exact continuousAt_comp_ofComplex h b

/-- `Res_{z=b} K₊⁽²⁴⁾(Tb, z) = 1/(2π)`: the right residue at `T`, from the left residue
`Res_{τ=z} K₊|₁₂T = −1/(2π)`. -/
theorem tendsto_ckmrvLeechPlusKernel_right_residue_T (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) * ckmrvLeechPlusKernel (ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (1 / (2 * (π : ℂ)))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have ha : ((ModularGroup.T • b : ℍ) : ℂ) = (b : ℂ) + 1 := coe_T_smul b
  have hJa : kleinJC ((b : ℂ) + 1) = kleinJC b := kleinJC_add_one b.im_pos
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvLeechPlusKernel (ofComplex (w + 1)) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (-1 / (2 * (π : ℂ)))) := by
    refine (tendsto_ckmrvLeechPlusKernel_residue_T b hA hB).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_add_one hw, UpperHalfPlane.ofComplex_apply]
  have hev := eventually_kleinJC_ne b hd
  have hpos := (eventually_im_pos_nhds b).filter_mono (nhdsWithin_le_nhds (s := {(b : ℂ)}ᶜ))
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvLeechPlusKernel (ofComplex τ)
      (ofComplex z)) (N := leechPlusNumC) (J := kleinJC) (M := fun w => w + 1)
    (a := (b : ℂ) + 1) (b := b) (d := kleinModularJDerivative b) rfl (by fun_prop)
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_add_one hw) (hasDerivAt_kleinJC b) hd
    (by
      filter_upwards [hev, hpos] with w hw hw'
      exact ckmrvLeechPlusKernel_eq_numC (by rw [kleinJC_add_one hw']; exact hw))
    (by
      filter_upwards [hev] with z hz
      exact ckmrvLeechPlusKernel_eq_numC (by rw [hJa]; exact hz.symm))
    (by rw [← ha]; exact continuousAt_leechPlusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_leechPlusNumC_right _ b) hres
  have e : -(-1 / (2 * (π : ℂ))) = 1 / (2 * (π : ℂ)) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

/-- `Res_{z=b} K₊⁽²⁴⁾(STb, z) = −(b + 1)¹² / (2π)`: the right residue at `ST`, from the left
`S`-eigenvalue `−1` at weight `12`. -/
theorem tendsto_ckmrvLeechPlusKernel_right_residue_ST (b : ℍ)
    (hA : ModularForm.E₄ b ≠ 0) (hB : ModularForm.E₆ b ≠ 0) :
    Tendsto (fun z : ℂ => (z - b) *
      ckmrvLeechPlusKernel (ModularGroup.S • ModularGroup.T • b) (ofComplex z))
      (𝓝[≠] (b : ℂ)) (𝓝 (-(((b : ℂ) + 1) ^ 12 / (2 * (π : ℂ))))) := by
  have hd := (kleinModularJDerivative_ne_zero_iff b).mpr ⟨hA, hB⟩
  have hb1 : (b : ℂ) + 1 ≠ 0 := add_one_ne_zero_of_im_pos b.im_pos
  have ha : ((ModularGroup.S • ModularGroup.T • b : ℍ) : ℂ) = -1 / ((b : ℂ) + 1) := by
    rw [coe_S_smul, coe_T_smul]
  have hJa : kleinJC (-1 / ((b : ℂ) + 1)) = kleinJC b := kleinJC_ST b.im_pos
  have hres : Tendsto (fun w : ℂ => (w - b) *
      ckmrvLeechPlusKernel (ofComplex (-1 / (w + 1))) (ofComplex (b : ℂ)))
      (𝓝[≠] (b : ℂ)) (𝓝 (-((b : ℂ) + 1) ^ 12 * (-1 / (2 * (π : ℂ))))) := by
    have hT := tendsto_ckmrvLeechPlusKernel_residue_T b hA hB
    have hpow : Tendsto (fun w : ℂ => -(w + 1) ^ 12) (𝓝[≠] (b : ℂ))
        (𝓝 (-((b : ℂ) + 1) ^ 12)) :=
      (((continuous_id.add continuous_const).pow 12).neg).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    refine (hpow.mul hT).congr' ?_
    filter_upwards [(eventually_im_pos_nhds b).filter_mono nhdsWithin_le_nhds] with w hw
    rw [ckmrv_slash_T_apply_smul, ofComplex_ST hw, ckmrvLeechPlusKernel_S,
      UpperHalfPlane.ofComplex_apply, coe_T_smul, ofComplex_apply_of_im_pos hw]
    ring
  have hev := eventually_kleinJC_ne b hd
  have hpos := (eventually_im_pos_nhds b).filter_mono (nhdsWithin_le_nhds (s := {(b : ℂ)}ᶜ))
  have h := tendsto_residue_transfer (K := fun τ z => ckmrvLeechPlusKernel (ofComplex τ)
      (ofComplex z)) (N := leechPlusNumC) (J := kleinJC) (M := fun w => -1 / (w + 1))
    (a := -1 / ((b : ℂ) + 1)) (b := b) (d := kleinModularJDerivative b) rfl
    ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hb1))
    ((eventually_im_pos_nhds b).mono fun w hw => kleinJC_ST hw) (hasDerivAt_kleinJC b) hd
    (by
      filter_upwards [hev, hpos] with w hw hw'
      exact ckmrvLeechPlusKernel_eq_numC (by rw [kleinJC_ST hw']; exact hw))
    (by
      filter_upwards [hev] with z hz
      exact ckmrvLeechPlusKernel_eq_numC (by rw [hJa]; exact hz.symm))
    (by rw [← ha]; exact continuousAt_leechPlusNumC_left _ b)
    (by rw [← ha]; exact continuousAt_leechPlusNumC_right _ b) hres
  have e : -(-((b : ℂ) + 1) ^ 12 * (-1 / (2 * (π : ℂ)))) =
      -(((b : ℂ) + 1) ^ 12 / (2 * (π : ℂ))) := by ring
  rw [e] at h
  refine h.congr fun z => ?_
  rw [← ha, UpperHalfPlane.ofComplex_apply]

/-! ## The two kernels and their combinations at the special points -/

/-- Removability at `Sτ` from the existing limit of `K(τ, S·) zⁿ` at `τ`, for any exponent `n`:
a reduction to `hasResidueAt_zero_at_S` (the case `n = 2`), since `zⁿ` and `z²` differ by a
factor that is continuous and nonzero at `τ`. -/
theorem hasResidueAt_zero_at_S_of_pow {K : ℍ → ℍ → ℂ} (τ₀ : ℍ) (n : ℕ)
    (hlim : ∃ L : ℂ, Tendsto (fun w : ℂ => K τ₀ (ModularGroup.S • ofComplex w) *
      ((ofComplex w : ℍ) : ℂ) ^ n) (𝓝[≠] (τ₀ : ℂ)) (𝓝 L)) :
    HasResidueAt (fun z => K τ₀ (ofComplex z)) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 := by
  obtain ⟨L, hL⟩ := hlim
  have hF : Continuous fun z : ℍ => (z : ℂ) ^ 2 / (z : ℂ) ^ n :=
    (UpperHalfPlane.continuous_coe.pow 2).div (UpperHalfPlane.continuous_coe.pow n)
      fun z => pow_ne_zero n (ne_zero z)
  refine hasResidueAt_zero_at_S τ₀ ⟨_, (hL.mul (tendsto_comp_ofComplex_punctured hF τ₀)).congr'
    (Eventually.of_forall fun w => ?_)⟩
  have hw : ((ofComplex w : ℍ) : ℂ) ≠ 0 := ne_zero _
  field_simp

theorem rightC_leechKernel (τ : ℍ) (z : ℂ) : rightC ckmrvLeechKernel τ z =
    (rightC ckmrvLeechPlusKernel τ z + rightC ckmrvLeechMinusKernel τ z) / 2 := rfl

theorem rightC_leechHatKernel (τ : ℍ) (z : ℂ) : rightC ckmrvLeechHatKernel τ z =
    (rightC ckmrvLeechPlusKernel τ z - rightC ckmrvLeechMinusKernel τ z) / 2 := rfl

section SpecialPoints

variable {τ₀ : ℍ} (hA : ModularForm.E₄ τ₀ ≠ 0) (hB : ModularForm.E₆ τ₀ ≠ 0)
include hA hB

theorem hasResidueAt_leechPlus_self : HasResidueAt (rightC ckmrvLeechPlusKernel τ₀) τ₀ 0 := by
  obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechPlusKernel_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩)
  exact HasResidueAt.of_tendsto hL

theorem hasResidueAt_leechMinus_self : HasResidueAt (rightC ckmrvLeechMinusKernel τ₀) τ₀ 0 := by
  obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechMinusKernel_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩)
  exact HasResidueAt.of_tendsto hL

theorem hasResidueAt_leechPlus_S :
    HasResidueAt (rightC ckmrvLeechPlusKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_zero_at_S_of_pow τ₀ 10 (exists_tendsto_ckmrvLeechPlusKernel_S_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩))

theorem hasResidueAt_leechMinus_S :
    HasResidueAt (rightC ckmrvLeechMinusKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_zero_at_S_of_pow τ₀ 10 (exists_tendsto_ckmrvLeechMinusKernel_S_right τ₀
    ((kleinModularJDerivative_ne_zero_iff τ₀).mpr ⟨hA, hB⟩))

theorem hasResidueAt_leechPlus_T :
    HasResidueAt (rightC ckmrvLeechPlusKernel τ₀) ((τ₀ : ℂ) - 1) (1 / (2 * (π : ℂ))) :=
  hasResidueAt_T_of hA hB tendsto_ckmrvLeechPlusKernel_right_residue_T

theorem hasResidueAt_leechMinus_T :
    HasResidueAt (rightC ckmrvLeechMinusKernel τ₀) ((τ₀ : ℂ) - 1) (1 / (2 * (π : ℂ))) :=
  hasResidueAt_T_of hA hB tendsto_ckmrvLeechMinusKernel_right_residue_T

theorem hasResidueAt_leechPlus_ST :
    HasResidueAt (rightC ckmrvLeechPlusKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (-(((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 12 / (2 * (π : ℂ)))) :=
  hasResidueAt_ST_of hA hB (R := fun x => -(x ^ 12 / (2 * (π : ℂ))))
    tendsto_ckmrvLeechPlusKernel_right_residue_ST

theorem hasResidueAt_leechMinus_ST :
    HasResidueAt (rightC ckmrvLeechMinusKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 12 / (2 * (π : ℂ))) :=
  hasResidueAt_ST_of hA hB (R := fun x => x ^ 12 / (2 * (π : ℂ)))
    tendsto_ckmrvLeechMinusKernel_right_residue_ST

/-! The combined kernels `𝒦 = (K₊ + K₋)/2` and `𝒦̂ = (K₊ − K₋)/2`. -/

omit hA hB in
theorem hasResidueAt_leechKernel_of {p R S T : ℂ}
    (hp : HasResidueAt (rightC ckmrvLeechPlusKernel τ₀) p R)
    (hm : HasResidueAt (rightC ckmrvLeechMinusKernel τ₀) p S) (hT : (R + S) / 2 = T) :
    HasResidueAt (rightC ckmrvLeechKernel τ₀) p T := by
  have h := (hp.add hm).div_const 2
  rw [hT] at h
  exact h

omit hA hB in
theorem hasResidueAt_leechHatKernel_of {p R S T : ℂ}
    (hp : HasResidueAt (rightC ckmrvLeechPlusKernel τ₀) p R)
    (hm : HasResidueAt (rightC ckmrvLeechMinusKernel τ₀) p S) (hT : (R - S) / 2 = T) :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) p T := by
  have h := (hp.sub hm).div_const 2
  rw [hT] at h
  exact h

/-- `𝒦⁽²⁴⁾(τ, ·)` is regular at `τ`. -/
theorem hasResidueAt_leechKernel_self : HasResidueAt (rightC ckmrvLeechKernel τ₀) τ₀ 0 :=
  hasResidueAt_leechKernel_of (hasResidueAt_leechPlus_self hA hB)
    (hasResidueAt_leechMinus_self hA hB) (by ring)

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at `τ`. -/
theorem hasResidueAt_leechHatKernel_self : HasResidueAt (rightC ckmrvLeechHatKernel τ₀) τ₀ 0 :=
  hasResidueAt_leechHatKernel_of (hasResidueAt_leechPlus_self hA hB)
    (hasResidueAt_leechMinus_self hA hB) (by ring)

/-- `𝒦⁽²⁴⁾(τ, ·)` is regular at `Sτ`. -/
theorem hasResidueAt_leechKernel_S :
    HasResidueAt (rightC ckmrvLeechKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_leechKernel_of (hasResidueAt_leechPlus_S hA hB) (hasResidueAt_leechMinus_S hA hB)
    (by ring)

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at `Sτ`. -/
theorem hasResidueAt_leechHatKernel_S :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) ((ModularGroup.S • τ₀ : ℍ) : ℂ) 0 :=
  hasResidueAt_leechHatKernel_of (hasResidueAt_leechPlus_S hA hB)
    (hasResidueAt_leechMinus_S hA hB) (by ring)

/-- The pole of `𝒦⁽²⁴⁾(τ, ·)` at `τ − 1`: residue `1/(2π)`. -/
theorem hasResidueAt_leechKernel_T :
    HasResidueAt (rightC ckmrvLeechKernel τ₀) ((τ₀ : ℂ) - 1) (1 / (2 * (π : ℂ))) :=
  hasResidueAt_leechKernel_of (hasResidueAt_leechPlus_T hA hB) (hasResidueAt_leechMinus_T hA hB)
    (by ring)

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at `τ − 1`. -/
theorem hasResidueAt_leechHatKernel_T :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) ((τ₀ : ℂ) - 1) 0 :=
  hasResidueAt_leechHatKernel_of (hasResidueAt_leechPlus_T hA hB)
    (hasResidueAt_leechMinus_T hA hB) (by ring)

/-- `𝒦⁽²⁴⁾(τ, ·)` is regular at `Sτ − 1`. -/
theorem hasResidueAt_leechKernel_ST :
    HasResidueAt (rightC ckmrvLeechKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1) 0 :=
  hasResidueAt_leechKernel_of (hasResidueAt_leechPlus_ST hA hB)
    (hasResidueAt_leechMinus_ST hA hB) (by ring)

/-- The pole of `𝒦̂⁽²⁴⁾(τ, ·)` at `Sτ − 1`: residue `−(Sτ)¹²/(2π)`. -/
theorem hasResidueAt_leechHatKernel_ST :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1)
      (-(((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 12 / (2 * (π : ℂ)))) :=
  hasResidueAt_leechHatKernel_of (hasResidueAt_leechPlus_ST hA hB)
    (hasResidueAt_leechMinus_ST hA hB) (by ring)

end SpecialPoints

/-! ## The `STS` relation in pointwise form (weight `−10`) -/

theorem slash_STS_apply_ten (f : ℍ → ℂ) (w : ℍ) :
    (f ∣[(-10 : ℤ)] (ModularGroup.S * ModularGroup.T * ModularGroup.S)) w =
      f (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) * ((w : ℂ) - 1) ^ 10 := by
  have hw := ne_zero w
  have e : (-1 / (w : ℂ) + 1) * w = w - 1 := by field_simp; ring
  rw [slash_STS, ckmrv_slash_S_apply, ckmrv_slash_T_apply_smul, ckmrv_slash_S_apply, coe_T_smul,
    coe_S_smul]
  simp only [neg_neg, zpow_ofNat]
  rw [mul_assoc, ← mul_pow, e]

theorem ckmrvLeechPlusKernel_STS (τ w : ℍ) :
    ckmrvLeechPlusKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) *
      ((w : ℂ) - 1) ^ 10 = ckmrvLeechPlusKernel τ w := by
  have h := congrFun (ckmrvLeechPlusKernel_right_rel_two τ) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [slash_STS_apply_ten] at h
  linear_combination -h

theorem ckmrvLeechMinusKernel_STS (τ w : ℍ) :
    ckmrvLeechMinusKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) *
      ((w : ℂ) - 1) ^ 10 = -ckmrvLeechMinusKernel τ w := by
  have h := congrFun (ckmrvLeechMinusKernel_right_rel_two τ) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, one_mul] at h
  rw [slash_STS_apply_ten] at h
  linear_combination h

/-- `𝒦̂⁽²⁴⁾ = 𝒦⁽²⁴⁾ |_{−10} STS`. -/
theorem ckmrvLeechHatKernel_eq_STS (τ w : ℍ) : ckmrvLeechHatKernel τ w =
    ((w : ℂ) - 1) ^ 10 *
      ckmrvLeechKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) := by
  have h1 := ckmrvLeechPlusKernel_STS τ w
  have h2 := ckmrvLeechMinusKernel_STS τ w
  simp only [ckmrvLeechHatKernel, ckmrvLeechKernel]
  linear_combination (-h1 - h2) / 2

/-- `𝒦⁽²⁴⁾ = 𝒦̂⁽²⁴⁾ |_{−10} STS`. -/
theorem ckmrvLeechKernel_eq_STS (τ w : ℍ) : ckmrvLeechKernel τ w =
    ((w : ℂ) - 1) ^ 10 *
      ckmrvLeechHatKernel τ (ModularGroup.S • ModularGroup.T • ModularGroup.S • w) := by
  have h1 := ckmrvLeechPlusKernel_STS τ w
  have h2 := ckmrvLeechMinusKernel_STS τ w
  simp only [ckmrvLeechHatKernel, ckmrvLeechKernel]
  linear_combination (-h1 + h2) / 2

/-- From the `STS` form to the `TST` form at weight `−10`: if `F(w) = (w − 1)¹⁰ G(STS w)` on `ℍ`,
then `G(u) = (u + 1)¹⁰ F(u / (u + 1))` on `ℂ`. -/
theorem eq_TST_of_eq_STS_ten {F G : ℍ → ℂ}
    (h : ∀ w : ℍ, F w = ((w : ℂ) - 1) ^ 10 *
      G (ModularGroup.S • ModularGroup.T • ModularGroup.S • w)) {u : ℂ} (hu : 0 < u.im) :
    G (ofComplex u) = (u + 1) ^ 10 * F (ofComplex (u / (u + 1))) := by
  have hw := im_div_add_one_pos hu
  have hu1 := add_one_ne_zero_of_im_pos hu
  have e : u / (u + 1) / (1 - u / (u + 1)) = u := by field_simp; ring
  have e2 : (u + 1) * (u / (u + 1) - 1) = -1 := by field_simp; ring
  rw [h, STS_smul_ofComplex hw, e, ofComplex_apply_of_im_pos hw, ← mul_assoc, ← mul_pow, e2]
  norm_num

/-- `𝒦̂(w) = (w − 1)¹⁰ 𝒦(w / (1 − w))` on `ℂ`. -/
theorem rightC_leechHat_eq_STS {τ : ℍ} {w : ℂ} (hw : 0 < w.im) :
    rightC ckmrvLeechHatKernel τ w =
      (w - 1) ^ 10 * rightC ckmrvLeechKernel τ (w / (1 - w)) := by
  simp only [rightC]
  rw [ckmrvLeechHatKernel_eq_STS, STS_smul_ofComplex hw, ofComplex_apply_of_im_pos hw]

/-- `𝒦̂(u) = (u + 1)¹⁰ 𝒦(u / (u + 1))` on `ℂ` (the `TST` form). -/
theorem rightC_leechHat_eq_TST {τ : ℍ} {u : ℂ} (hu : 0 < u.im) :
    rightC ckmrvLeechHatKernel τ u =
      (u + 1) ^ 10 * rightC ckmrvLeechKernel τ (u / (u + 1)) :=
  eq_TST_of_eq_STS_ten (F := ckmrvLeechKernel τ) (G := ckmrvLeechHatKernel τ)
    (ckmrvLeechKernel_eq_STS τ) hu

/-- `𝒦(w) = (w − 1)¹⁰ 𝒦̂(w / (1 − w))` on `ℂ`. -/
theorem rightC_leech_eq_STS {τ : ℍ} {w : ℂ} (hw : 0 < w.im) :
    rightC ckmrvLeechKernel τ w =
      (w - 1) ^ 10 * rightC ckmrvLeechHatKernel τ (w / (1 - w)) := by
  simp only [rightC]
  rw [ckmrvLeechKernel_eq_STS, STS_smul_ofComplex hw, ofComplex_apply_of_im_pos hw]

/-- `𝒦(u) = (u + 1)¹⁰ 𝒦̂(u / (u + 1))` on `ℂ` (the `TST` form). -/
theorem rightC_leech_eq_TST {τ : ℍ} {u : ℂ} (hu : 0 < u.im) :
    rightC ckmrvLeechKernel τ u =
      (u + 1) ^ 10 * rightC ckmrvLeechHatKernel τ (u / (u + 1)) :=
  eq_TST_of_eq_STS_ten (F := ckmrvLeechHatKernel τ) (G := ckmrvLeechKernel τ)
    (ckmrvLeechHatKernel_eq_STS τ) hu

/-! ## Transported residues -/

/-- A residue `R` of `𝒦⁽²⁴⁾(τ, ·)` at `p = q / (1 − q)` gives the residue
`(q − 1)¹⁰ (1 − q)² R` of `𝒦̂⁽²⁴⁾(τ, ·)` at `q`. -/
theorem hasResidueAt_leechHat_of_STS (τ : ℍ) {q p R : ℂ} (hq : 0 < q.im)
    (hMq : q / (1 - q) = p) (hK : HasResidueAt (rightC ckmrvLeechKernel τ) p R) :
    HasResidueAt (rightC ckmrvLeechHatKernel τ) q ((q - 1) ^ 10 * (1 - q) ^ 2 * R) := by
  have hq1 := one_sub_ne_zero_of_im_pos hq
  have h := HasResidueAt.comp (h := fun w : ℂ => (w - 1) ^ 10) (M := fun w : ℂ => w / (1 - w))
    (q := q) hK hMq (hasDerivAt_div_one_sub hq1)
    (by simpa using pow_ne_zero 2 hq1) (by fun_prop) (f := rightC ckmrvLeechHatKernel τ)
    (by
      filter_upwards [eventually_im_pos_of_im_pos hq] with w hw
      exact rightC_leechHat_eq_STS hw)
  have e : (q - 1) ^ 10 * (1 / (1 - q) ^ 2)⁻¹ * R = (q - 1) ^ 10 * (1 - q) ^ 2 * R := by
    rw [one_div, inv_inv]
  rwa [e] at h

/-- A residue `R` of `𝒦⁽²⁴⁾(τ, ·)` at `p = q / (q + 1)` gives the residue
`(q + 1)¹⁰ (q + 1)² R` of `𝒦̂⁽²⁴⁾(τ, ·)` at `q`. -/
theorem hasResidueAt_leechHat_of_TST (τ : ℍ) {q p R : ℂ} (hq : 0 < q.im)
    (hMq : q / (q + 1) = p) (hK : HasResidueAt (rightC ckmrvLeechKernel τ) p R) :
    HasResidueAt (rightC ckmrvLeechHatKernel τ) q ((q + 1) ^ 10 * (q + 1) ^ 2 * R) := by
  have hq1 := add_one_ne_zero_of_im_pos hq
  have h := HasResidueAt.comp (h := fun w : ℂ => (w + 1) ^ 10) (M := fun w : ℂ => w / (w + 1))
    (q := q) hK hMq (hasDerivAt_div_add_one hq1)
    (by simpa using pow_ne_zero 2 hq1) (by fun_prop) (f := rightC ckmrvLeechHatKernel τ)
    (by
      filter_upwards [eventually_im_pos_of_im_pos hq] with w hw
      exact rightC_leechHat_eq_TST hw)
  have e : (q + 1) ^ 10 * (1 / (q + 1) ^ 2)⁻¹ * R = (q + 1) ^ 10 * (q + 1) ^ 2 * R := by
    rw [one_div, inv_inv]
  rwa [e] at h

section SpecialPoints2

variable {τ₀ : ℍ} (hA : ModularForm.E₄ τ₀ ≠ 0) (hB : ModularForm.E₆ τ₀ ≠ 0)
include hA hB

/-- The pole of `𝒦̂⁽²⁴⁾(τ, ·)` on the line `Re z = 1`: residue `(Sτ)¹²/(2π)` at `Sτ + 1`. -/
theorem hasResidueAt_leechHatKernel_S_add_one :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) (((ModularGroup.S • τ₀ : ℍ) : ℂ) + 1)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) ^ 12 / (2 * (π : ℂ))) := by
  set σ : ℂ := ((ModularGroup.S • τ₀ : ℍ) : ℂ) with hσ
  have hσ0 : σ ≠ 0 := ne_zero _
  have hστ : σ * (τ₀ : ℂ) = -1 := coe_S_smul_mul τ₀
  have hq : 0 < (σ + 1).im := by simpa [hσ] using (ModularGroup.S • τ₀).im_pos
  have hM : (σ + 1) / (1 - (σ + 1)) = (τ₀ : ℂ) - 1 := by
    rw [div_eq_iff (by simpa using hσ0)]
    linear_combination hστ
  have h := hasResidueAt_leechHat_of_STS τ₀ hq hM (hasResidueAt_leechKernel_T hA hB)
  have e : (σ + 1 - 1) ^ 10 * (1 - (σ + 1)) ^ 2 * (1 / (2 * (π : ℂ))) =
      σ ^ 12 / (2 * (π : ℂ)) := by
    ring
  rwa [e] at h

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at `τ + 1`. -/
theorem hasResidueAt_leechHatKernel_add_one :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) ((τ₀ : ℂ) + 1) 0 := by
  have hτ0 : (τ₀ : ℂ) ≠ 0 := ne_zero τ₀
  have hστ : ((ModularGroup.S • τ₀ : ℍ) : ℂ) * (τ₀ : ℂ) = -1 := coe_S_smul_mul τ₀
  have hq : 0 < ((τ₀ : ℂ) + 1).im := by simpa using τ₀.im_pos
  have hM : ((τ₀ : ℂ) + 1) / (1 - ((τ₀ : ℂ) + 1)) = ((ModularGroup.S • τ₀ : ℍ) : ℂ) - 1 := by
    rw [div_eq_iff (by simpa using hτ0)]
    linear_combination hστ
  have h := hasResidueAt_leechHat_of_STS τ₀ hq hM (hasResidueAt_leechKernel_ST hA hB)
  simpa using h

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at the point `τ/(1 + τ)` of the semicircle `|z − 1/2| = 1/2`. -/
theorem hasResidueAt_leechHatKernel_semicircle_self :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) ((τ₀ : ℂ) / (1 + τ₀)) 0 := by
  have hq : 0 < ((τ₀ : ℂ) / (1 + τ₀)).im := by
    rw [add_comm]; exact im_div_add_one_pos τ₀.im_pos
  have h1 : (1 : ℂ) + τ₀ ≠ 0 := by rw [add_comm]; exact add_one_ne_zero_of_im_pos τ₀.im_pos
  have hM : (τ₀ : ℂ) / (1 + τ₀) / (1 - (τ₀ : ℂ) / (1 + τ₀)) = τ₀ := by
    field_simp; ring
  have h := hasResidueAt_leechHat_of_STS τ₀ hq hM (hasResidueAt_leechKernel_self hA hB)
  simpa using h

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at the point `Sτ/(1 + Sτ)` of the semicircle `|z − 1/2| = 1/2`. -/
theorem hasResidueAt_leechHatKernel_semicircle_S :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) / (1 + ((ModularGroup.S • τ₀ : ℍ) : ℂ))) 0 := by
  set σ := ModularGroup.S • τ₀
  have hq : 0 < ((σ : ℂ) / (1 + σ)).im := by
    rw [add_comm]; exact im_div_add_one_pos σ.im_pos
  have h1 : (1 : ℂ) + σ ≠ 0 := by rw [add_comm]; exact add_one_ne_zero_of_im_pos σ.im_pos
  have hM : (σ : ℂ) / (1 + σ) / (1 - (σ : ℂ) / (1 + σ)) = σ := by
    field_simp; ring
  have h := hasResidueAt_leechHat_of_STS τ₀ hq hM (hasResidueAt_leechKernel_S hA hB)
  simpa using h

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at the point `τ/(1 − τ)` of the semicircle `|z + 1/2| = 1/2`. -/
theorem hasResidueAt_leechHatKernel_semicircle'_self :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀) ((τ₀ : ℂ) / (1 - τ₀)) 0 := by
  have hq : 0 < ((τ₀ : ℂ) / (1 - τ₀)).im := im_div_one_sub_pos τ₀.im_pos
  have h1 : (1 : ℂ) - τ₀ ≠ 0 := one_sub_ne_zero_of_im_pos τ₀.im_pos
  have hM : (τ₀ : ℂ) / (1 - τ₀) / ((τ₀ : ℂ) / (1 - τ₀) + 1) = τ₀ := by
    field_simp; ring
  have h := hasResidueAt_leechHat_of_TST τ₀ hq hM (hasResidueAt_leechKernel_self hA hB)
  simpa using h

/-- `𝒦̂⁽²⁴⁾(τ, ·)` is regular at the point `Sτ/(1 − Sτ)` of the semicircle `|z + 1/2| = 1/2`. -/
theorem hasResidueAt_leechHatKernel_semicircle'_S :
    HasResidueAt (rightC ckmrvLeechHatKernel τ₀)
      (((ModularGroup.S • τ₀ : ℍ) : ℂ) / (1 - ((ModularGroup.S • τ₀ : ℍ) : ℂ))) 0 := by
  set σ := ModularGroup.S • τ₀
  have hq : 0 < ((σ : ℂ) / (1 - σ)).im := im_div_one_sub_pos σ.im_pos
  have h1 : (1 : ℂ) - σ ≠ 0 := one_sub_ne_zero_of_im_pos σ.im_pos
  have hM : (σ : ℂ) / (1 - σ) / ((σ : ℂ) / (1 - σ) + 1) = σ := by
    field_simp; ring
  have h := hasResidueAt_leechHat_of_TST τ₀ hq hM (hasResidueAt_leechKernel_S hA hB)
  simpa using h

end SpecialPoints2

end E8Leech
