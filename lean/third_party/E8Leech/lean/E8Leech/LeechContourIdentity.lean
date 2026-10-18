import E8Leech.LeechKernelPoles
import E8Leech.LeechContourDefs

/-!
# The integrands `F±` of the contour identity in dimension 24: residues and regularity

For `τ = iy` (`y ≠ 1`) the function `𝒦̂⁽²⁴⁾(τ, ·)` is holomorphic on the closed triangles
`(0, 1, ∞)` and `(−1, 0, ∞)` off the same special points as in dimension eight, with poles only at
`Sτ ± 1` (residues `±(Sτ)¹²/(2π)`, `LeechKernelPoles`). The cusp parts `P_{±1}` are holomorphic in
the upper half-plane, so `F₊ = (𝒦̂ − P₁) E − c₊ k₊` and `F₋ = (𝒦̂ − P₋₁) E − c₋ k₋` have removable
singularities at the special points (`res_leechFPlus_special`, `res_leechFMinus_special`) and
extend to functions `G±` that are differentiable on the closed triangles (`exists_leechGPlus`,
`exists_leechGMinus`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Holomorphy away from the `j`-coincidence locus -/

theorem differentiableAt_rightC_leechMinus (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC τ₀) :
    DifferentiableAt ℂ (rightC ckmrvLeechMinusKernel τ₀) z := by
  have hnum : DifferentiableAt ℂ (leechMinusNumC τ₀) z := by
    unfold leechMinusNumC
    have h1 := (analyticAt_of_upperHalfPlane_mdifferentiable
      (mdifferentiable_leechMinusSingNum (ofComplex (τ₀ : ℂ))) ⟨z, hz⟩).differentiableAt
    have h2 := (analyticAt_of_upperHalfPlane_mdifferentiable
      mdifferentiable_modularDiscriminant ⟨z, hz⟩).differentiableAt
    exact (h1.div (h2.pow 2) (pow_ne_zero 2 (ModularForm.discriminant_ne_zero _))).const_mul _
  have hden : DifferentiableAt ℂ (fun w => kleinJC τ₀ - kleinJC w) z :=
    (differentiableAt_const _).sub (hasDerivAt_kleinJC ⟨z, hz⟩).differentiableAt
  have h := hnum.div hden (sub_ne_zero.mpr (Ne.symm hj))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [rightC, Pi.div_apply]
  rw [← ckmrvLeechMinusKernel_eq_numC, UpperHalfPlane.ofComplex_apply]

theorem differentiableAt_rightC_leechPlus (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC τ₀) :
    DifferentiableAt ℂ (rightC ckmrvLeechPlusKernel τ₀) z := by
  have hnum : DifferentiableAt ℂ (leechPlusNumC τ₀) z := by
    have h := mdifferentiable_ckmrvLeechPlusNormalizedNumerator.comp
      ((mdifferentiable_const (c := ofComplex (τ₀ : ℂ))).prodMk mdifferentiable_id)
    exact (analyticAt_of_upperHalfPlane_mdifferentiable h ⟨z, hz⟩).differentiableAt
  have hden : DifferentiableAt ℂ (fun w => kleinJC τ₀ - kleinJC w) z :=
    (differentiableAt_const _).sub (hasDerivAt_kleinJC ⟨z, hz⟩).differentiableAt
  have h := hnum.div hden (sub_ne_zero.mpr (Ne.symm hj))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_kleinJC_ne_of_ne hz hj] with w hw
  simp only [rightC, Pi.div_apply]
  have e := ckmrvLeechPlusKernel_eq_numC (τ := (τ₀ : ℂ)) (z := w)
    (by rw [show kleinJC (τ₀ : ℂ) = kleinJC τ₀ from rfl]; exact Ne.symm hw)
  rw [UpperHalfPlane.ofComplex_apply] at e
  exact e

theorem differentiableAt_rightC_leechHatKernel (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC τ₀) :
    DifferentiableAt ℂ (rightC ckmrvLeechHatKernel τ₀) z := by
  have h := ((differentiableAt_rightC_leechPlus τ₀ hz hj).sub
    (differentiableAt_rightC_leechMinus τ₀ hz hj)).div_const 2
  exact h

/-! ## The residues of `𝒦̂⁽²⁴⁾(iy, ·)` at the special points -/

section LeechHatResidues

variable {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
include hy hy1

theorem res_leechHat_tau :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) ((imagPt y : ℍ) : ℂ) 0 :=
  hasResidueAt_leechHatKernel_self (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_leechHat_sigma : HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (sigmaC y) 0 := by
  have h := hasResidueAt_leechHatKernel_S (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_leechHat_tau_add_one :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (((imagPt y : ℍ) : ℂ) + 1) 0 :=
  hasResidueAt_leechHatKernel_add_one (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_leechHat_sigma_add_one :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (sigmaC y + 1)
      (sigmaC y ^ 12 / (2 * (π : ℂ))) := by
  have h := hasResidueAt_leechHatKernel_S_add_one (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_leechHat_tau_semicircle :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y))
      (((imagPt y : ℍ) : ℂ) / (1 + ((imagPt y : ℍ) : ℂ))) 0 :=
  hasResidueAt_leechHatKernel_semicircle_self (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_leechHat_sigma_semicircle :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (sigmaC y / (1 + sigmaC y)) 0 := by
  have h := hasResidueAt_leechHatKernel_semicircle_S (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_leechHat_tau_sub_one :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (((imagPt y : ℍ) : ℂ) - 1) 0 :=
  hasResidueAt_leechHatKernel_T (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_leechHat_sigma_sub_one :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (sigmaC y - 1)
      (-(sigmaC y ^ 12 / (2 * (π : ℂ)))) := by
  have h := hasResidueAt_leechHatKernel_ST (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_leechHat_tau_semicircle' :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y))
      (((imagPt y : ℍ) : ℂ) / (1 - ((imagPt y : ℍ) : ℂ))) 0 :=
  hasResidueAt_leechHatKernel_semicircle'_self (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_leechHat_sigma_semicircle' :
    HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) (sigmaC y / (1 - sigmaC y)) 0 := by
  have h := hasResidueAt_leechHatKernel_semicircle'_S (eisensteinFour_imagPt_ne_zero hy)
    (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

end LeechHatResidues

/-! ## The residues of `F±` -/

theorem continuousAt_cuspPartPlus_mul (A B : ℂ) (ρ : ℝ) {p : ℂ} (hp : 0 < p.im) :
    ContinuousAt (fun z => cuspPartPlus A B z * gaussE ρ z) p :=
  (differentiableAt_cuspPartPlus A B (one_sub_ne_zero_of_im_pos hp)).continuousAt.mul
    (continuous_gaussE ρ).continuousAt

theorem continuousAt_cuspPartMinus_mul (A B : ℂ) (ρ : ℝ) {p : ℂ} (hp : 0 < p.im) :
    ContinuousAt (fun z => cuspPartMinus A B z * gaussE ρ z) p :=
  (differentiableAt_cuspPartMinus A B (add_one_ne_zero_of_im_pos hp)).continuousAt.mul
    (continuous_gaussE ρ).continuousAt

theorem res_leechPlusF_of {y ρ : ℝ} {p R : ℂ} (hp : 0 < p.im)
    (h : HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) p R) :
    HasResidueAt (leechPlusF y ρ) p (R * gaussE ρ p) := by
  have h1 := h.mul_continuousAt (continuous_gaussE ρ).continuousAt
  have h2 : HasResidueAt (fun z =>
      cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z * gaussE ρ z) p 0 :=
    HasResidueAt.of_tendsto
      ((continuousAt_cuspPartPlus_mul _ _ ρ hp).tendsto.mono_left nhdsWithin_le_nhds)
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  exact h3.congr (Eventually.of_forall fun z => by simp only [leechPlusF]; ring)

theorem res_leechMinusF_of {y ρ : ℝ} {p R : ℂ} (hp : 0 < p.im)
    (h : HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) p R) :
    HasResidueAt (leechMinusF y ρ) p (R * gaussE ρ p) := by
  have h1 := h.mul_continuousAt (continuous_gaussE ρ).continuousAt
  have h2 : HasResidueAt (fun z =>
      cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z * gaussE ρ z) p 0 :=
    HasResidueAt.of_tendsto
      ((continuousAt_cuspPartMinus_mul _ _ ρ hp).tendsto.mono_left nhdsWithin_le_nhds)
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  exact h3.congr (Eventually.of_forall fun z => by simp only [leechMinusF]; ring)

section LeechFResidues

variable {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ)
include hy hy1

omit hy hy1 in
theorem res_leechFPlus_of {p R K : ℂ} (hp : 0 < p.im)
    (hR : HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) p R)
    (hK : HasResidueAt (principalK (sigmaC y + 1)) p K) :
    HasResidueAt (leechFPlus y ρ) p (R * gaussE ρ p - leechCPlus y ρ * K) :=
  (res_leechPlusF_of hp hR).sub (hK.const_mul _)

omit hy hy1 in
theorem res_leechFMinus_of {p R K : ℂ} (hp : 0 < p.im)
    (hR : HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) p R)
    (hK : HasResidueAt (principalK (sigmaC y - 1)) p K) :
    HasResidueAt (leechFMinus y ρ) p (R * gaussE ρ p - leechCMinus y ρ * K) :=
  (res_leechMinusF_of hp hR).sub (hK.const_mul _)

/-- `F₊` has removable singularities at all six special points. -/
theorem res_leechFPlus_special : ∀ p ∈ specialPlus y, HasResidueAt (leechFPlus y ρ) p 0 := by
  have hσ := im_sigmaC_pos hy
  have hτ := im_tauC_pos (y := y)
  have hp : 0 < (sigmaC y + 1).im := by simpa using hσ
  have hst := sigmaC_mul_tau hy
  have hσ0 : sigmaC y ≠ 0 := fun h => by simp [h] at hσ
  have hzero : ∀ q : ℂ, 0 < q.im → q ≠ sigmaC y + 1 →
      HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) q 0 →
      HasResidueAt (leechFPlus y ρ) q 0 := by
    intro q hq hne hR
    have h := res_leechFPlus_of ρ hq hR
      (hasResidueAt_principalK_of_ne hne (ne_conj_of_im_pos hq hp))
    simpa using h
  intro q hq
  simp only [specialPlus, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with h | h | h | h | h | h <;> subst h
  · refine hzero _ hτ (ne_of_re_ne ?_) (res_leechHat_tau hy hy1)
    rw [re_tauC hy]; simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ hσ (ne_of_re_ne ?_) (res_leechHat_sigma hy hy1)
    simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ (by simpa using hτ) (fun e => tauC_ne_sigmaC hy hy1 (by linear_combination e))
      (res_leechHat_tau_add_one hy hy1)
  · have h := res_leechFPlus_of ρ hp (res_leechHat_sigma_add_one hy hy1)
      (hasResidueAt_principalK_self hp)
    have e : sigmaC y ^ 12 / (2 * (π : ℂ)) * gaussE ρ (sigmaC y + 1) - leechCPlus y ρ * 1 = 0 := by
      simp [leechCPlus]
    rwa [e] at h
  · have h1 : (1 : ℂ) + sigmaC y ≠ 0 := by rw [add_comm]; exact add_one_ne_zero_of_im_pos hσ
    refine hzero _ (by rw [add_comm]; exact im_div_add_one_pos hσ) (fun e => ?_)
      (res_leechHat_sigma_semicircle hy hy1)
    rw [div_eq_iff h1] at e
    have := congrArg Complex.im e
    simp [re_imagPt (inv_pos.mpr hy), Complex.mul_im] at this
    have h2 : 0 < (imagPt y⁻¹).im := (imagPt y⁻¹).im_pos
    linarith
  · have h1 : (1 : ℂ) + ((imagPt y : ℍ) : ℂ) ≠ 0 := by
      rw [add_comm]; exact add_one_ne_zero_of_im_pos hτ
    refine hzero _ (by rw [add_comm]; exact im_div_add_one_pos hτ) (fun e => ?_)
      (res_leechHat_tau_semicircle hy hy1)
    rw [div_eq_iff h1] at e
    apply hσ0
    linear_combination -e - hst

/-- `F₋` has removable singularities at all six special points. -/
theorem res_leechFMinus_special : ∀ p ∈ specialMinus y, HasResidueAt (leechFMinus y ρ) p 0 := by
  have hσ := im_sigmaC_pos hy
  have hτ := im_tauC_pos (y := y)
  have hp : 0 < (sigmaC y - 1).im := by simpa using hσ
  have hst := sigmaC_mul_tau hy
  have hσ0 : sigmaC y ≠ 0 := fun h => by simp [h] at hσ
  have hzero : ∀ q : ℂ, 0 < q.im → q ≠ sigmaC y - 1 →
      HasResidueAt (rightC ckmrvLeechHatKernel (imagPt y)) q 0 →
      HasResidueAt (leechFMinus y ρ) q 0 := by
    intro q hq hne hR
    have h := res_leechFMinus_of ρ hq hR
      (hasResidueAt_principalK_of_ne hne (ne_conj_of_im_pos hq hp))
    simpa using h
  intro q hq
  simp only [specialMinus, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with h | h | h | h | h | h <;> subst h
  · refine hzero _ hτ (ne_of_re_ne ?_) (res_leechHat_tau hy hy1)
    rw [re_tauC hy]; simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ hσ (ne_of_re_ne ?_) (res_leechHat_sigma hy hy1)
    simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ (by simpa using hτ) (fun e => tauC_ne_sigmaC hy hy1 (by linear_combination e))
      (res_leechHat_tau_sub_one hy hy1)
  · have h := res_leechFMinus_of ρ hp (res_leechHat_sigma_sub_one hy hy1)
      (hasResidueAt_principalK_self hp)
    have e : -(sigmaC y ^ 12 / (2 * (π : ℂ))) * gaussE ρ (sigmaC y - 1) -
        leechCMinus y ρ * 1 = 0 := by
      simp [leechCMinus]
    rwa [e] at h
  · have h1 : (1 : ℂ) - ((imagPt y : ℍ) : ℂ) ≠ 0 := one_sub_ne_zero_of_im_pos hτ
    refine hzero _ (im_div_one_sub_pos hτ) (fun e => ?_) (res_leechHat_tau_semicircle' hy hy1)
    rw [div_eq_iff h1] at e
    apply hσ0
    linear_combination -e + hst
  · have h1 : (1 : ℂ) - sigmaC y ≠ 0 := one_sub_ne_zero_of_im_pos hσ
    refine hzero _ (im_div_one_sub_pos hσ) (fun e => ?_) (res_leechHat_sigma_semicircle' hy hy1)
    rw [div_eq_iff h1] at e
    have := congrArg Complex.im e
    simp [re_imagPt (inv_pos.mpr hy), Complex.mul_im] at this
    have h2 : 0 < (imagPt y⁻¹).im := (imagPt y⁻¹).im_pos
    linarith

end LeechFResidues

/-! ## Regularity of `F±` off the special points -/

theorem differentiableAt_leechPlusF {y ρ : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) : DifferentiableAt ℂ (leechPlusF y ρ) z :=
  ((differentiableAt_rightC_leechHatKernel (imagPt y) hz hj).sub
    (differentiableAt_cuspPartPlus _ _ (one_sub_ne_zero_of_im_pos hz))).mul
      (differentiable_gaussE ρ z)

theorem differentiableAt_leechMinusF {y ρ : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) : DifferentiableAt ℂ (leechMinusF y ρ) z :=
  ((differentiableAt_rightC_leechHatKernel (imagPt y) hz hj).sub
    (differentiableAt_cuspPartMinus _ _ (add_one_ne_zero_of_im_pos hz))).mul
      (differentiable_gaussE ρ z)

theorem differentiableAt_leechFPlus {y ρ : ℝ} (hy : 0 < y) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) (hz1 : z ≠ sigmaC y + 1) :
    DifferentiableAt ℂ (leechFPlus y ρ) z := by
  have hp : 0 < (sigmaC y + 1).im := by simpa using im_sigmaC_pos hy
  exact (differentiableAt_leechPlusF hz hj).sub ((differentiableAt_const _).mul
    (differentiableAt_principalK hz1 (ne_conj_of_im_pos hz hp)))

theorem differentiableAt_leechFMinus {y ρ : ℝ} (hy : 0 < y) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) (hz1 : z ≠ sigmaC y - 1) :
    DifferentiableAt ℂ (leechFMinus y ρ) z := by
  have hp : 0 < (sigmaC y - 1).im := by simpa using im_sigmaC_pos hy
  exact (differentiableAt_leechMinusF hz hj).sub ((differentiableAt_const _).mul
    (differentiableAt_principalK hz1 (ne_conj_of_im_pos hz hp)))

theorem eventually_differentiableAt_leechFPlus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ)
    {p : ℂ} (hp : 0 < p.im) : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ (leechFPlus y ρ) z := by
  have hpos : ∀ᶠ z in 𝓝[≠] p, 0 < z.im :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto p).eventually (lt_mem_nhds hp))
  filter_upwards [hpos, eventually_kleinJC_ne_imagPt hy hy1 hp,
    eventually_ne_nhdsWithin_ne p (sigmaC y + 1)] with z hz hj hz1
  exact differentiableAt_leechFPlus hy hz hj hz1

theorem eventually_differentiableAt_leechFMinus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ)
    {p : ℂ} (hp : 0 < p.im) : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ (leechFMinus y ρ) z := by
  have hpos : ∀ᶠ z in 𝓝[≠] p, 0 < z.im :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto p).eventually (lt_mem_nhds hp))
  filter_upwards [hpos, eventually_kleinJC_ne_imagPt hy hy1 hp,
    eventually_ne_nhdsWithin_ne p (sigmaC y - 1)] with z hz hj hz1
  exact differentiableAt_leechFMinus hy hz hj hz1

/-! ## The corrected functions `G±` -/

theorem exists_leechGPlus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ) :
    ∃ G : ℂ → ℂ, (∀ z ∈ idealTriangleCl, DifferentiableAt ℂ G z) ∧
      ∀ z, z ∉ specialPlus y → G z = leechFPlus y ρ z := by
  obtain ⟨G, hG, hGF⟩ := exists_differentiable_update (K := idealTriangleCl) (specialPlus y)
    (leechFPlus y ρ)
    (fun z hz hzP => by
      have hj : kleinJC z ≠ kleinJC (imagPt y) := fun hj =>
        hzP (mem_specialPlus_of_kleinJC hy hz hj)
      have hz1 : z ≠ sigmaC y + 1 := fun h => hzP (by
        rw [h]; simp [specialPlus])
      exact differentiableAt_leechFPlus hy hz.1 hj hz1)
    (fun p hp => eventually_differentiableAt_leechFPlus hy hy1 ρ
      (im_pos_of_mem_specialPlus hy p hp))
    (res_leechFPlus_special hy hy1 ρ)
  exact ⟨G, fun z hz => hG z (Or.inl hz), hGF⟩

theorem exists_leechGMinus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ) :
    ∃ G : ℂ → ℂ, (∀ z, z + 1 ∈ idealTriangleCl → DifferentiableAt ℂ G z) ∧
      ∀ z, z ∉ specialMinus y → G z = leechFMinus y ρ z := by
  obtain ⟨G, hG, hGF⟩ := exists_differentiable_update (K := {z | z + 1 ∈ idealTriangleCl})
    (specialMinus y) (leechFMinus y ρ)
    (fun z hz hzP => by
      have hj : kleinJC z ≠ kleinJC (imagPt y) := fun hj =>
        hzP (mem_specialMinus_of_kleinJC hy hz hj)
      have hz1 : z ≠ sigmaC y - 1 := fun h => hzP (by
        rw [h]; simp [specialMinus])
      exact differentiableAt_leechFMinus hy (by simpa using hz.1) hj hz1)
    (fun p hp => eventually_differentiableAt_leechFMinus hy hy1 ρ
      (im_pos_of_mem_specialMinus hy p hp))
    (res_leechFMinus_special hy hy1 ρ)
  exact ⟨G, fun z hz => hG z (Or.inl hz), hGF⟩

end E8Leech
