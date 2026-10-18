import E8Leech.CKMRVContourKernel

/-!
# The CKMRV contour identity (**) in dimension eight

Known answer first: for `τ = iy` (`y ≠ 1`), `ρ > 0` and `E(z) = e^{πiρz}`, put `f = 𝒦̂(τ, ·) E`.
Its only poles on the closed triangles `(0, 1, ∞)` and `(−1, 0, ∞)` are `Sτ ± 1`, with residues
`±(Sτ)⁴ E(Sτ ± 1)/(2π)`. Subtracting the principal parts
`k±(z) = 1/(z − p±) − 1/(z − p̄±)` (`p± = Sτ ± 1`) leaves functions to which Cauchy's theorem on
the ideal triangle applies; the principal parts cancel on the imaginary axis because
`k₊(z + 1) = k₋(z − 1)`, and their remaining explicit integrals add up to `−2π`.

This file first removes the finitely many removable singularities (`exists_differentiable_update`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Removing finitely many removable singularities -/

theorem differentiableAt_update_of_hasResidueAt_zero {F : ℂ → ℂ} {p : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ F z) (hr : HasResidueAt F p 0) :
    DifferentiableAt ℂ (Function.update F p (limUnder (𝓝[≠] p) F)) p := by
  rw [eventually_nhdsWithin_iff] at hd
  have hs : {z | z ≠ p → DifferentiableAt ℂ F z} ∈ 𝓝 p := hd
  have hdiff : DifferentiableOn ℂ F ({z | z ≠ p → DifferentiableAt ℂ F z} \ {p}) :=
    fun z hz => (hz.1 hz.2).differentiableWithinAt
  have ho : (fun z => F z - F p) =o[𝓝[≠] p] fun z => (z - p)⁻¹ := by
    refine Asymptotics.isLittleO_of_tendsto (fun z hz => ?_) ?_
    · have : z - p = 0 := inv_eq_zero.mp hz
      rw [sub_eq_zero.mp this, sub_self]
    · have h1 : Tendsto (fun z => (z - p) * F z) (𝓝[≠] p) (𝓝 0) := hr
      have h2 : Tendsto (fun z => (z - p) * F p) (𝓝[≠] p) (𝓝 0) := by
        have := ((continuous_sub_right p).tendsto' p 0 (sub_self p)).mono_left
          (nhdsWithin_le_nhds (s := {p}ᶜ))
        simpa using this.mul_const (F p)
      have h3 := h1.sub h2
      rw [sub_zero] at h3
      refine h3.congr fun z => ?_
      rw [div_inv_eq_mul]
      ring
  exact (differentiableOn_update_limUnder_of_isLittleO hs hdiff ho).differentiableAt hs

/-- **Finitely many removable singularities.** -/
theorem exists_differentiable_update {K : Set ℂ} :
    ∀ (P : Finset ℂ) (F : ℂ → ℂ), (∀ z ∈ K, z ∉ P → DifferentiableAt ℂ F z) →
      (∀ p ∈ P, ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ F z) →
      (∀ p ∈ P, HasResidueAt F p 0) →
      ∃ G : ℂ → ℂ, (∀ z ∈ K ∪ ↑P, DifferentiableAt ℂ G z) ∧ ∀ z, z ∉ P → G z = F z := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro F hd _ _
    refine ⟨F, fun z hz => ?_, fun _ _ => rfl⟩
    rcases hz with hz | hz
    · exact hd z hz (Finset.notMem_empty z)
    · exact absurd hz (Finset.notMem_empty z)
  | insert p P hp ih =>
    intro F hd hnear hr
    set F₁ := Function.update F p (limUnder (𝓝[≠] p) F) with hF₁
    have hF₁p : DifferentiableAt ℂ F₁ p :=
      differentiableAt_update_of_hasResidueAt_zero (hnear p (Finset.mem_insert_self p P))
        (hr p (Finset.mem_insert_self p P))
    have hne : ∀ {z : ℂ}, z ≠ p → F₁ =ᶠ[𝓝 z] F := fun {z} hz => by
      filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hz)]
        with w hw
      exact Function.update_of_ne (Set.mem_compl_singleton_iff.mp hw) _ _
    have hd₁ : ∀ z ∈ K, z ∉ P → DifferentiableAt ℂ F₁ z := by
      intro z hz hzP
      by_cases hzp : z = p
      · rw [hzp]; exact hF₁p
      · exact (hd z hz (by simp [Finset.mem_insert, hzp, hzP])).congr_of_eventuallyEq (hne hzp)
    have hnear₁ : ∀ q ∈ P, ∀ᶠ z in 𝓝[≠] q, DifferentiableAt ℂ F₁ z := by
      intro q hq
      have hqp : q ≠ p := fun h => hp (h ▸ hq)
      have hpq : ∀ᶠ z in 𝓝[≠] q, z ≠ p :=
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hqp))
      filter_upwards [hnear q (Finset.mem_insert_of_mem hq), hpq] with z hz hzp
      exact hz.congr_of_eventuallyEq (hne hzp)
    have hr₁ : ∀ q ∈ P, HasResidueAt F₁ q 0 := by
      intro q hq
      have hqp : q ≠ p := fun h => hp (h ▸ hq)
      refine (hr q (Finset.mem_insert_of_mem hq)).congr ?_
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hqp))] with w hw
      exact (Function.update_of_ne (Set.mem_compl_singleton_iff.mp hw) _ _).symm
    obtain ⟨G, hG, hGF⟩ := ih F₁ hd₁ hnear₁ hr₁
    refine ⟨G, fun z hz => ?_, fun z hz => ?_⟩
    · rcases hz with hz | hz
      · exact hG z (Or.inl hz)
      · rcases Finset.mem_insert.mp hz with h | h
        · -- `z = p`: `G` agrees with `F₁` near `p`, which is differentiable at `p`
          rw [h]
          have hpP : ∀ᶠ w in 𝓝 p, w ∉ P := by
            have hc : IsClosed (↑P : Set ℂ) := P.finite_toSet.isClosed
            exact hc.isOpen_compl.mem_nhds hp
          have heq : G =ᶠ[𝓝 p] F₁ := by
            filter_upwards [hpP] with w hw
            exact hGF w hw
          exact hF₁p.congr_of_eventuallyEq heq
        · exact hG z (Or.inr h)
    · have hzp : z ≠ p := fun h => hz (h ▸ Finset.mem_insert_self p P)
      have hzP : z ∉ P := fun h => hz (Finset.mem_insert_of_mem h)
      rw [hGF z hzP]
      exact Function.update_of_ne hzp _ _

/-! ## A global bound on the closed triangle from bounds near its ends -/

theorem isClosed_triangleCutCl (W : ℝ) : IsClosed (triangleCutCl W) := by
  have c1 := Complex.continuous_im
  have c2 := Complex.continuous_re
  have c3 : Continuous fun z : ℂ => ‖z - 1 / 2‖ := (continuous_id.sub continuous_const).norm
  have c4 : Continuous fun z : ℂ => ‖z‖ := continuous_norm
  have c5 : Continuous fun z : ℂ => ‖z - 1‖ := (continuous_id.sub continuous_const).norm
  exact (isClosed_le continuous_const c1).inter ((isClosed_le continuous_const c2).inter
    ((isClosed_le c2 continuous_const).inter ((isClosed_le continuous_const c3).inter
      ((isClosed_le c1 continuous_const).inter ((isClosed_le continuous_const c4).inter
        (isClosed_le continuous_const c5))))))

theorem isCompact_triangleCutCl (W : ℝ) : IsCompact (triangleCutCl W) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_triangleCutCl W)
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := W + 1)).subset fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hz.2.1, abs_of_nonneg hz.1] at this
  linarith [hz.2.2.1, hz.2.2.2.2.1]

theorem triangleCutCl_subset_cl {W : ℝ} (hW : 0 < W) : triangleCutCl W ⊆ idealTriangleCl :=
  fun _ hz => ⟨im_pos_of_mem_triangleCutCl hW hz, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩

theorem idealTriangle_bound_of_pieces {G : ℂ → ℂ} (hc : ContinuousOn G idealTriangleCl)
    {V M δ₀ M₀ δ₁ M₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁)
    (htop : ∀ z ∈ idealTriangleCl, V ≤ z.im → ‖G z‖ ≤ M / (1 + z.im) ^ 2)
    (h0 : ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ₀ → ‖G z‖ ≤ M₀)
    (h1 : ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ₁ → ‖G z‖ ≤ M₁) :
    ∃ C, ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2 := by
  set W := max (max V 1) (max (1 / (2 * δ₀)) (1 / (2 * δ₁))) with hWdef
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) (le_max_left _ _)
  have hW : 0 < W := by linarith
  have hδW : ∀ δ : ℝ, 0 < δ → 1 / (2 * δ) ≤ W → 1 / (2 * W) ≤ δ := by
    intro δ hδ h
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith
  have hδW₀ := hδW δ₀ hδ₀ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hδW₁ := hδW δ₁ hδ₁ (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨MK, hMK⟩ := (isCompact_triangleCutCl W).exists_bound_of_continuousOn
    (hc.mono (triangleCutCl_subset_cl hW))
  refine ⟨max (max M (4 * M₀)) (max (4 * M₁) (MK * (1 + W) ^ 2)), fun z hz => ?_⟩
  have hv : 0 < z.im := hz.1
  have hpos : 0 < (1 + z.im) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hG := norm_nonneg (G z)
  by_cases htopc : W ≤ z.im
  · have h := htop z hz (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htopc)
    rw [le_div_iff₀ hpos] at h
    exact h.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  push Not at htopc
  by_cases hc0 : ‖z‖ ≤ 1 / (2 * W)
  · have h := h0 z hz (hc0.trans hδW₀)
    have him : z.im ≤ 1 := by
      have := Complex.abs_im_le_norm z
      rw [abs_of_pos hv] at this
      have : 1 / (2 * W) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    have : (1 + z.im) ^ 2 ≤ 4 := by nlinarith
    calc ‖G z‖ * (1 + z.im) ^ 2 ≤ M₀ * 4 := by nlinarith
      _ ≤ _ := by
        rw [mul_comm]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  push Not at hc0
  by_cases hc1 : ‖z - 1‖ ≤ 1 / (2 * W)
  · have h := h1 z hz (hc1.trans hδW₁)
    have him : z.im ≤ 1 := by
      have := Complex.abs_im_le_norm (z - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero, abs_of_pos hv] at this
      have : 1 / (2 * W) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    have : (1 + z.im) ^ 2 ≤ 4 := by nlinarith
    calc ‖G z‖ * (1 + z.im) ^ 2 ≤ M₁ * 4 := by nlinarith
      _ ≤ _ := by
        rw [mul_comm]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  push Not at hc1
  have hK : z ∈ triangleCutCl W :=
    ⟨hv.le, hz.2.1, hz.2.2.1, hz.2.2.2, htopc.le, hc0.le, hc1.le⟩
  have h := hMK z hK
  have : (1 + z.im) ^ 2 ≤ (1 + W) ^ 2 := by nlinarith
  calc ‖G z‖ * (1 + z.im) ^ 2 ≤ MK * (1 + W) ^ 2 := by
        apply mul_le_mul h this hpos.le (hG.trans h)
    _ ≤ _ := le_trans (le_max_right _ _) (le_max_right _ _)

/-! ## The integrand `f = 𝒦̂(iy, ·) e^{πiρ·}` and its principal parts -/

/-- `E(z) = e^{πiρz}`. -/
def gaussE (ρ : ℝ) (z : ℂ) : ℂ := cexp (π * I * ρ * z)

theorem differentiable_gaussE (ρ : ℝ) : Differentiable ℂ (gaussE ρ) := by
  unfold gaussE; fun_prop

theorem continuous_gaussE (ρ : ℝ) : Continuous (gaussE ρ) := (differentiable_gaussE ρ).continuous

theorem norm_gaussE (ρ : ℝ) (z : ℂ) : ‖gaussE ρ z‖ = Real.exp (-(π * ρ) * z.im) := by
  rw [gaussE, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem gaussE_add (ρ : ℝ) (z w : ℂ) : gaussE ρ (z + w) = gaussE ρ z * gaussE ρ w := by
  simp only [gaussE, ← Complex.exp_add]; ring_nf

/-- `f = 𝒦̂(iy, ·) E`. -/
def contourF (y ρ : ℝ) (z : ℂ) : ℂ := rightC ckmrvEightHatKernel (imagPt y) z * gaussE ρ z

/-- The principal part with poles at `p` and `p̄`. -/
def principalK (p z : ℂ) : ℂ := 1 / (z - p) - 1 / (z - (starRingEnd ℂ) p)

theorem HasResidueAt.mul_continuousAt {f g : ℂ → ℂ} {p R : ℂ} (hf : HasResidueAt f p R)
    (hg : ContinuousAt g p) : HasResidueAt (fun z => f z * g z) p (R * g p) := by
  unfold HasResidueAt at *
  exact (hf.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)).congr fun z => by ring

theorem HasResidueAt.const_mul {f : ℂ → ℂ} {p R : ℂ} (hf : HasResidueAt f p R) (c : ℂ) :
    HasResidueAt (fun z => c * f z) p (c * R) := by
  unfold HasResidueAt at *
  exact (hf.const_mul c).congr fun z => by ring

theorem conj_ne_of_im_pos {p : ℂ} (hp : 0 < p.im) : p ≠ (starRingEnd ℂ) p := fun h => by
  have := congrArg Complex.im h
  simp at this; linarith

theorem hasResidueAt_principalK_self {p : ℂ} (hp : 0 < p.im) : HasResidueAt (principalK p) p 1 := by
  have hne : p - (starRingEnd ℂ) p ≠ 0 := sub_ne_zero.mpr (conj_ne_of_im_pos hp)
  have hc : ContinuousAt (fun z => (z - p) / (z - (starRingEnd ℂ) p)) p :=
    (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) hne
  have ht := hc.tendsto
  simp only [sub_self, zero_div] at ht
  unfold HasResidueAt
  have h := (tendsto_const_nhds (x := (1 : ℂ))).sub (ht.mono_left (nhdsWithin_le_nhds (s := {p}ᶜ)))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z - p ≠ 0 := sub_ne_zero.mpr hz
  simp only [principalK]
  rw [mul_sub, mul_one_div_cancel hz', mul_one_div]

theorem hasResidueAt_principalK_of_ne {p q : ℂ} (hq : q ≠ p) (hq' : q ≠ (starRingEnd ℂ) p) :
    HasResidueAt (principalK p) q 0 := by
  refine HasResidueAt.of_tendsto ((ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds)
  exact ((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
    (sub_ne_zero.mpr hq)).sub (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr hq')))

theorem differentiableAt_principalK {p z : ℂ} (hz : z ≠ p) (hz' : z ≠ (starRingEnd ℂ) p) :
    DifferentiableAt ℂ (principalK p) z := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - p)) z :=
    (differentiableAt_const _).div ((differentiableAt_fun_id).sub (differentiableAt_const _))
      (sub_ne_zero.mpr hz)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - (starRingEnd ℂ) p)) z :=
    (differentiableAt_const _).div ((differentiableAt_fun_id).sub (differentiableAt_const _))
      (sub_ne_zero.mpr hz')
  exact h1.sub h2

/-- The translation symmetry `k₊(z + 1) = k₋(z − 1)` that kills the principal parts on the
imaginary axis. -/
theorem principalK_add_one_eq (σ z : ℂ) :
    principalK (σ + 1) (z + 1) = principalK (σ - 1) (z - 1) := by
  simp only [principalK, map_add, map_sub, map_one]
  congr 1 <;> congr 1 <;> ring

/-! ## The special points for `τ = iy` -/

theorem S_smul_imagPt {y : ℝ} (hy : 0 < y) : ModularGroup.S • imagPt y = imagPt y⁻¹ := by
  have h := S_smul_imagPt_inv (t := y⁻¹) (inv_pos.mpr hy)
  rwa [inv_inv] at h

/-- `σ = Sτ = i/y` as a complex number. -/
abbrev sigmaC (y : ℝ) : ℂ := ((imagPt y⁻¹ : ℍ) : ℂ)

theorem sigmaC_mul_tau {y : ℝ} (hy : 0 < y) : sigmaC y * ((imagPt y : ℍ) : ℂ) = -1 := by
  have h := coe_S_smul_mul (imagPt y)
  rwa [S_smul_imagPt hy] at h

theorem coe_imagPt_eq_I_mul {y : ℝ} (hy : 0 < y) : ((imagPt y : ℍ) : ℂ) = I * y := coe_imagPt hy

theorem sigmaC_eq {y : ℝ} (hy : 0 < y) : sigmaC y = I * (y⁻¹ : ℝ) := coe_imagPt (inv_pos.mpr hy)

theorem im_sigmaC {y : ℝ} (hy : 0 < y) : (sigmaC y).im = y⁻¹ := by
  rw [sigmaC_eq hy]; simp

theorem re_sigmaC {y : ℝ} (hy : 0 < y) : (sigmaC y).re = 0 := by
  rw [sigmaC_eq hy]; simp

theorem re_tauC {y : ℝ} (hy : 0 < y) : ((imagPt y : ℍ) : ℂ).re = 0 := by
  rw [coe_imagPt hy]; simp

theorem re_imagPt {t : ℝ} (ht : 0 < t) : (imagPt t).re = 0 := by
  show ((imagPt t : ℍ) : ℂ).re = 0
  rw [coe_imagPt ht]; simp

theorem tauC_ne_sigmaC {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) : ((imagPt y : ℍ) : ℂ) ≠ sigmaC y := by
  intro h
  have := congrArg Complex.im h
  rw [coe_imagPt hy, sigmaC_eq hy] at this
  simp at this
  have : y * y = 1 := by nth_rewrite 2 [this]; exact mul_inv_cancel₀ hy.ne'
  have : (y - 1) * (y + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h' | h'
  · exact hy1 (by linarith)
  · linarith

section HatResidues

variable {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
include hy hy1

theorem res_hat_tau :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) ((imagPt y : ℍ) : ℂ) 0 :=
  hasResidueAt_hatKernel_self (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_hat_sigma : HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (sigmaC y) 0 := by
  have h := hasResidueAt_hatKernel_S (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_hat_tau_add_one :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (((imagPt y : ℍ) : ℂ) + 1) 0 :=
  hasResidueAt_hatKernel_add_one (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_hat_sigma_add_one :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (sigmaC y + 1)
      (sigmaC y ^ 4 / (2 * (π : ℂ))) := by
  have h := hasResidueAt_hatKernel_S_add_one (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_hat_tau_semicircle :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y))
      (((imagPt y : ℍ) : ℂ) / (1 + ((imagPt y : ℍ) : ℂ))) 0 :=
  hasResidueAt_hatKernel_semicircle_self (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_hat_sigma_semicircle :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (sigmaC y / (1 + sigmaC y)) 0 := by
  have h := hasResidueAt_hatKernel_semicircle_S (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_hat_tau_sub_one :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (((imagPt y : ℍ) : ℂ) - 1) 0 :=
  hasResidueAt_hatKernel_T (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_hat_sigma_sub_one :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (sigmaC y - 1)
      (-(sigmaC y ^ 4 / (2 * (π : ℂ)))) := by
  have h := hasResidueAt_hatKernel_ST (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

theorem res_hat_tau_semicircle' :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y))
      (((imagPt y : ℍ) : ℂ) / (1 - ((imagPt y : ℍ) : ℂ))) 0 :=
  hasResidueAt_hatKernel_semicircle'_self (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)

theorem res_hat_sigma_semicircle' :
    HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) (sigmaC y / (1 - sigmaC y)) 0 := by
  have h := hasResidueAt_hatKernel_semicircle'_S (eisensteinFour_imagPt_ne_zero hy) (eisensteinSix_imagPt_ne_zero hy hy1)
  rwa [S_smul_imagPt hy] at h

end HatResidues

/-! ## The two functions `F± = f − c± k±` -/

/-- `c₊ = Res_{σ+1} f`. -/
def cPlus (y ρ : ℝ) : ℂ := sigmaC y ^ 4 / (2 * (π : ℂ)) * gaussE ρ (sigmaC y + 1)

/-- `c₋ = Res_{σ−1} f`. -/
def cMinus (y ρ : ℝ) : ℂ := -(sigmaC y ^ 4 / (2 * (π : ℂ))) * gaussE ρ (sigmaC y - 1)

/-- `F₊ = f − c₊ k₊`, regular on the closed triangle `(0, 1, ∞)`. -/
def fPlus (y ρ : ℝ) (z : ℂ) : ℂ := contourF y ρ z - cPlus y ρ * principalK (sigmaC y + 1) z

/-- `F₋ = f − c₋ k₋`, regular on the closed triangle `(−1, 0, ∞)`. -/
def fMinus (y ρ : ℝ) (z : ℂ) : ℂ := contourF y ρ z - cMinus y ρ * principalK (sigmaC y - 1) z

/-- The six special points on the boundary of `(0, 1, ∞)`. -/
def specialPlus (y : ℝ) : Finset ℂ :=
  {((imagPt y : ℍ) : ℂ), sigmaC y, ((imagPt y : ℍ) : ℂ) + 1, sigmaC y + 1,
    sigmaC y / (1 + sigmaC y), ((imagPt y : ℍ) : ℂ) / (1 + ((imagPt y : ℍ) : ℂ))}

/-- The six special points on the boundary of `(−1, 0, ∞)`. -/
def specialMinus (y : ℝ) : Finset ℂ :=
  {((imagPt y : ℍ) : ℂ), sigmaC y, ((imagPt y : ℍ) : ℂ) - 1, sigmaC y - 1,
    ((imagPt y : ℍ) : ℂ) / (1 - ((imagPt y : ℍ) : ℂ)), sigmaC y / (1 - sigmaC y)}

theorem res_contourF_of {y ρ : ℝ} {p R : ℂ}
    (h : HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) p R) :
    HasResidueAt (contourF y ρ) p (R * gaussE ρ p) :=
  h.mul_continuousAt (continuous_gaussE ρ).continuousAt

theorem ne_conj_of_im_pos {p q : ℂ} (hp : 0 < p.im) (hq : 0 < q.im) : p ≠ (starRingEnd ℂ) q :=
  fun h => by
    have := congrArg Complex.im h
    simp at this; linarith

theorem ne_of_re_ne {a b : ℂ} (h : a.re ≠ b.re) : a ≠ b := fun e => h (by rw [e])

section FPlusResidues

variable {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ)
include hy hy1

omit hy hy1 in
theorem res_fPlus_of {p R K : ℂ} (hR : HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) p R)
    (hK : HasResidueAt (principalK (sigmaC y + 1)) p K) :
    HasResidueAt (fPlus y ρ) p (R * gaussE ρ p - cPlus y ρ * K) :=
  (res_contourF_of hR).sub (hK.const_mul _)

omit hy hy1 in
theorem res_fMinus_of {p R K : ℂ} (hR : HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) p R)
    (hK : HasResidueAt (principalK (sigmaC y - 1)) p K) :
    HasResidueAt (fMinus y ρ) p (R * gaussE ρ p - cMinus y ρ * K) :=
  (res_contourF_of hR).sub (hK.const_mul _)

omit hy1 in
theorem im_sigmaC_pos : 0 < (sigmaC y).im := by rw [im_sigmaC hy]; exact inv_pos.mpr hy

omit hy hy1 in
theorem im_tauC_pos : 0 < ((imagPt y : ℍ) : ℂ).im := (imagPt y).im_pos

/-- `F₊` has removable singularities at all six special points. -/
theorem res_fPlus_special : ∀ p ∈ specialPlus y, HasResidueAt (fPlus y ρ) p 0 := by
  have hσ := im_sigmaC_pos hy
  have hτ := im_tauC_pos (y := y)
  have hp : 0 < (sigmaC y + 1).im := by simpa using hσ
  have hst := sigmaC_mul_tau hy
  have hσ0 : sigmaC y ≠ 0 := fun h => by simp [h] at hσ
  have hzero : ∀ q : ℂ, 0 < q.im → q ≠ sigmaC y + 1 →
      HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) q 0 →
      HasResidueAt (fPlus y ρ) q 0 := by
    intro q hq hne hR
    have h := res_fPlus_of ρ hR (hasResidueAt_principalK_of_ne hne (ne_conj_of_im_pos hq hp))
    simpa using h
  intro q hq
  simp only [specialPlus, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with h | h | h | h | h | h <;> subst h
  · refine hzero _ hτ (ne_of_re_ne ?_) (res_hat_tau hy hy1)
    rw [re_tauC hy]; simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ hσ (ne_of_re_ne ?_) (res_hat_sigma hy hy1)
    simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ (by simpa using hτ) (fun e => tauC_ne_sigmaC hy hy1 (by linear_combination e))
      (res_hat_tau_add_one hy hy1)
  · have h := res_fPlus_of ρ (res_hat_sigma_add_one hy hy1) (hasResidueAt_principalK_self hp)
    have e : sigmaC y ^ 4 / (2 * (π : ℂ)) * gaussE ρ (sigmaC y + 1) - cPlus y ρ * 1 = 0 := by
      simp [cPlus]
    rwa [e] at h
  · have h1 : (1 : ℂ) + sigmaC y ≠ 0 := by rw [add_comm]; exact add_one_ne_zero_of_im_pos hσ
    refine hzero _ (by rw [add_comm]; exact im_div_add_one_pos hσ) (fun e => ?_)
      (res_hat_sigma_semicircle hy hy1)
    rw [div_eq_iff h1] at e
    have := congrArg Complex.im e
    simp [re_imagPt (inv_pos.mpr hy), Complex.mul_im] at this
    have h2 : 0 < (imagPt y⁻¹).im := (imagPt y⁻¹).im_pos
    linarith
  · have h1 : (1 : ℂ) + ((imagPt y : ℍ) : ℂ) ≠ 0 := by
      rw [add_comm]; exact add_one_ne_zero_of_im_pos hτ
    refine hzero _ (by rw [add_comm]; exact im_div_add_one_pos hτ) (fun e => ?_)
      (res_hat_tau_semicircle hy hy1)
    rw [div_eq_iff h1] at e
    apply hσ0
    linear_combination -e - hst

/-- `F₋` has removable singularities at all six special points. -/
theorem res_fMinus_special : ∀ p ∈ specialMinus y, HasResidueAt (fMinus y ρ) p 0 := by
  have hσ := im_sigmaC_pos hy
  have hτ := im_tauC_pos (y := y)
  have hp : 0 < (sigmaC y - 1).im := by simpa using hσ
  have hst := sigmaC_mul_tau hy
  have hσ0 : sigmaC y ≠ 0 := fun h => by simp [h] at hσ
  have hzero : ∀ q : ℂ, 0 < q.im → q ≠ sigmaC y - 1 →
      HasResidueAt (rightC ckmrvEightHatKernel (imagPt y)) q 0 →
      HasResidueAt (fMinus y ρ) q 0 := by
    intro q hq hne hR
    have h := res_fMinus_of ρ hR (hasResidueAt_principalK_of_ne hne (ne_conj_of_im_pos hq hp))
    simpa using h
  intro q hq
  simp only [specialMinus, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with h | h | h | h | h | h <;> subst h
  · refine hzero _ hτ (ne_of_re_ne ?_) (res_hat_tau hy hy1)
    rw [re_tauC hy]; simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ hσ (ne_of_re_ne ?_) (res_hat_sigma hy hy1)
    simp [re_imagPt (inv_pos.mpr hy)]
  · refine hzero _ (by simpa using hτ) (fun e => tauC_ne_sigmaC hy hy1 (by linear_combination e))
      (res_hat_tau_sub_one hy hy1)
  · have h := res_fMinus_of ρ (res_hat_sigma_sub_one hy hy1) (hasResidueAt_principalK_self hp)
    have e : -(sigmaC y ^ 4 / (2 * (π : ℂ))) * gaussE ρ (sigmaC y - 1) - cMinus y ρ * 1 = 0 := by
      simp [cMinus]
    rwa [e] at h
  · have h1 : (1 : ℂ) - ((imagPt y : ℍ) : ℂ) ≠ 0 := one_sub_ne_zero_of_im_pos hτ
    refine hzero _ (im_div_one_sub_pos hτ) (fun e => ?_) (res_hat_tau_semicircle' hy hy1)
    rw [div_eq_iff h1] at e
    apply hσ0
    linear_combination -e + hst
  · have h1 : (1 : ℂ) - sigmaC y ≠ 0 := one_sub_ne_zero_of_im_pos hσ
    refine hzero _ (im_div_one_sub_pos hσ) (fun e => ?_) (res_hat_sigma_semicircle' hy hy1)
    rw [div_eq_iff h1] at e
    have := congrArg Complex.im e
    simp [re_imagPt (inv_pos.mpr hy), Complex.mul_im] at this
    have h2 : 0 < (imagPt y⁻¹).im := (imagPt y⁻¹).im_pos
    linarith

end FPlusResidues

/-! ## Regularity of `F±` off the special points -/

theorem eventually_ne_nhdsWithin_ne (p a : ℂ) : ∀ᶠ z in 𝓝[≠] p, z ≠ a := by
  by_cases h : a = p
  · subst h; exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr
      (Ne.symm h)))

theorem kleinJC_imagPt_eq (y : ℝ) : kleinJC (imagPt y) = kleinModularJ (imagPt y) := by
  rw [kleinJC, UpperHalfPlane.ofComplex_apply]

theorem kleinModularJ_imagPt_ne_1728 {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    kleinModularJ (imagPt y) ≠ 1728 := by
  rw [← kleinImaginaryJ_eq_imagPt]
  intro h
  rcases lt_or_gt_of_ne hy1 with h1 | h1
  · have := kleinImaginaryJ_re_gt_1728 (one_lt_inv₀ hy |>.mpr h1)
    rw [kleinImaginaryJ_inv hy, h] at this
    simp at this
  · have := kleinImaginaryJ_re_gt_1728 h1
    rw [h] at this
    simp at this

theorem kleinModularJ_imagPt_ne_zero' {y : ℝ} (hy : 0 < y) : kleinModularJ (imagPt y) ≠ 0 := by
  rw [← kleinImaginaryJ_eq_imagPt]
  intro h
  have := kleinImaginaryJ_re_ge_1728 hy
  rw [h] at this
  simp at this; linarith

theorem kleinModularJDerivative_ne_zero_of_j {z : ℍ} (h0 : kleinModularJ z ≠ 0)
    (h1728 : kleinModularJ z ≠ 1728) : kleinModularJDerivative z ≠ 0 := by
  refine (kleinModularJDerivative_ne_zero_iff z).mpr ⟨fun h4 => h0 ?_, fun h6 => h1728 ?_⟩
  · rw [kleinModularJ, h4]; simp
  · have := kleinModularJ_sub_1728 z
    rw [h6] at this
    simp at this
    linear_combination this

/-- Near any point of `ℍ`, the punctured neighborhood avoids the `j`-locus of `iy`. -/
theorem eventually_kleinJC_ne_imagPt {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {p : ℂ} (hp : 0 < p.im) :
    ∀ᶠ z in 𝓝[≠] p, kleinJC z ≠ kleinJC (imagPt y) := by
  by_cases h : kleinJC p = kleinJC (imagPt y)
  · have hj : kleinModularJ (ofComplex p) = kleinModularJ (imagPt y) := by
      rw [← kleinJC_imagPt_eq]; exact h
    have h0 : kleinModularJ (ofComplex p) ≠ 0 := by
      rw [hj]; exact kleinModularJ_imagPt_ne_zero' hy
    have h1728 : kleinModularJ (ofComplex p) ≠ 1728 := by
      rw [hj]; exact kleinModularJ_imagPt_ne_1728 hy hy1
    have hd' := kleinModularJDerivative_ne_zero_of_j h0 h1728
    have e : ofComplex p = (⟨p, hp⟩ : ℍ) := ofComplex_apply_of_im_pos hp
    rw [e] at hd'
    have hD := hasDerivAt_kleinJC ⟨p, hp⟩
    have hev := hD.eventually_ne (c := kleinJC (imagPt y)) hd'
    exact hev
  · exact nhdsWithin_le_nhds (eventually_kleinJC_ne_of_ne hp h)

theorem differentiableAt_contourF {y ρ : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) : DifferentiableAt ℂ (contourF y ρ) z :=
  (differentiableAt_rightC_hatKernel (imagPt y) hz hj).mul (differentiable_gaussE ρ z)

theorem differentiableAt_fPlus {y ρ : ℝ} (hy : 0 < y) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) (hz1 : z ≠ sigmaC y + 1) :
    DifferentiableAt ℂ (fPlus y ρ) z := by
  have hp : 0 < (sigmaC y + 1).im := by simpa using im_sigmaC_pos hy
  exact (differentiableAt_contourF hz hj).sub ((differentiableAt_const _).mul
    (differentiableAt_principalK hz1 (ne_conj_of_im_pos hz hp)))

theorem differentiableAt_fMinus {y ρ : ℝ} (hy : 0 < y) {z : ℂ} (hz : 0 < z.im)
    (hj : kleinJC z ≠ kleinJC (imagPt y)) (hz1 : z ≠ sigmaC y - 1) :
    DifferentiableAt ℂ (fMinus y ρ) z := by
  have hp : 0 < (sigmaC y - 1).im := by simpa using im_sigmaC_pos hy
  exact (differentiableAt_contourF hz hj).sub ((differentiableAt_const _).mul
    (differentiableAt_principalK hz1 (ne_conj_of_im_pos hz hp)))

theorem eventually_differentiableAt_fPlus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ) {p : ℂ}
    (hp : 0 < p.im) : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ (fPlus y ρ) z := by
  have hpos : ∀ᶠ z in 𝓝[≠] p, 0 < z.im :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto p).eventually (lt_mem_nhds hp))
  filter_upwards [hpos, eventually_kleinJC_ne_imagPt hy hy1 hp,
    eventually_ne_nhdsWithin_ne p (sigmaC y + 1)] with z hz hj hz1
  exact differentiableAt_fPlus hy hz hj hz1

theorem eventually_differentiableAt_fMinus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ) {p : ℂ}
    (hp : 0 < p.im) : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ (fMinus y ρ) z := by
  have hpos : ∀ᶠ z in 𝓝[≠] p, 0 < z.im :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto p).eventually (lt_mem_nhds hp))
  filter_upwards [hpos, eventually_kleinJC_ne_imagPt hy hy1 hp,
    eventually_ne_nhdsWithin_ne p (sigmaC y - 1)] with z hz hj hz1
  exact differentiableAt_fMinus hy hz hj hz1

/-! ## The corrected functions `G±` -/

theorem im_pos_of_mem_specialPlus {y : ℝ} (hy : 0 < y) :
    ∀ p ∈ specialPlus y, 0 < p.im := by
  have hσ := im_sigmaC_pos hy
  have hτ := im_tauC_pos (y := y)
  intro p hp
  simp only [specialPlus, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h <;> subst h
  · exact hτ
  · exact hσ
  · simpa using hτ
  · simpa using hσ
  · rw [add_comm]; exact im_div_add_one_pos hσ
  · rw [add_comm]; exact im_div_add_one_pos hτ

theorem im_pos_of_mem_specialMinus {y : ℝ} (hy : 0 < y) :
    ∀ p ∈ specialMinus y, 0 < p.im := by
  have hσ := im_sigmaC_pos hy
  have hτ := im_tauC_pos (y := y)
  intro p hp
  simp only [specialMinus, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h <;> subst h
  · exact hτ
  · exact hσ
  · simpa using hτ
  · simpa using hσ
  · exact im_div_one_sub_pos hτ
  · exact im_div_one_sub_pos hσ

theorem neg_one_div_tau_sub_one {y : ℝ} (hy : 0 < y) :
    -1 / (((imagPt y : ℍ) : ℂ) - 1) = sigmaC y / (1 + sigmaC y) := by
  have hst := sigmaC_mul_tau hy
  have h1 : ((imagPt y : ℍ) : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [(imagPt y).im_pos]
  have h2 : 1 + sigmaC y ≠ 0 := by
    rw [add_comm]; exact add_one_ne_zero_of_im_pos (im_sigmaC_pos hy)
  rw [div_eq_div_iff h1 h2]
  linear_combination -hst

theorem neg_one_div_sigma_sub_one {y : ℝ} (hy : 0 < y) :
    -1 / (sigmaC y - 1) = ((imagPt y : ℍ) : ℂ) / (1 + ((imagPt y : ℍ) : ℂ)) := by
  have hst := sigmaC_mul_tau hy
  have h1 : sigmaC y - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [(imagPt y⁻¹).im_pos]
  have h2 : 1 + ((imagPt y : ℍ) : ℂ) ≠ 0 := by
    rw [add_comm]; exact add_one_ne_zero_of_im_pos (imagPt y).im_pos
  rw [div_eq_div_iff h1 h2]
  linear_combination -hst

theorem mem_specialPlus_of_kleinJC {y : ℝ} (hy : 0 < y) {z : ℂ} (hz : z ∈ idealTriangleCl)
    (hj : kleinJC z = kleinJC (imagPt y)) : z ∈ specialPlus y := by
  rcases kleinJC_eq_imagPt_of_mem_cl hy hz hj with h | h | h | h | h | h <;>
    simp only [specialPlus, Finset.mem_insert, Finset.mem_singleton]
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [neg_one_div_tau_sub_one hy] at h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rw [neg_one_div_sigma_sub_one hy] at h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem mem_specialMinus_of_kleinJC {y : ℝ} (hy : 0 < y) {z : ℂ} (hz : z + 1 ∈ idealTriangleCl)
    (hj : kleinJC z = kleinJC (imagPt y)) : z ∈ specialMinus y := by
  have him : 0 < z.im := by simpa using hz.1
  have hj' : kleinJC (z + 1) = kleinJC (imagPt y) := by rw [kleinJC_add_one him]; exact hj
  have hτ1 : ((imagPt y : ℍ) : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [(imagPt y).im_pos]
  have hσ1 : sigmaC y - 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [(imagPt y⁻¹).im_pos]
  have hτ1' : (1 : ℂ) - ((imagPt y : ℍ) : ℂ) ≠ 0 := fun h => hτ1 (by linear_combination -h)
  have hσ1' : (1 : ℂ) - sigmaC y ≠ 0 := fun h => hσ1 (by linear_combination -h)
  rcases kleinJC_eq_imagPt_of_mem_cl hy hz hj' with h | h | h | h | h | h <;>
    simp only [specialMinus, Finset.mem_insert, Finset.mem_singleton]
  · right; right; left; linear_combination h
  · right; right; right; left; linear_combination h
  · left; linear_combination h
  · right; left; linear_combination h
  · right; right; right; right; left
    have e : z = -1 / (((imagPt y : ℍ) : ℂ) - 1) - 1 := by linear_combination h
    rw [e]; field_simp; ring
  · right; right; right; right; right
    have e : z = -1 / (sigmaC y - 1) - 1 := by linear_combination h
    rw [e]; field_simp; ring

theorem exists_gPlus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ) :
    ∃ G : ℂ → ℂ, (∀ z ∈ idealTriangleCl, DifferentiableAt ℂ G z) ∧
      ∀ z, z ∉ specialPlus y → G z = fPlus y ρ z := by
  obtain ⟨G, hG, hGF⟩ := exists_differentiable_update (K := idealTriangleCl) (specialPlus y)
    (fPlus y ρ)
    (fun z hz hzP => by
      have hj : kleinJC z ≠ kleinJC (imagPt y) := fun hj => hzP (mem_specialPlus_of_kleinJC hy hz hj)
      have hz1 : z ≠ sigmaC y + 1 := fun h => hzP (by
        rw [h]; simp [specialPlus])
      exact differentiableAt_fPlus hy hz.1 hj hz1)
    (fun p hp => eventually_differentiableAt_fPlus hy hy1 ρ (im_pos_of_mem_specialPlus hy p hp))
    (res_fPlus_special hy hy1 ρ)
  exact ⟨G, fun z hz => hG z (Or.inl hz), hGF⟩

theorem exists_gMinus {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (ρ : ℝ) :
    ∃ G : ℂ → ℂ, (∀ z, z + 1 ∈ idealTriangleCl → DifferentiableAt ℂ G z) ∧
      ∀ z, z ∉ specialMinus y → G z = fMinus y ρ z := by
  obtain ⟨G, hG, hGF⟩ := exists_differentiable_update (K := {z | z + 1 ∈ idealTriangleCl})
    (specialMinus y) (fMinus y ρ)
    (fun z hz hzP => by
      have hj : kleinJC z ≠ kleinJC (imagPt y) := fun hj =>
        hzP (mem_specialMinus_of_kleinJC hy hz hj)
      have hz1 : z ≠ sigmaC y - 1 := fun h => hzP (by
        rw [h]; simp [specialMinus])
      exact differentiableAt_fMinus hy (by simpa using hz.1) hj hz1)
    (fun p hp => eventually_differentiableAt_fMinus hy hy1 ρ (im_pos_of_mem_specialMinus hy p hp))
    (res_fMinus_special hy hy1 ρ)
  exact ⟨G, fun z hz => hG z (Or.inl hz), hGF⟩

/-! ## Size of the kernel on the closed triangles -/

theorem cl_re_le_normSq {z : ℂ} (hz : z ∈ idealTriangleCl) : z.re ≤ Complex.normSq z := by
  have h2 : (1 / 2 : ℝ) ^ 2 ≤ Complex.normSq (z - 1 / 2) := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (by norm_num) hz.2.2.2 2
  have e : Complex.normSq (z - 1 / 2) = Complex.normSq z - z.re + 1 / 4 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]; simp; ring
  linarith

theorem cl_neg_re_sub_one_le {z : ℂ} (hz : z ∈ idealTriangleCl) :
    -(z - 1).re ≤ Complex.normSq (z - 1) := by
  have h := cl_re_le_normSq hz
  have e : Complex.normSq (z - 1) = Complex.normSq z - 2 * z.re + 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply]; simp; ring
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem one_div_two_mul_ge {V x : ℝ} (hV : 0 < V) (hx : 0 < x) (h : x ≤ 1 / (2 * V)) :
    V ≤ 1 / (2 * x) := by
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

theorem im_le_norm_of_pos {z : ℂ} (hz : 0 < z.im) : z.im ≤ ‖z‖ := by
  have := Complex.abs_im_le_norm z
  rwa [abs_of_pos hz] at this

theorem im_neg_one_div_le {u : ℂ} (hu : 0 < u.im) : (-1 / u).im ≤ 1 / ‖u‖ := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have him : (-1 / u).im = u.im / ‖u‖ ^ 2 := by
    rw [Complex.div_im]; norm_num; rw [Complex.normSq_eq_norm_sq]; ring
  rw [him, div_le_div_iff₀ (by positivity) hn]
  have := im_le_norm_of_pos hu
  nlinarith

theorem div_one_sub_eq_neg_one_add {z : ℂ} (h : z - 1 ≠ 0) :
    z / (1 - z) = -1 + -1 / (z - 1) := by
  have h' : (1 : ℂ) - z ≠ 0 := by
    rw [← neg_sub]; exact neg_ne_zero.mpr h
  field_simp
  ring

/-- `𝒦̂(τ, ·)` is bounded near the cusp `0` of `(0, 1, ∞)`. -/
theorem exists_bound_hat_cusp0 (τ : ℍ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ →
      ‖rightC ckmrvEightHatKernel τ z‖ ≤ M := by
  obtain ⟨C, V, _, hV1, hb⟩ := exists_bound_hatKernel_S τ
  have hV : 0 < V := by linarith
  refine ⟨1 / (2 * V), C, by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith,
    fun z hz hzn => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by simp [h, idealTriangleCl] at hz
  have hsmall : ‖z‖ ≤ 1 / 2 := hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hh := horn_zero_bounds hz.1 hz.2.1 (cl_re_le_normSq hz) hsmall
  have hIm : V ≤ (-1 / z).im := (one_div_two_mul_ge hV hz0 hzn).trans hh.2
  have hw : 0 < (-1 / z).im := lt_of_lt_of_le hV hIm
  have e : rightC ckmrvEightHatKernel τ z =
      ckmrvEightHatKernel τ (ModularGroup.S • (⟨-1 / z, hw⟩ : ℍ)) := by
    simp only [rightC]
    rw [← ofComplex_neg_inv hz.1, ofComplex_apply_of_im_pos hw]
  rw [e]
  exact (hb ⟨-1 / z, hw⟩ hIm).1

/-- `𝒦̂(τ, ·)` is bounded near the cusp `1` of `(0, 1, ∞)` (through `𝒦̂ = 𝒦 |_{−2} STS`). -/
theorem exists_bound_hat_cusp1 (τ : ℍ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ →
      ‖rightC ckmrvEightHatKernel τ z‖ ≤ M := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_hatKernel_top τ (R := 1) zero_le_one
  set W := max V 1
  have hW : 0 < W := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / (2 * W), C, by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1],
    fun z hz hzn => ?_⟩
  set u := z - 1 with hu
  have huim : 0 < u.im := by simpa [hu] using hz.1
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr fun h => by simp [h] at huim
  have hsmall : ‖u‖ ≤ 1 / 2 := hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1])
  have hure : u.re ≤ 0 := by simp [hu]; linarith [hz.2.2.1]
  have hh := horn_one_bounds huim hure (cl_neg_re_sub_one_le hz) hsmall
  have hIm : W ≤ (-1 / u).im := (one_div_two_mul_ge hW hu0 hzn).trans hh.2
  have hu1 : u ≠ 0 := fun h => by simp [h] at huim
  have hw : z / (1 - z) = -1 + -1 / u := div_one_sub_eq_neg_one_add hu1
  have hwim : (z / (1 - z)).im = (-1 / u).im := by rw [hw]; simp
  have hwre : |(z / (1 - z)).re| ≤ 1 := by
    rw [hw, Complex.add_re, abs_le]; simp only [Complex.neg_re, Complex.one_re]
    constructor <;> linarith [hh.1.1, hh.1.2]
  have hwpos : 0 < (z / (1 - z)).im := by rw [hwim]; linarith [le_max_right V 1]
  have hb' := (hb ⟨z / (1 - z), hwpos⟩ (by
    show V ≤ (z / (1 - z)).im
    rw [hwim]; exact le_trans (le_max_left _ _) hIm) hwre).2
  rw [rightC_hat_eq_STS hz.1]
  have e : rightC ckmrvEightKernel τ (z / (1 - z)) = ckmrvEightKernel τ ⟨z / (1 - z), hwpos⟩ := by
    simp only [rightC]; rw [ofComplex_apply_of_im_pos hwpos]
  rw [e, norm_mul, norm_pow]
  have hkey : (⟨z / (1 - z), hwpos⟩ : ℍ).im ≤ 1 / ‖u‖ := by
    show (z / (1 - z)).im ≤ 1 / ‖u‖
    rw [hwim]; exact im_neg_one_div_le huim
  calc ‖z - 1‖ ^ 2 * ‖ckmrvEightKernel τ ⟨z / (1 - z), hwpos⟩‖
      ≤ ‖u‖ ^ 2 * (C * (1 + 1 / ‖u‖)) := by
        rw [← hu]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hb'.trans (by gcongr)
    _ = C * (‖u‖ ^ 2 + ‖u‖) := by field_simp
    _ ≤ C * 1 := by gcongr; nlinarith
    _ = C := mul_one C

/-- `𝒦̂(τ, ·)` is bounded near `−1` on the closed triangle `(−1, 0, ∞)`. -/
theorem exists_bound_hat_shift_cusp0 (τ : ℍ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ →
      ‖rightC ckmrvEightHatKernel τ (z - 1)‖ ≤ M := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_hatKernel_top τ (R := 1) zero_le_one
  set W := max V 1
  have hW : 0 < W := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / (2 * W), C, by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1],
    fun z hz hzn => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by simp [h, idealTriangleCl] at hz
  have hsmall : ‖z‖ ≤ 1 / 2 := hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith [le_max_right V 1])
  have hh := horn_zero_bounds hz.1 hz.2.1 (cl_re_le_normSq hz) hsmall
  have hIm : W ≤ (-1 / z).im := (one_div_two_mul_ge hW hz0 hzn).trans hh.2
  have huim : 0 < (z - 1).im := by simpa using hz.1
  have hz00 : z ≠ 0 := fun h => by simp [h] at hz0
  have hw : (z - 1) / (z - 1 + 1) = 1 + -1 / z := by
    rw [sub_add_cancel]; field_simp; ring
  have hwim : ((z - 1) / (z - 1 + 1)).im = (-1 / z).im := by rw [hw]; simp
  have hwre : |((z - 1) / (z - 1 + 1)).re| ≤ 1 := by
    rw [hw, Complex.add_re, abs_le]; simp only [Complex.one_re]
    constructor <;> linarith [hh.1.1, hh.1.2]
  have hwpos : 0 < ((z - 1) / (z - 1 + 1)).im := by rw [hwim]; linarith [le_max_right V 1]
  have hb' := (hb ⟨(z - 1) / (z - 1 + 1), hwpos⟩ (by
    show V ≤ ((z - 1) / (z - 1 + 1)).im
    rw [hwim]; exact le_trans (le_max_left _ _) hIm) hwre).2
  rw [rightC_hat_eq_TST huim]
  have e : rightC ckmrvEightKernel τ ((z - 1) / (z - 1 + 1)) =
      ckmrvEightKernel τ ⟨(z - 1) / (z - 1 + 1), hwpos⟩ := by
    simp only [rightC]; rw [ofComplex_apply_of_im_pos hwpos]
  rw [e, norm_mul, norm_pow, show ‖z - 1 + 1‖ = ‖z‖ by rw [sub_add_cancel]]
  have hkey : (⟨(z - 1) / (z - 1 + 1), hwpos⟩ : ℍ).im ≤ 1 / ‖z‖ := by
    show ((z - 1) / (z - 1 + 1)).im ≤ 1 / ‖z‖
    rw [hwim]; exact im_neg_one_div_le hz.1
  calc ‖z‖ ^ 2 * ‖ckmrvEightKernel τ ⟨(z - 1) / (z - 1 + 1), hwpos⟩‖
      ≤ ‖z‖ ^ 2 * (C * (1 + 1 / ‖z‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hb'.trans (by gcongr)
    _ = C * (‖z‖ ^ 2 + ‖z‖) := by field_simp
    _ ≤ C * 1 := by gcongr; nlinarith
    _ = C := mul_one C

/-- `𝒦̂(τ, ·)` is bounded near `0` on the closed triangle `(−1, 0, ∞)`. -/
theorem exists_bound_hat_shift_cusp1 (τ : ℍ) :
    ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ →
      ‖rightC ckmrvEightHatKernel τ (z - 1)‖ ≤ M := by
  obtain ⟨C, V, _, hV1, hb⟩ := exists_bound_hatKernel_S τ
  have hV : 0 < V := by linarith
  refine ⟨1 / (2 * V), C, by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith,
    fun z hz hzn => ?_⟩
  set u := z - 1 with hu
  have huim : 0 < u.im := by simpa [hu] using hz.1
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr fun h => by simp [h] at huim
  have hsmall : ‖u‖ ≤ 1 / 2 := hzn.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hure : u.re ≤ 0 := by simp [hu]; linarith [hz.2.2.1]
  have hh := horn_one_bounds huim hure (cl_neg_re_sub_one_le hz) hsmall
  have hIm : V ≤ (-1 / u).im := (one_div_two_mul_ge hV hu0 hzn).trans hh.2
  have hw : 0 < (-1 / u).im := lt_of_lt_of_le hV hIm
  have e : rightC ckmrvEightHatKernel τ u =
      ckmrvEightHatKernel τ (ModularGroup.S • (⟨-1 / u, hw⟩ : ℍ)) := by
    simp only [rightC]
    rw [← ofComplex_neg_inv huim, ofComplex_apply_of_im_pos hw]
  rw [e]
  exact (hb ⟨-1 / u, hw⟩ hIm).1

end E8Leech
