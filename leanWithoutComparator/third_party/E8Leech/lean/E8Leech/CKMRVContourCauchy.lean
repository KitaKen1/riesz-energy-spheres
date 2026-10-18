import E8Leech.CKMRVContourIdentity

/-!
# Cauchy's theorem for `F± = f − c± k±` on the ideal triangles

The corrected function `G₊` (equal to `f − c₊k₊` off finitely many points) on `(0, 1, ∞)`, and
`G₋(· − 1)` (from `f − c₋k₋`) on the same triangle, are `O((1 + Im z)⁻²)` on the closed triangle:
the kernel grows linearly at `i∞` against the decay `e^{−πρ Im z}`, it is bounded at the cusps, and
the principal parts are explicit. Hence `idealTriangle_cauchy` applies to both.
-/

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Finite sets of points in the upper half-plane -/

theorem exists_im_bounds_of_finset (P : Finset ℂ) (hP : ∀ p ∈ P, 0 < p.im) :
    ∃ a b : ℝ, 0 < a ∧ ∀ p ∈ P, a ≤ p.im ∧ p.im ≤ b := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, 0, one_pos, by simp⟩
  | @insert q P hq ih =>
    obtain ⟨a, b, ha, hab⟩ := ih fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hq0 := hP q (Finset.mem_insert_self q P)
    refine ⟨min a q.im, max b q.im, lt_min ha hq0, fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨(min_le_left _ _).trans (hab p hp).1, (hab p hp).2.trans (le_max_left _ _)⟩

theorem not_mem_of_im_lt {P : Finset ℂ} {a : ℝ} (h : ∀ p ∈ P, a ≤ p.im) {z : ℂ}
    (hz : z.im < a) : z ∉ P := fun hm => absurd (h z hm) (not_le.mpr hz)

theorem not_mem_of_lt_im {P : Finset ℂ} {b : ℝ} (h : ∀ p ∈ P, p.im ≤ b) {z : ℂ}
    (hz : b < z.im) : z ∉ P := fun hm => absurd (h z hm) (not_le.mpr hz)

/-! ## The principal parts -/

theorem principalK_eq {p z : ℂ} (h1 : z - p ≠ 0) (h2 : z - (starRingEnd ℂ) p ≠ 0) :
    principalK p z = (2 * p.im * I) / ((z - p) * (z - (starRingEnd ℂ) p)) := by
  have e : p - (starRingEnd ℂ) p = 2 * p.im * I := by
    apply Complex.ext <;> simp; ring
  rw [principalK, div_sub_div _ _ h1 h2, ← e]
  congr 1
  ring

theorem norm_principalK_le {p z : ℂ} (hp : 0 < p.im) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hzp : A ≤ |z.im - p.im|) (hzq : B ≤ z.im + p.im) :
    ‖principalK p z‖ ≤ 2 * p.im / (A * B) := by
  have h1' : A ≤ ‖z - p‖ := hzp.trans (by
    have := Complex.abs_im_le_norm (z - p)
    simpa using this)
  have h2' : B ≤ ‖z - (starRingEnd ℂ) p‖ := hzq.trans (by
    have := Complex.abs_im_le_norm (z - (starRingEnd ℂ) p)
    simp at this
    exact (le_abs_self _).trans this)
  have h1 : z - p ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hA h1')
  have h2 : z - (starRingEnd ℂ) p ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hB h2')
  have hn : ‖(2 * (p.im : ℂ) * I)‖ = 2 * p.im := by simp [abs_of_pos hp]
  rw [principalK_eq h1 h2, norm_div, hn, norm_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul h1' h2' hB.le (norm_nonneg _))

theorem norm_principalK_le_top {p z : ℂ} (hp : 0 < p.im) (hz1 : 1 ≤ z.im)
    (hz2 : 2 * p.im ≤ z.im) : ‖principalK p z‖ ≤ 16 * p.im / (1 + z.im) ^ 2 := by
  have hz0 : 0 < z.im := by linarith
  have h := norm_principalK_le hp (A := z.im / 2) (B := z.im) (by positivity) hz0
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by linarith)
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : (1 + z.im) ^ 2 ≤ 4 * z.im ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * p.im)
  nlinarith

theorem norm_principalK_le_low {p z : ℂ} (hp : 0 < p.im) (hz0 : 0 < z.im)
    (hz : z.im ≤ p.im / 2) : ‖principalK p z‖ ≤ 4 / p.im := by
  have h := norm_principalK_le hp (A := p.im / 2) (B := p.im) (by positivity) hp
    (by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith) (by linarith)
  refine h.trans (le_of_eq ?_)
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-! ## Polynomial growth against exponential decay -/

theorem exists_pow_three_mul_exp_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 0 ≤ v → (1 + v) ^ 3 * Real.exp (-(c * v)) ≤ K := by
  refine ⟨4 * (1 + 6 / c ^ 3), by positivity, fun v hv => ?_⟩
  have hcube : (1 + v) ^ 3 ≤ 4 * (1 + v ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (1 - v)) (by linarith : (0 : ℝ) ≤ 1 + v)]
  have h1 : 1 ≤ Real.exp (c * v) := Real.one_le_exp (by positivity)
  have h6 : (c * v) ^ 3 / ((Nat.factorial 3 : ℕ) : ℝ) ≤ Real.exp (c * v) :=
    Real.pow_div_factorial_le_exp (c * v) (by positivity) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h6
  have hv3 : v ^ 3 ≤ 6 / c ^ 3 * Real.exp (c * v) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e3 : (c * v) ^ 3 = v ^ 3 * c ^ 3 := by ring
    rw [e3] at h6
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [hcube, h1, hv3]

/-! ## Size of `f = 𝒦̂(iy, ·) E` -/

theorem norm_contourF (y ρ : ℝ) (z : ℂ) :
    ‖contourF y ρ z‖ =
      ‖rightC ckmrvEightHatKernel (imagPt y) z‖ * Real.exp (-(π * ρ) * z.im) := by
  rw [contourF, norm_mul, norm_gaussE]

theorem exists_bound_contourF_top (y : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ M V : ℝ, ∀ z : ℂ, 0 < z.im → |z.re| ≤ 1 → V ≤ z.im →
      ‖contourF y ρ z‖ ≤ M / (1 + z.im) ^ 2 := by
  obtain ⟨C, V, hC, hb⟩ := exists_bound_hatKernel_top (imagPt y) (R := 1) zero_le_one
  obtain ⟨K, hK, hKb⟩ := exists_pow_three_mul_exp_le (c := π * ρ) (by positivity)
  refine ⟨C * K, V, fun z hz hre hV => ?_⟩
  have hk := (hb ⟨z, hz⟩ hV hre).1
  have e : rightC ckmrvEightHatKernel (imagPt y) z = ckmrvEightHatKernel (imagPt y) ⟨z, hz⟩ := by
    simp only [rightC]; rw [ofComplex_apply_of_im_pos hz]
  rw [norm_contourF, e]
  have hv := hKb z.im hz.le
  have hpos : 0 < (1 + z.im) ^ 2 := by positivity
  have hexp : Real.exp (-(π * ρ) * z.im) = Real.exp (-(π * ρ * z.im)) := by ring_nf
  rw [le_div_iff₀ hpos, hexp]
  calc ‖ckmrvEightHatKernel (imagPt y) ⟨z, hz⟩‖ * Real.exp (-(π * ρ * z.im)) * (1 + z.im) ^ 2
      ≤ C * (1 + z.im) * Real.exp (-(π * ρ * z.im)) * (1 + z.im) ^ 2 := by gcongr; exact hk
    _ = C * ((1 + z.im) ^ 3 * Real.exp (-(π * ρ * z.im))) := by ring
    _ ≤ C * K := by gcongr

theorem norm_contourF_le_of {y ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : 0 < z.im) {M : ℝ}
    (h : ‖rightC ckmrvEightHatKernel (imagPt y) z‖ ≤ M) : ‖contourF y ρ z‖ ≤ M := by
  rw [norm_contourF]
  have h0 : 0 ≤ π * ρ * z.im := by positivity
  have he : Real.exp (-(π * ρ) * z.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact (mul_le_mul h he (Real.exp_pos _).le ((norm_nonneg _).trans h)).trans (le_of_eq (mul_one M))

theorem im_le_norm_sub_one {z : ℂ} : z.im ≤ ‖z - 1‖ := by
  have h := Complex.abs_im_le_norm (z - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
  exact (le_abs_self _).trans h

theorem im_le_norm' {z : ℂ} : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)

theorem norm_sub_mul_le (a c k : ℂ) : ‖a - c * k‖ ≤ ‖a‖ + ‖c‖ * ‖k‖ := by
  rw [← norm_mul]; exact norm_sub_le _ _

/-! ## The bound `|G| ≤ C/(1 + Im z)²` -/

theorem exists_bound_gPlus {y : ℝ} (hy : 0 < y) {ρ : ℝ} (hρ : 0 < ρ) {G : ℂ → ℂ}
    (hGc : ContinuousOn G idealTriangleCl) (hGF : ∀ z, z ∉ specialPlus y → G z = fPlus y ρ z) :
    ∃ C, ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2 := by
  obtain ⟨a, b, ha, hab⟩ := exists_im_bounds_of_finset (specialPlus y) (im_pos_of_mem_specialPlus hy)
  have hpS : sigmaC y + 1 ∈ specialPlus y := by simp [specialPlus]
  have hpim : 0 < (sigmaC y + 1).im := im_pos_of_mem_specialPlus hy _ hpS
  have hap : a ≤ (sigmaC y + 1).im := (hab _ hpS).1
  obtain ⟨M, V, hMV⟩ := exists_bound_contourF_top y hρ
  obtain ⟨δ₀, M₀, hδ₀, -, hM₀⟩ := exists_bound_hat_cusp0 (imagPt y)
  obtain ⟨δ₁, M₁, hδ₁, -, hM₁⟩ := exists_bound_hat_cusp1 (imagPt y)
  set c := cPlus y ρ
  refine idealTriangle_bound_of_pieces hGc (V := max (max V (b + 1)) (max 1 (2 * (sigmaC y + 1).im)))
    (M := M + ‖c‖ * (16 * (sigmaC y + 1).im)) (δ₀ := min δ₀ (a / 2)) (δ₁ := min δ₁ (a / 2))
    (M₀ := M₀ + ‖c‖ * (4 / (sigmaC y + 1).im)) (M₁ := M₁ + ‖c‖ * (4 / (sigmaC y + 1).im))
    (lt_min hδ₀ (by positivity)) (lt_min hδ₁ (by positivity)) ?_ ?_ ?_
  · intro z hz hV
    simp only [max_le_iff] at hV
    obtain ⟨⟨hV1, hV2⟩, hV3, hV4⟩ := hV
    rw [hGF z (not_mem_of_lt_im (fun q hq => (hab q hq).2) (by linarith)), fPlus]
    have h1 := hMV z hz.1 (by rw [abs_le]; constructor <;> linarith [hz.2.1, hz.2.2.1]) hV1
    have h2 := norm_principalK_le_top hpim hV3 hV4
    calc _ ≤ ‖contourF y ρ z‖ + ‖c‖ * ‖principalK (sigmaC y + 1) z‖ := norm_sub_mul_le _ _ _
      _ ≤ M / (1 + z.im) ^ 2 + ‖c‖ * (16 * (sigmaC y + 1).im / (1 + z.im) ^ 2) := by gcongr
      _ = (M + ‖c‖ * (16 * (sigmaC y + 1).im)) / (1 + z.im) ^ 2 := by ring
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm'.trans (hzn.trans (min_le_right _ _))
    rw [hGF z (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by linarith)), fPlus]
    have h1 := norm_contourF_le_of hρ.le hz.1 (hM₀ z hz (hzn.trans (min_le_left _ _)))
    have h2 := norm_principalK_le_low hpim hz.1 (by linarith)
    calc _ ≤ ‖contourF y ρ z‖ + ‖c‖ * ‖principalK (sigmaC y + 1) z‖ := norm_sub_mul_le _ _ _
      _ ≤ M₀ + ‖c‖ * (4 / (sigmaC y + 1).im) := by gcongr
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm_sub_one.trans (hzn.trans (min_le_right _ _))
    rw [hGF z (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by linarith)), fPlus]
    have h1 := norm_contourF_le_of hρ.le hz.1 (hM₁ z hz (hzn.trans (min_le_left _ _)))
    have h2 := norm_principalK_le_low hpim hz.1 (by linarith)
    calc _ ≤ ‖contourF y ρ z‖ + ‖c‖ * ‖principalK (sigmaC y + 1) z‖ := norm_sub_mul_le _ _ _
      _ ≤ M₁ + ‖c‖ * (4 / (sigmaC y + 1).im) := by gcongr

theorem exists_bound_gMinus {y : ℝ} (hy : 0 < y) {ρ : ℝ} (hρ : 0 < ρ) {G : ℂ → ℂ}
    (hGc : ContinuousOn (fun z => G (z - 1)) idealTriangleCl)
    (hGF : ∀ z, z ∉ specialMinus y → G z = fMinus y ρ z) :
    ∃ C, ∀ z ∈ idealTriangleCl, ‖G (z - 1)‖ ≤ C / (1 + z.im) ^ 2 := by
  obtain ⟨a, b, ha, hab⟩ :=
    exists_im_bounds_of_finset (specialMinus y) (im_pos_of_mem_specialMinus hy)
  have hpS : sigmaC y - 1 ∈ specialMinus y := by simp [specialMinus]
  have hpim : 0 < (sigmaC y - 1).im := im_pos_of_mem_specialMinus hy _ hpS
  have hap : a ≤ (sigmaC y - 1).im := (hab _ hpS).1
  obtain ⟨M, V, hMV⟩ := exists_bound_contourF_top y hρ
  obtain ⟨δ₀, M₀, hδ₀, -, hM₀⟩ := exists_bound_hat_shift_cusp0 (imagPt y)
  obtain ⟨δ₁, M₁, hδ₁, -, hM₁⟩ := exists_bound_hat_shift_cusp1 (imagPt y)
  set c := cMinus y ρ
  have him : ∀ z : ℂ, (z - 1).im = z.im := fun z => by simp
  refine idealTriangle_bound_of_pieces hGc (V := max (max V (b + 1)) (max 1 (2 * (sigmaC y - 1).im)))
    (M := M + ‖c‖ * (16 * (sigmaC y - 1).im)) (δ₀ := min δ₀ (a / 2)) (δ₁ := min δ₁ (a / 2))
    (M₀ := M₀ + ‖c‖ * (4 / (sigmaC y - 1).im)) (M₁ := M₁ + ‖c‖ * (4 / (sigmaC y - 1).im))
    (lt_min hδ₀ (by positivity)) (lt_min hδ₁ (by positivity)) ?_ ?_ ?_
  · intro z hz hV
    simp only [max_le_iff] at hV
    obtain ⟨⟨hV1, hV2⟩, hV3, hV4⟩ := hV
    rw [hGF (z - 1) (not_mem_of_lt_im (fun q hq => (hab q hq).2) (by rw [him z]; linarith)), fMinus]
    have h1 := hMV (z - 1) (by rw [him z]; exact hz.1)
      (by rw [abs_le]; simp only [Complex.sub_re, Complex.one_re]; constructor <;>
        linarith [hz.2.1, hz.2.2.1]) (by rw [him z]; exact hV1)
    have h2 := norm_principalK_le_top hpim (z := z - 1) (by rw [him z]; exact hV3) (by rw [him z]; exact hV4)
    rw [him z] at h1 h2
    calc _ ≤ ‖contourF y ρ (z - 1)‖ + ‖c‖ * ‖principalK (sigmaC y - 1) (z - 1)‖ :=
          norm_sub_mul_le _ _ _
      _ ≤ M / (1 + z.im) ^ 2 + ‖c‖ * (16 * (sigmaC y - 1).im / (1 + z.im) ^ 2) := by gcongr
      _ = (M + ‖c‖ * (16 * (sigmaC y - 1).im)) / (1 + z.im) ^ 2 := by ring
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm'.trans (hzn.trans (min_le_right _ _))
    rw [hGF (z - 1) (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by rw [him z]; linarith)), fMinus]
    have h1 := norm_contourF_le_of hρ.le (z := z - 1) (by rw [him z]; exact hz.1)
      (hM₀ z hz (hzn.trans (min_le_left _ _)))
    have h2 := norm_principalK_le_low hpim (z := z - 1) (by rw [him z]; exact hz.1)
      (by rw [him z]; linarith)
    calc _ ≤ ‖contourF y ρ (z - 1)‖ + ‖c‖ * ‖principalK (sigmaC y - 1) (z - 1)‖ :=
          norm_sub_mul_le _ _ _
      _ ≤ M₀ + ‖c‖ * (4 / (sigmaC y - 1).im) := by gcongr
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm_sub_one.trans (hzn.trans (min_le_right _ _))
    rw [hGF (z - 1) (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by rw [him z]; linarith)), fMinus]
    have h1 := norm_contourF_le_of hρ.le (z := z - 1) (by rw [him z]; exact hz.1)
      (hM₁ z hz (hzn.trans (min_le_left _ _)))
    have h2 := norm_principalK_le_low hpim (z := z - 1) (by rw [him z]; exact hz.1)
      (by rw [him z]; linarith)
    calc _ ≤ ‖contourF y ρ (z - 1)‖ + ‖c‖ * ‖principalK (sigmaC y - 1) (z - 1)‖ :=
          norm_sub_mul_le _ _ _
      _ ≤ M₁ + ‖c‖ * (4 / (sigmaC y - 1).im) := by gcongr

/-! ## Cauchy's theorem for `G₊` and `G₋(· − 1)` -/

theorem idealTriangle_subset_cl : idealTriangle ⊆ idealTriangleCl := fun _ hz =>
  ⟨hz.1, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

/-- **Cauchy for `F₊` on `(0, 1, ∞)`.** -/
theorem exists_gPlus_cauchy {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : ℂ → ℂ, (∀ z, z ∉ specialPlus y → G z = fPlus y ρ z) ∧
      ContinuousOn G idealTriangleCl ∧
      (∃ C, ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2) ∧
      (∫ t in Ioi (0 : ℝ), I * G (1 + I * t)) - (∫ t in Ioi (0 : ℝ), I * G (I * t)) =
        ∫ θ in (0 : ℝ)..π, semicircleIntegrand G θ := by
  obtain ⟨G, hGd, hGF⟩ := exists_gPlus hy hy1 ρ
  have hGc : ContinuousOn G idealTriangleCl := fun z hz =>
    (hGd z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := exists_bound_gPlus hy hρ hGc hGF
  exact ⟨G, hGF, hGc, ⟨C, hC⟩, idealTriangle_cauchy
    (fun z hz => (hGd z (idealTriangle_subset_cl hz)).differentiableWithinAt) hGc hC⟩

/-- **Cauchy for `F₋` on `(−1, 0, ∞)`** (translated to `(0, 1, ∞)`). -/
theorem exists_gMinus_cauchy {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ G : ℂ → ℂ, (∀ z, z ∉ specialMinus y → G z = fMinus y ρ z) ∧
      ContinuousOn (fun z => G (z - 1)) idealTriangleCl ∧
      (∃ C, ∀ z ∈ idealTriangleCl, ‖G (z - 1)‖ ≤ C / (1 + z.im) ^ 2) ∧
      (∫ t in Ioi (0 : ℝ), I * G (I * t)) - (∫ t in Ioi (0 : ℝ), I * G (I * t - 1)) =
        ∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => G (z - 1)) θ := by
  obtain ⟨G, hGd, hGF⟩ := exists_gMinus hy hy1 ρ
  have hHd : ∀ z ∈ idealTriangleCl, DifferentiableAt ℂ (fun z => G (z - 1)) z := fun z hz =>
    (hGd (z - 1) (by simpa using hz)).comp z (differentiableAt_fun_id.sub_const 1)
  have hHc : ContinuousOn (fun z => G (z - 1)) idealTriangleCl := fun z hz =>
    (hHd z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := exists_bound_gMinus hy hρ hHc hGF
  have h := idealTriangle_cauchy (g := fun z => G (z - 1))
    (fun z hz => (hHd z (idealTriangle_subset_cl hz)).differentiableWithinAt) hHc hC
  refine ⟨G, hGF, hHc, ⟨C, hC⟩, ?_⟩
  simp only [add_sub_cancel_left] at h
  exact h

end E8Leech
