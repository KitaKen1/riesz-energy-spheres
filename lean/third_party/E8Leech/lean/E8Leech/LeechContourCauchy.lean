import E8Leech.LeechContourIdentity

/-!
# Cauchy's theorem for the integrands `F±` in dimension 24

For `ρ > 2` the corrected functions `G±` of `LeechContourIdentity` are `O((1 + Im z)⁻²)` on the
closed triangles:

* at `i∞`: `𝒦̂ = O((1 + Im z) e^{2π Im z})` against `E = e^{−πρ Im z}`, and the cusp parts grow
  polynomially;
* at the cusp where the subtracted cusp part lives (`1` for `F₊`, `−1` for `F₋`):
  `(𝒦̂ − P₁)(z) = (z − 1)¹⁰ (𝒦 − f)(z/(1 − z))` and `𝒦 − f` grows only linearly
  (`exists_bound_leech_cusp1`, `exists_bound_leech_shift_cusp0`);
* at the other cusp `𝒦̂` and the cusp part are both bounded.

Hence `idealTriangle_cauchy` applies (`exists_leechGPlus_cauchy`, `exists_leechGMinus_cauchy`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set MeasureTheory
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## `F±` through the right relation two -/

theorem norm_gaussE_le_one {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : 0 < z.im) : ‖gaussE ρ z‖ ≤ 1 := by
  rw [norm_gaussE]
  exact Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hρ) hz.le])

theorem leechPlusF_eq_STS {y ρ : ℝ} {z : ℂ} (hz : 0 < z.im) :
    leechPlusF y ρ z = (z - 1) ^ 10 * (rightC ckmrvLeechKernel (imagPt y) (z / (1 - z)) -
      growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * (z / (1 - z)))) * gaussE ρ z := by
  rw [leechPlusF, rightC_leechHat_eq_STS hz, cuspPartPlus]
  ring

theorem leechMinusF_eq_TST {y ρ : ℝ} {u : ℂ} (hu : 0 < u.im) :
    leechMinusF y ρ u = (u + 1) ^ 10 * (rightC ckmrvLeechKernel (imagPt y) (u / (u + 1)) -
      growthC (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (-I * (u / (u + 1)))) * gaussE ρ u := by
  rw [leechMinusF, rightC_leechHat_eq_TST hu, cuspPartMinus]
  ring

/-! ## Size of `(𝒦̂ − P_{±1}) E` -/

theorem exists_bound_leechPlusF_top (y : ℝ) {ρ : ℝ} (hρ : 2 < ρ) :
    ∃ M V : ℝ, ∀ z : ℂ, 0 < z.im → 0 ≤ z.re → z.re ≤ 1 → V ≤ z.im →
      ‖leechPlusF y ρ z‖ ≤ M / (1 + z.im) ^ 2 := by
  obtain ⟨M₁, V, h₁⟩ := exists_bound_leechHatF_top y hρ
  obtain ⟨M₂, h₂⟩ := exists_bound_cuspPartPlus_top (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1)
    (ρ := ρ) (by linarith)
  refine ⟨M₁ + M₂, max V 1, fun z hz h0 h1 hV => ?_⟩
  rw [leechPlusF_eq, add_div]
  exact (norm_sub_le _ _).trans (add_le_add
    (h₁ z hz (abs_le.mpr ⟨by linarith, h1⟩) ((le_max_left _ _).trans hV))
    (h₂ z ((le_max_right _ _).trans hV) h0 h1))

theorem exists_bound_leechMinusF_top (y : ℝ) {ρ : ℝ} (hρ : 2 < ρ) :
    ∃ M V : ℝ, ∀ z : ℂ, 0 < z.im → -1 ≤ z.re → z.re ≤ 0 → V ≤ z.im →
      ‖leechMinusF y ρ z‖ ≤ M / (1 + z.im) ^ 2 := by
  obtain ⟨M₁, V, h₁⟩ := exists_bound_leechHatF_top y hρ
  obtain ⟨M₂, h₂⟩ := exists_bound_cuspPartMinus_top (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1)
    (ρ := ρ) (by linarith)
  refine ⟨M₁ + M₂, max V 1, fun z hz h0 h1 hV => ?_⟩
  rw [leechMinusF_eq, add_div]
  exact (norm_sub_le _ _).trans (add_le_add
    (h₁ z hz (abs_le.mpr ⟨h0, by linarith⟩) ((le_max_left _ _).trans hV))
    (h₂ z ((le_max_right _ _).trans hV) h0 h1))

theorem exists_bound_leechPlusF_cusp0 (y : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ → ‖leechPlusF y ρ z‖ ≤ M := by
  obtain ⟨δ, M, hδ, hδ2, hM⟩ := exists_bound_leechHat_cusp0 (imagPt y)
  refine ⟨δ, M + (3 / 2) ^ 10 * (Real.exp (2 * π * 1) *
    (‖leechAxisCusp 1 y 0‖ * 1 + ‖leechAxisCusp 1 y 1‖)), hδ, fun z hz hzn => ?_⟩
  have h1 := hM z hz hzn
  have h2 := norm_cuspPartPlus_le_of_norm_le (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1)
    (hzn.trans hδ2)
  have h3 := (norm_sub_le (rightC ckmrvLeechHatKernel (imagPt y) z)
    (cuspPartPlus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) z)).trans (add_le_add h1 h2)
  rw [leechPlusF, norm_mul]
  exact (mul_le_mul h3 (norm_gaussE_le_one hρ hz.1) (norm_nonneg _)
    ((norm_nonneg _).trans h3)).trans_eq (mul_one _)

theorem exists_bound_leechPlusF_cusp1 (y : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ → ‖leechPlusF y ρ z‖ ≤ M := by
  obtain ⟨δ, M, hδ, -, hM⟩ := exists_bound_leech_cusp1 y
  refine ⟨δ, M, hδ, fun z hz hzn => ?_⟩
  have h := hM z hz hzn
  rw [leechPlusF_eq_STS hz.1, norm_mul]
  exact (mul_le_mul h (norm_gaussE_le_one hρ hz.1) (norm_nonneg _)
    ((norm_nonneg _).trans h)).trans_eq (mul_one _)

theorem exists_bound_leechMinusF_shift_cusp0 (y : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ z ∈ idealTriangleCl, ‖z‖ ≤ δ → ‖leechMinusF y ρ (z - 1)‖ ≤ M := by
  obtain ⟨δ, M, hδ, -, hM⟩ := exists_bound_leech_shift_cusp0 y
  refine ⟨δ, M, hδ, fun z hz hzn => ?_⟩
  have huim : 0 < (z - 1).im := by simpa using hz.1
  have h := hM z hz hzn
  rw [leechMinusF_eq_TST huim, norm_mul]
  exact (mul_le_mul h (norm_gaussE_le_one hρ huim) (norm_nonneg _)
    ((norm_nonneg _).trans h)).trans_eq (mul_one _)

theorem exists_bound_leechMinusF_shift_cusp1 (y : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ z ∈ idealTriangleCl, ‖z - 1‖ ≤ δ → ‖leechMinusF y ρ (z - 1)‖ ≤ M := by
  obtain ⟨δ, M, hδ, hδ2, hM⟩ := exists_bound_leechHat_shift_cusp1 (imagPt y)
  refine ⟨δ, M + (3 / 2) ^ 10 * (Real.exp (2 * π * 1) *
    (‖leechAxisCusp 1 y 0‖ * 1 + ‖leechAxisCusp 1 y 1‖)), hδ, fun z hz hzn => ?_⟩
  have huim : 0 < (z - 1).im := by simpa using hz.1
  have h1 := hM z hz hzn
  have h2 := norm_cuspPartMinus_le_of_norm_le (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1)
    (hzn.trans hδ2)
  have h3 := (norm_sub_le (rightC ckmrvLeechHatKernel (imagPt y) (z - 1))
    (cuspPartMinus (leechAxisCusp 1 y 0) (leechAxisCusp 1 y 1) (z - 1))).trans (add_le_add h1 h2)
  rw [leechMinusF, norm_mul]
  exact (mul_le_mul h3 (norm_gaussE_le_one hρ huim) (norm_nonneg _)
    ((norm_nonneg _).trans h3)).trans_eq (mul_one _)

/-! ## The bound `|G| ≤ C/(1 + Im z)²` -/

theorem exists_bound_leechGPlus {y : ℝ} (hy : 0 < y) {ρ : ℝ} (hρ : 2 < ρ) {G : ℂ → ℂ}
    (hGc : ContinuousOn G idealTriangleCl)
    (hGF : ∀ z, z ∉ specialPlus y → G z = leechFPlus y ρ z) :
    ∃ C, ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2 := by
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  obtain ⟨a, b, ha, hab⟩ := exists_im_bounds_of_finset (specialPlus y) (im_pos_of_mem_specialPlus hy)
  have hpS : sigmaC y + 1 ∈ specialPlus y := by simp [specialPlus]
  have hpim : 0 < (sigmaC y + 1).im := im_pos_of_mem_specialPlus hy _ hpS
  obtain ⟨M, V, hMV⟩ := exists_bound_leechPlusF_top y hρ
  obtain ⟨δ₀, M₀, hδ₀, hM₀⟩ := exists_bound_leechPlusF_cusp0 y hρ0
  obtain ⟨δ₁, M₁, hδ₁, hM₁⟩ := exists_bound_leechPlusF_cusp1 y hρ0
  set c := leechCPlus y ρ
  refine idealTriangle_bound_of_pieces hGc
    (V := max (max V (b + 1)) (max 1 (2 * (sigmaC y + 1).im)))
    (M := M + ‖c‖ * (16 * (sigmaC y + 1).im)) (δ₀ := min δ₀ (a / 2)) (δ₁ := min δ₁ (a / 2))
    (M₀ := M₀ + ‖c‖ * (4 / (sigmaC y + 1).im)) (M₁ := M₁ + ‖c‖ * (4 / (sigmaC y + 1).im))
    (lt_min hδ₀ (by positivity)) (lt_min hδ₁ (by positivity)) ?_ ?_ ?_
  · intro z hz hV
    simp only [max_le_iff] at hV
    obtain ⟨⟨hV1, hV2⟩, hV3, hV4⟩ := hV
    rw [hGF z (not_mem_of_lt_im (fun q hq => (hab q hq).2) (by linarith)), leechFPlus]
    have h1 := hMV z hz.1 hz.2.1 hz.2.2.1 hV1
    have h2 := norm_principalK_le_top hpim hV3 hV4
    calc _ ≤ ‖leechPlusF y ρ z‖ + ‖c‖ * ‖principalK (sigmaC y + 1) z‖ := norm_sub_mul_le _ _ _
      _ ≤ M / (1 + z.im) ^ 2 + ‖c‖ * (16 * (sigmaC y + 1).im / (1 + z.im) ^ 2) := by gcongr
      _ = (M + ‖c‖ * (16 * (sigmaC y + 1).im)) / (1 + z.im) ^ 2 := by ring
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm'.trans (hzn.trans (min_le_right _ _))
    rw [hGF z (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by linarith)), leechFPlus]
    have h1 := hM₀ z hz (hzn.trans (min_le_left _ _))
    have h2 := norm_principalK_le_low hpim hz.1 (by linarith [(hab _ hpS).1])
    calc _ ≤ ‖leechPlusF y ρ z‖ + ‖c‖ * ‖principalK (sigmaC y + 1) z‖ := norm_sub_mul_le _ _ _
      _ ≤ M₀ + ‖c‖ * (4 / (sigmaC y + 1).im) := by gcongr
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm_sub_one.trans (hzn.trans (min_le_right _ _))
    rw [hGF z (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by linarith)), leechFPlus]
    have h1 := hM₁ z hz (hzn.trans (min_le_left _ _))
    have h2 := norm_principalK_le_low hpim hz.1 (by linarith [(hab _ hpS).1])
    calc _ ≤ ‖leechPlusF y ρ z‖ + ‖c‖ * ‖principalK (sigmaC y + 1) z‖ := norm_sub_mul_le _ _ _
      _ ≤ M₁ + ‖c‖ * (4 / (sigmaC y + 1).im) := by gcongr

theorem exists_bound_leechGMinus {y : ℝ} (hy : 0 < y) {ρ : ℝ} (hρ : 2 < ρ) {G : ℂ → ℂ}
    (hGc : ContinuousOn (fun z => G (z - 1)) idealTriangleCl)
    (hGF : ∀ z, z ∉ specialMinus y → G z = leechFMinus y ρ z) :
    ∃ C, ∀ z ∈ idealTriangleCl, ‖G (z - 1)‖ ≤ C / (1 + z.im) ^ 2 := by
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  obtain ⟨a, b, ha, hab⟩ :=
    exists_im_bounds_of_finset (specialMinus y) (im_pos_of_mem_specialMinus hy)
  have hpS : sigmaC y - 1 ∈ specialMinus y := by simp [specialMinus]
  have hpim : 0 < (sigmaC y - 1).im := im_pos_of_mem_specialMinus hy _ hpS
  obtain ⟨M, V, hMV⟩ := exists_bound_leechMinusF_top y hρ
  obtain ⟨δ₀, M₀, hδ₀, hM₀⟩ := exists_bound_leechMinusF_shift_cusp0 y hρ0
  obtain ⟨δ₁, M₁, hδ₁, hM₁⟩ := exists_bound_leechMinusF_shift_cusp1 y hρ0
  set c := leechCMinus y ρ
  have him : ∀ z : ℂ, (z - 1).im = z.im := fun z => by simp
  refine idealTriangle_bound_of_pieces hGc
    (V := max (max V (b + 1)) (max 1 (2 * (sigmaC y - 1).im)))
    (M := M + ‖c‖ * (16 * (sigmaC y - 1).im)) (δ₀ := min δ₀ (a / 2)) (δ₁ := min δ₁ (a / 2))
    (M₀ := M₀ + ‖c‖ * (4 / (sigmaC y - 1).im)) (M₁ := M₁ + ‖c‖ * (4 / (sigmaC y - 1).im))
    (lt_min hδ₀ (by positivity)) (lt_min hδ₁ (by positivity)) ?_ ?_ ?_
  · intro z hz hV
    simp only [max_le_iff] at hV
    obtain ⟨⟨hV1, hV2⟩, hV3, hV4⟩ := hV
    rw [hGF (z - 1) (not_mem_of_lt_im (fun q hq => (hab q hq).2) (by rw [him z]; linarith)),
      leechFMinus]
    have h1 := hMV (z - 1) (by rw [him z]; exact hz.1)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2.1])
      (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2.2.1])
      (by rw [him z]; exact hV1)
    have h2 := norm_principalK_le_top hpim (z := z - 1) (by rw [him z]; exact hV3)
      (by rw [him z]; exact hV4)
    rw [him z] at h1 h2
    calc _ ≤ ‖leechMinusF y ρ (z - 1)‖ + ‖c‖ * ‖principalK (sigmaC y - 1) (z - 1)‖ :=
          norm_sub_mul_le _ _ _
      _ ≤ M / (1 + z.im) ^ 2 + ‖c‖ * (16 * (sigmaC y - 1).im / (1 + z.im) ^ 2) := by gcongr
      _ = (M + ‖c‖ * (16 * (sigmaC y - 1).im)) / (1 + z.im) ^ 2 := by ring
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm'.trans (hzn.trans (min_le_right _ _))
    rw [hGF (z - 1) (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by rw [him z]; linarith)),
      leechFMinus]
    have h1 := hM₀ z hz (hzn.trans (min_le_left _ _))
    have h2 := norm_principalK_le_low hpim (z := z - 1) (by rw [him z]; exact hz.1)
      (by rw [him z]; linarith [(hab _ hpS).1])
    calc _ ≤ ‖leechMinusF y ρ (z - 1)‖ + ‖c‖ * ‖principalK (sigmaC y - 1) (z - 1)‖ :=
          norm_sub_mul_le _ _ _
      _ ≤ M₀ + ‖c‖ * (4 / (sigmaC y - 1).im) := by gcongr
  · intro z hz hzn
    have hzim : z.im ≤ a / 2 := im_le_norm_sub_one.trans (hzn.trans (min_le_right _ _))
    rw [hGF (z - 1) (not_mem_of_im_lt (fun q hq => (hab q hq).1) (by rw [him z]; linarith)),
      leechFMinus]
    have h1 := hM₁ z hz (hzn.trans (min_le_left _ _))
    have h2 := norm_principalK_le_low hpim (z := z - 1) (by rw [him z]; exact hz.1)
      (by rw [him z]; linarith [(hab _ hpS).1])
    calc _ ≤ ‖leechMinusF y ρ (z - 1)‖ + ‖c‖ * ‖principalK (sigmaC y - 1) (z - 1)‖ :=
          norm_sub_mul_le _ _ _
      _ ≤ M₁ + ‖c‖ * (4 / (sigmaC y - 1).im) := by gcongr

/-! ## Cauchy's theorem for `G₊` and `G₋(· − 1)` -/

/-- **Cauchy for `F₊` on `(0, 1, ∞)`** (`ρ > 2`). -/
theorem exists_leechGPlus_cauchy {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {ρ : ℝ} (hρ : 2 < ρ) :
    ∃ G : ℂ → ℂ, (∀ z, z ∉ specialPlus y → G z = leechFPlus y ρ z) ∧
      ContinuousOn G idealTriangleCl ∧
      (∃ C, ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2) ∧
      (∫ t in Ioi (0 : ℝ), I * G (1 + I * t)) - (∫ t in Ioi (0 : ℝ), I * G (I * t)) =
        ∫ θ in (0 : ℝ)..π, semicircleIntegrand G θ := by
  obtain ⟨G, hGd, hGF⟩ := exists_leechGPlus hy hy1 ρ
  have hGc : ContinuousOn G idealTriangleCl := fun z hz =>
    (hGd z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := exists_bound_leechGPlus hy hρ hGc hGF
  exact ⟨G, hGF, hGc, ⟨C, hC⟩, idealTriangle_cauchy
    (fun z hz => (hGd z (idealTriangle_subset_cl hz)).differentiableWithinAt) hGc hC⟩

/-- **Cauchy for `F₋` on `(−1, 0, ∞)`** (translated to `(0, 1, ∞)`; `ρ > 2`). -/
theorem exists_leechGMinus_cauchy {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {ρ : ℝ} (hρ : 2 < ρ) :
    ∃ G : ℂ → ℂ, (∀ z, z ∉ specialMinus y → G z = leechFMinus y ρ z) ∧
      ContinuousOn (fun z => G (z - 1)) idealTriangleCl ∧
      (∃ C, ∀ z ∈ idealTriangleCl, ‖G (z - 1)‖ ≤ C / (1 + z.im) ^ 2) ∧
      (∫ t in Ioi (0 : ℝ), I * G (I * t)) - (∫ t in Ioi (0 : ℝ), I * G (I * t - 1)) =
        ∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => G (z - 1)) θ := by
  obtain ⟨G, hGd, hGF⟩ := exists_leechGMinus hy hy1 ρ
  have hHd : ∀ z ∈ idealTriangleCl, DifferentiableAt ℂ (fun z => G (z - 1)) z := fun z hz =>
    (hGd (z - 1) (by simpa using hz)).comp z (differentiableAt_fun_id.sub_const 1)
  have hHc : ContinuousOn (fun z => G (z - 1)) idealTriangleCl := fun z hz =>
    (hHd z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := exists_bound_leechGMinus hy hρ hHc hGF
  have h := idealTriangle_cauchy (g := fun z => G (z - 1))
    (fun z hz => (hHd z (idealTriangle_subset_cl hz)).differentiableWithinAt) hHc hC
  refine ⟨G, hGF, hHc, ⟨C, hC⟩, ?_⟩
  simp only [add_sub_cancel_left] at h
  exact h

end E8Leech
