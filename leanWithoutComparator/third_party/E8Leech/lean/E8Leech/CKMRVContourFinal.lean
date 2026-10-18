import E8Leech.CKMRVContourAssembly

/-!
# The CKMRV identity (**) in dimension eight, and the conditional E8 certificate

Putting the pieces together (`CKMRVContourCauchy`, `CKMRVContourAssembly`):

* the `2t⁻⁴e^{−πρ/t}` term becomes, after `t ↦ 1/s` and the right relation one, the lines
  `L₀, L₁, L₋₁` of the two ideal triangles;
* the `(t ∓ i)` terms become the two semicircles;
* Cauchy for `F± = f − c±k±` on both triangles cancels every `f`-term;
* the explicit principal parts give `Q' = −4 arctan(1/y) − 4 arctan y = −2π`, which produces the
  Gaussian `y⁻⁴ e^{−πρ/y}`.

This is the hypothesis `hF` of `e8_exists_gaussianSchwartzCertificate_of_pos`, so the only remaining
analytic input of the `E8` certificate is the positivity (6.4)(1).
-/

namespace E8Leech

open Complex Filter Topology Set MeasureTheory
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm FourierTransform

/-! ## Principal parts on the imaginary axis -/

theorem norm_principalK_imag_le {q : ℂ} (hq : 0 < q.im) (hqr : |q.re| = 1) {t : ℝ}
    (ht : 0 ≤ t) : ‖principalK q (I * t)‖ ≤ 8 * q.im * (1 + q.im) / (1 + t) ^ 2 := by
  have hre1 : (I * (t : ℂ) - q).re = -q.re := by simp
  have him1 : (I * (t : ℂ) - q).im = t - q.im := by simp
  have hre2 : (I * (t : ℂ) - (starRingEnd ℂ) q).re = -q.re := by simp
  have him2 : (I * (t : ℂ) - (starRingEnd ℂ) q).im = t + q.im := by simp
  have hX1 : 1 ≤ ‖I * (t : ℂ) - q‖ := by
    have := Complex.abs_re_le_norm (I * (t : ℂ) - q); rwa [hre1, abs_neg, hqr] at this
  have hX2 : t - q.im ≤ ‖I * (t : ℂ) - q‖ := by
    have := Complex.abs_im_le_norm (I * (t : ℂ) - q); rw [him1] at this
    exact (le_abs_self _).trans this
  have hY1 : 1 ≤ ‖I * (t : ℂ) - (starRingEnd ℂ) q‖ := by
    have := Complex.abs_re_le_norm (I * (t : ℂ) - (starRingEnd ℂ) q)
    rwa [hre2, abs_neg, hqr] at this
  have hY2 : t + q.im ≤ ‖I * (t : ℂ) - (starRingEnd ℂ) q‖ := by
    have := Complex.abs_im_le_norm (I * (t : ℂ) - (starRingEnd ℂ) q); rw [him2] at this
    exact (le_abs_self _).trans this
  have hA : 1 + t ≤ ‖I * (t : ℂ) - q‖ * (2 + 2 * q.im) := by
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hX1)]
  have hB : 1 + t ≤ 2 * ‖I * (t : ℂ) - (starRingEnd ℂ) q‖ := by linarith
  have h1 : I * (t : ℂ) - q ≠ 0 := norm_pos_iff.mp (by linarith)
  have h2 : I * (t : ℂ) - (starRingEnd ℂ) q ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn : ‖(2 * (q.im : ℂ) * I)‖ = 2 * q.im := by simp [abs_of_pos hq]
  have hXY : (1 + t) ^ 2 ≤ (‖I * (t : ℂ) - q‖ * (2 + 2 * q.im)) *
      (2 * ‖I * (t : ℂ) - (starRingEnd ℂ) q‖) := by
    rw [sq]; exact mul_le_mul hA hB (by positivity) (by positivity)
  have hpos : 0 < ‖I * (t : ℂ) - q‖ * ‖I * (t : ℂ) - (starRingEnd ℂ) q‖ :=
    mul_pos (by linarith) (by linarith)
  rw [principalK_eq h1 h2, norm_div, hn, norm_mul,
    div_le_div_iff₀ hpos (by positivity)]
  have := mul_le_mul_of_nonneg_left hXY (by positivity : (0 : ℝ) ≤ 2 * q.im)
  linarith

theorem integrableOn_principalK_imag {q : ℂ} (hq : 0 < q.im) (hqr : |q.re| = 1) :
    IntegrableOn (fun t : ℝ => principalK q (I * t)) (Ioi 0) := by
  have hq0 : q.re ≠ 0 := fun h => by rw [h, abs_zero] at hqr; exact zero_ne_one hqr
  have hne1 : ∀ t : ℝ, I * (t : ℂ) - q ≠ 0 := fun t h => hq0 (by
    have := congrArg Complex.re h; simp at this; linarith)
  have hne2 : ∀ t : ℝ, I * (t : ℂ) - (starRingEnd ℂ) q ≠ 0 := fun t h => hq0 (by
    have := congrArg Complex.re h; simp at this; linarith)
  have hc : Continuous fun t : ℝ => principalK q (I * t) := by
    simp only [principalK]
    exact (continuous_const.div (by fun_prop) hne1).sub (continuous_const.div (by fun_prop) hne2)
  exact integrableOn_Ioi_of_bound hc.continuousOn fun t ht => norm_principalK_imag_le hq hqr ht.le

theorem inv_sub_inv_imag (w : ℝ) :
    (1 : ℂ) / (-1 + I * w) - 1 / (1 + I * w) = ((-2 * (1 / (1 + w ^ 2)) : ℝ) : ℂ) := by
  have h1 : (-1 + I * (w : ℂ)) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this
  have h2 : (1 + I * (w : ℂ)) ≠ 0 := one_add_I_mul_ne_zero w
  have h3 : (1 + (w : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : (1 + w ^ 2 : ℝ) ≠ 0)
  push_cast
  rw [div_sub_div _ _ h1 h2, mul_one_div, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  linear_combination (2 * (w : ℂ) ^ 2) * Complex.I_sq

theorem principalK_sub_imag (a t : ℝ) :
    principalK (I * a + 1) (I * t) - principalK (I * a - 1) (I * t) =
      ((-2 * (1 / (1 + (t - a) ^ 2)) + 2 * (1 / (1 + (t - -a) ^ 2)) : ℝ) : ℂ) := by
  have c1 : (starRingEnd ℂ) (I * (a : ℂ) + 1) = -(I * a) + 1 := by apply Complex.ext <;> simp
  have c2 : (starRingEnd ℂ) (I * (a : ℂ) - 1) = -(I * a) - 1 := by apply Complex.ext <;> simp
  have e1 : I * (t : ℂ) - (I * a + 1) = -1 + I * ((t - a : ℝ) : ℂ) := by push_cast; ring
  have e2 : I * (t : ℂ) - (-(I * a) + 1) = -1 + I * ((t - -a : ℝ) : ℂ) := by push_cast; ring
  have e3 : I * (t : ℂ) - (I * a - 1) = 1 + I * ((t - a : ℝ) : ℂ) := by push_cast; ring
  have e4 : I * (t : ℂ) - (-(I * a) - 1) = 1 + I * ((t - -a : ℝ) : ℂ) := by push_cast; ring
  simp only [principalK]
  rw [c1, c2, e1, e2, e3, e4]
  have k1 := inv_sub_inv_imag (t - a)
  have k2 := inv_sub_inv_imag (t - -a)
  rw [show ∀ x y z w : ℂ, x - y - (z - w) = (x - z) - (y - w) from fun _ _ _ _ => by ring, k1, k2]
  push_cast
  ring

theorem integral_Ioi_inv_one_add_sq_sub (c : ℝ) :
    IntegrableOn (fun t : ℝ => 1 / (1 + (t - c) ^ 2)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 1 / (1 + (t - c) ^ 2) = π / 2 + Real.arctan c := by
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t => Real.arctan (t - c)) (1 / (1 + (x - c) ^ 2)) x := by
    intro x _
    have h := (Real.hasDerivAt_arctan (x - c)).comp x ((hasDerivAt_id' x).sub_const c)
    rw [mul_one] at h
    exact h
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ 1 / (1 + (x - c) ^ 2) := fun x _ => by positivity
  have hlim : Tendsto (fun t => Real.arctan (t - c)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      ((tendsto_atTop_add_const_right _ (-c) tendsto_id).congr fun t => (sub_eq_add_neg t c).symm)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hlim, zero_sub, Real.arctan_neg,
    sub_neg_eq_add]

theorem integral_principalK_sub_imag (a : ℝ) :
    ∫ t in Ioi (0 : ℝ), (principalK (I * a + 1) (I * t) - principalK (I * a - 1) (I * t)) =
      ((-4 * Real.arctan a : ℝ) : ℂ) := by
  obtain ⟨i1, v1⟩ := integral_Ioi_inv_one_add_sq_sub a
  obtain ⟨i2, v2⟩ := integral_Ioi_inv_one_add_sq_sub (-a)
  simp_rw [principalK_sub_imag]
  rw [integral_complex_ofReal, integral_add (i1.const_mul (-2)) (i2.const_mul 2), integral_const_mul,
    integral_const_mul, v1, v2, Real.arctan_neg]
  push_cast
  ring

/-! ## Möbius pull-back of the principal parts to the semicircles -/

theorem mobius_v_term {z q : ℂ} (hz : 1 + z ≠ 0) (hq : 1 + q ≠ 0) (hzq : z - q ≠ 0) :
    1 / (z / (1 + z) - q / (1 + q)) * (1 / (1 + z) ^ 2) = 1 / (z - q) - 1 / (z + 1) := by
  have hz' : z + 1 ≠ 0 := by rwa [add_comm]
  have h1 : z / (1 + z) - q / (1 + q) = (z - q) / ((1 + z) * (1 + q)) := by
    rw [div_sub_div _ _ hz hq]; congr 1; ring
  rw [h1]
  field_simp
  ring

theorem mobius_u_term {z q : ℂ} (hz : 1 - z ≠ 0) (hq : 1 - q ≠ 0) (hzq : z - q ≠ 0) :
    1 / (z / (1 - z) - q / (1 - q)) * (1 / (1 - z) ^ 2) = 1 / (z - q) + 1 / (1 - z) := by
  have h1 : z / (1 - z) - q / (1 - q) = (z - q) / ((1 - z) * (1 - q)) := by
    rw [div_sub_div _ _ hz hq]; congr 1; ring
  rw [h1]
  field_simp
  ring

theorem principalK_vPath {q : ℂ} (hq1 : 1 + q ≠ 0) (hq1' : 1 + (starRingEnd ℂ) q ≠ 0) {t : ℝ}
    (h1 : I * (t : ℂ) - q ≠ 0) (h2 : I * (t : ℂ) - (starRingEnd ℂ) q ≠ 0) :
    principalK (q / (1 + q)) (vPath t) * vPath' t = I * principalK q (I * t) := by
  have hD := one_add_I_mul_ne_zero t
  have hc : (starRingEnd ℂ) (q / (1 + q)) = (starRingEnd ℂ) q / (1 + (starRingEnd ℂ) q) := by
    simp [map_div₀]
  have T1 := mobius_v_term (z := I * t) hD hq1 h1
  have T2 := mobius_v_term (z := I * t) hD hq1' h2
  simp only [principalK, vPath, vPath', hc]
  linear_combination I * T1 - I * T2

theorem principalK_uPath {q : ℂ} (hq1 : 1 - q ≠ 0) (hq1' : 1 - (starRingEnd ℂ) q ≠ 0) {t : ℝ}
    (h1 : I * (t : ℂ) - q ≠ 0) (h2 : I * (t : ℂ) - (starRingEnd ℂ) q ≠ 0) :
    principalK (q / (1 - q)) (uPath t) * uPath' t = I * principalK q (I * t) := by
  have hE := one_sub_I_mul_ne_zero t
  have hc : (starRingEnd ℂ) (q / (1 - q)) = (starRingEnd ℂ) q / (1 - (starRingEnd ℂ) q) := by
    simp [map_div₀]
  have T1 := mobius_u_term (z := I * t) hE hq1 h1
  have T2 := mobius_u_term (z := I * t) hE hq1' h2
  simp only [principalK, uPath, uPath', hc]
  linear_combination I * T1 - I * T2

theorem sigma_add_one_eq {y : ℝ} (hy : 0 < y) :
    sigmaC y + 1 = (I * y - 1) / (1 + (I * y - 1)) := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hIy : I * (y : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hy0
  rw [sigmaC_eq hy, show (1 : ℂ) + (I * y - 1) = I * y by ring, eq_div_iff hIy]
  push_cast
  have hyy : (y : ℂ)⁻¹ * y = 1 := inv_mul_cancel₀ hy0
  linear_combination I ^ 2 * hyy + Complex.I_sq

theorem sigma_sub_one_eq {y : ℝ} (hy : 0 < y) :
    sigmaC y - 1 = (I * y + 1) / (1 - (I * y + 1)) := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hIy : -(I * (y : ℂ)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero I_ne_zero hy0)
  rw [sigmaC_eq hy, show (1 : ℂ) - (I * y + 1) = -(I * y) by ring, eq_div_iff hIy]
  push_cast
  have hyy : (y : ℂ)⁻¹ * y = 1 := inv_mul_cancel₀ hy0
  linear_combination -(I ^ 2 * hyy + Complex.I_sq)

/-- `k₊(v) v' = i · k(−1 + iy)(it)`. -/
theorem principalK_sigma_vPath {y : ℝ} (hy : 0 < y) (t : ℝ) :
    principalK (sigmaC y + 1) (vPath t) * vPath' t = I * principalK (I * y - 1) (I * t) := by
  have hc : (starRingEnd ℂ) (I * (y : ℂ) - 1) = -(I * y) - 1 := by apply Complex.ext <;> simp
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [sigma_add_one_eq hy]
  refine principalK_vPath ?_ ?_ ?_ ?_
  · rw [show (1 : ℂ) + (I * y - 1) = I * y by ring]; exact mul_ne_zero I_ne_zero hy0
  · rw [hc, show (1 : ℂ) + (-(I * y) - 1) = -(I * y) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero I_ne_zero hy0)
  · intro h; have := congrArg Complex.re h; simp at this
  · intro h; rw [hc] at h; have := congrArg Complex.re h; simp at this

/-- `k₋(u) u' = i · k(1 + iy)(it)`. -/
theorem principalK_sigma_uPath {y : ℝ} (hy : 0 < y) (t : ℝ) :
    principalK (sigmaC y - 1) (uPath t) * uPath' t = I * principalK (I * y + 1) (I * t) := by
  have hc : (starRingEnd ℂ) (I * (y : ℂ) + 1) = -(I * y) + 1 := by apply Complex.ext <;> simp
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [sigma_sub_one_eq hy]
  refine principalK_uPath ?_ ?_ ?_ ?_
  · rw [show (1 : ℂ) - (I * y + 1) = -(I * y) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero I_ne_zero hy0)
  · rw [hc, show (1 : ℂ) - (-(I * y) + 1) = I * y by ring]; exact mul_ne_zero I_ne_zero hy0
  · intro h; have := congrArg Complex.re h; simp at this
  · intro h; rw [hc] at h; have := congrArg Complex.re h; simp at this

/-! ## Finitely many exceptional points -/

theorem injective_I_mul : Function.Injective fun t : ℝ => I * (t : ℂ) := fun a b h => by
  have := congrArg Complex.im h; simpa using this

theorem injective_one_add_I_mul : Function.Injective fun t : ℝ => 1 + I * (t : ℂ) :=
  fun a b h => by have := congrArg Complex.im h; simpa using this

theorem injective_I_mul_sub_one : Function.Injective fun t : ℝ => I * (t : ℂ) - 1 :=
  fun a b h => by have := congrArg Complex.im h; simpa using this

theorem injective_vPath : Function.Injective vPath := fun a b h => by
  have ha := vPath_div_one_sub a
  rw [h, vPath_div_one_sub b] at ha
  exact injective_I_mul ha.symm

theorem injective_uPath : Function.Injective uPath := fun a b h => by
  have ha := uPath_div_add_one a
  rw [h, uPath_div_add_one b] at ha
  exact injective_I_mul ha.symm

theorem ae_not_mem_of_injective {φ : ℝ → ℂ} (hφ : Function.Injective φ) (P : Finset ℂ) :
    ∀ᵐ s : ℝ, φ s ∉ P := by
  have hfin : (φ ⁻¹' (P : Set ℂ)).Finite := P.finite_toSet.preimage hφ.injOn
  refine (ae_iff).2 (measure_mono_null (fun s hs => ?_) (hfin.measure_zero volume))
  simpa using hs

theorem ae_eq_of_eq_off_finset {φ : ℝ → ℂ} (hφ : Function.Injective φ) (P : Finset ℂ)
    {F G : ℂ → ℂ} (h : ∀ z, z ∉ P → F z = G z) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), F (φ t) = G (φ t) :=
  ae_restrict_of_ae ((ae_not_mem_of_injective hφ P).mono fun _ ht => h _ ht)

theorem integrableOn_line_one {G : ℂ → ℂ} (hGc : ContinuousOn G idealTriangleCl) {C : ℝ}
    (hC : ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2) :
    IntegrableOn (fun t : ℝ => G (1 + I * t)) (Ioi 0) :=
  integrableOn_Ioi_of_bound
    (continuousOn_comp_line hGc (by fun_prop) fun t ht => one_add_I_mul_mem ht)
    fun t ht => by simpa using hC _ (one_add_I_mul_mem ht)

theorem integrableOn_line_zero {G : ℂ → ℂ} (hGc : ContinuousOn G idealTriangleCl) {C : ℝ}
    (hC : ∀ z ∈ idealTriangleCl, ‖G z‖ ≤ C / (1 + z.im) ^ 2) :
    IntegrableOn (fun t : ℝ => G (I * t)) (Ioi 0) :=
  integrableOn_Ioi_of_bound
    (continuousOn_comp_line hGc (by fun_prop) fun t ht => I_mul_mem ht)
    fun t ht => by simpa using hC _ (I_mul_mem ht)

theorem gaussE_one (ρ : ℝ) : gaussE ρ 1 = cexp (π * I * ρ) := by simp [gaussE]

/-! ## The algebra of the assembly -/

theorem contour_algebra {LHS T1 T2 T3 F0 P0 P1 M0 M1 SG SH Kp Km Jp Jm cp cm eP eM C₀ Y A B : ℂ}
    (e1 : LHS = 2 * T1 - T2 - T3) (e2 : 2 * T1 = 2 * F0 - eM * P1 - eP * M1)
    (e3 : T2 = I * eM * SG + eM * cp * Jm) (e4 : T3 = -(I * eP * SH) + eP * cm * Jp)
    (e5 : SG = I * P1 - I * P0) (e6 : SH = I * M0 - I * M1)
    (e7 : F0 = P0 + cp * Kp) (e8 : F0 = M0 + cm * Km)
    (e9 : Kp - Km = -4 * A) (e10 : Jp - Jm = -4 * B)
    (e11 : eM * cp = C₀) (e11' : eP * cm = -C₀) (e13 : A + B = π / 2) (e14 : C₀ * (2 * π) = Y) :
    LHS + Y = (2 - eP - eM) * F0 := by
  linear_combination e1 + e2 - e3 - e4 - I * eM * e5 + I * eP * e6 +
    (eP * (M0 - M1) - eM * (P1 - P0)) * Complex.I_sq + (Kp - Jm) * e11 + (Km - Jp) * e11' +
    eM * e7 + eP * e8 + C₀ * e9 + C₀ * e10 - 4 * C₀ * e13 - e14

/-! ## The identity (**) -/

/-- **The CKMRV identity (**) in dimension eight** (`τ = iy`, `ρ = r²`):
`∫ 𝒦(iy, it)(2γ(t) − γ(t − i) − γ(t + i)) dt + y⁻⁴e^{−πr²/y} = 4 sin²(πr²/2) ∫ 𝒦̂(iy, it) e^{−πr²t} dt`. -/
theorem ckmrv_contour_identity {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) {r : ℝ} (hr : r ≠ 0) :
    (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
        (2 * gaussHat 8 t r - gaussHat 8 (t - I) r - gaussHat 8 (t + I) r)) +
      ((y⁻¹ ^ 4 : ℝ) : ℂ) * (Real.exp (-(π / y) * r ^ 2) : ℂ) =
    ((4 * Real.sin (π * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi (0 : ℝ), ckmrvEightHatKernel (imagPt y) (imagPt t) *
        (Real.exp (-(π * r ^ 2) * t) : ℂ) := by
  have hρ : 0 < r ^ 2 := by positivity
  obtain ⟨Gp, hGpF, hGpc, ⟨Cp, hCp⟩, hCauchyP⟩ := exists_gPlus_cauchy hy hy1 hρ
  obtain ⟨Gm, hGmF, hGmc, ⟨Cm, hCm⟩, hCauchyM⟩ := exists_gMinus_cauchy hy hy1 hρ
  -- principal parts on the imaginary axis
  have hqp : 0 < (sigmaC y + 1).im := by
    rw [Complex.add_im, im_sigmaC hy, Complex.one_im, add_zero]; exact inv_pos.mpr hy
  have hqm : 0 < (sigmaC y - 1).im := by
    rw [Complex.sub_im, im_sigmaC hy, Complex.one_im, sub_zero]; exact inv_pos.mpr hy
  have hqpr : |(sigmaC y + 1).re| = 1 := by
    rw [Complex.add_re, re_sigmaC hy, Complex.one_re, zero_add, abs_one]
  have hqmr : |(sigmaC y - 1).re| = 1 := by
    rw [Complex.sub_re, re_sigmaC hy, Complex.one_re, zero_sub, abs_neg, abs_one]
  have ikp := integrableOn_principalK_imag hqp hqpr
  have ikm := integrableOn_principalK_imag hqm hqmr
  have iJp := integrableOn_principalK_imag (q := I * y + 1) (by simpa using hy) (by simp)
  have iJm := integrableOn_principalK_imag (q := I * y - 1) (by simpa using hy) (by simp)
  -- the corrected functions on the lines
  have iGp1 : IntegrableOn (fun t : ℝ => Gp (1 + I * t)) (Ioi 0) := integrableOn_line_one hGpc hCp
  have iGp0 : IntegrableOn (fun t : ℝ => Gp (I * t)) (Ioi 0) := integrableOn_line_zero hGpc hCp
  have iGm0 : IntegrableOn (fun t : ℝ => Gm (I * t)) (Ioi 0) :=
    (integrableOn_line_one hGmc hCm).congr_fun (fun t _ => by simp only [add_sub_cancel_left])
      measurableSet_Ioi
  have iGm1 : IntegrableOn (fun t : ℝ => Gm (I * t - 1)) (Ioi 0) :=
    integrableOn_line_zero hGmc hCm
  -- finitely many exceptional points
  have aeP0 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gp (I * t) = fPlus y (r ^ 2) (I * t) :=
    ae_eq_of_eq_off_finset injective_I_mul (specialPlus y) hGpF
  have aeP1 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gp (1 + I * t) = fPlus y (r ^ 2) (1 + I * t) :=
    ae_eq_of_eq_off_finset injective_one_add_I_mul (specialPlus y) hGpF
  have aeM0 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gm (I * t) = fMinus y (r ^ 2) (I * t) :=
    ae_eq_of_eq_off_finset injective_I_mul (specialMinus y) hGmF
  have aeM1 : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gm (I * t - 1) = fMinus y (r ^ 2) (I * t - 1) :=
    ae_eq_of_eq_off_finset injective_I_mul_sub_one (specialMinus y) hGmF
  have aeV : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gp (vPath t) = fPlus y (r ^ 2) (vPath t) :=
    ae_eq_of_eq_off_finset injective_vPath (specialPlus y) hGpF
  have aeU : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      Gm (uPath t) = fMinus y (r ^ 2) (uPath t) :=
    ae_eq_of_eq_off_finset injective_uPath (specialMinus y) hGmF
  -- `f` on `L₀`
  have iF0 : IntegrableOn (fun t : ℝ => contourF y (r ^ 2) (I * t)) (Ioi 0) := by
    refine Integrable.congr (Integrable.add iGp0 (Integrable.const_mul ikp (cPlus y (r ^ 2)))) ?_
    filter_upwards [aeP0] with t ht
    simp only [Pi.add_apply]
    rw [ht, fPlus]
    ring
  have e7 : (∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (I * t)) =
      (∫ t in Ioi (0 : ℝ), Gp (I * t)) +
        cPlus y (r ^ 2) * ∫ t in Ioi (0 : ℝ), principalK (sigmaC y + 1) (I * t) := by
    rw [← integral_const_mul, ← integral_add iGp0 (Integrable.const_mul ikp (cPlus y (r ^ 2)))]
    refine integral_congr_ae ?_
    filter_upwards [aeP0] with t ht
    rw [ht, fPlus]
    ring
  have e8 : (∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (I * t)) =
      (∫ t in Ioi (0 : ℝ), Gm (I * t)) +
        cMinus y (r ^ 2) * ∫ t in Ioi (0 : ℝ), principalK (sigmaC y - 1) (I * t) := by
    rw [← integral_const_mul, ← integral_add iGm0 (Integrable.const_mul ikm (cMinus y (r ^ 2)))]
    refine integral_congr_ae ?_
    filter_upwards [aeM0] with t ht
    rw [ht, fMinus]
    ring
  -- Cauchy on both triangles
  have e5 : (∫ θ in (0 : ℝ)..π, semicircleIntegrand Gp θ) =
      I * (∫ t in Ioi (0 : ℝ), Gp (1 + I * t)) - I * ∫ t in Ioi (0 : ℝ), Gp (I * t) := by
    rw [← hCauchyP, integral_const_mul, integral_const_mul]
  have e6 : (∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => Gm (z - 1)) θ) =
      I * (∫ t in Ioi (0 : ℝ), Gm (I * t)) - I * ∫ t in Ioi (0 : ℝ), Gm (I * t - 1) := by
    rw [← hCauchyM, integral_const_mul, integral_const_mul]
  -- the semicircles in the `t`-parametrization
  have hSG := semicircle_conv_v Gp
  have hSH := semicircle_conv_u Gm
  have iGv : IntegrableOn (fun t : ℝ => Gp (vPath t) * vPath' t) (Ioi 0) :=
    hSG.1.mp (integrableOn_semicircleIntegrand hGpc hCp)
  have iGu : IntegrableOn (fun t : ℝ => Gm (uPath t) * uPath' t) (Ioi 0) :=
    hSH.1.mp (integrableOn_semicircleIntegrand hGmc hCm)
  have eSG : (∫ θ in (0 : ℝ)..π, semicircleIntegrand Gp θ) =
      -∫ t in Ioi (0 : ℝ), Gp (vPath t) * vPath' t := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo, hSG.2]
  have eSH : (∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => Gm (z - 1)) θ) =
      ∫ t in Ioi (0 : ℝ), Gm (uPath t) * uPath' t := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo, hSH.2]
  have hmv := principalK_sigma_vPath hy
  have hmu := principalK_sigma_uPath hy
  have efv : (∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (vPath t) * vPath' t) =
      (∫ t in Ioi (0 : ℝ), Gp (vPath t) * vPath' t) +
        cPlus y (r ^ 2) * (I * ∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add iGv
      (Integrable.const_mul (Integrable.const_mul iJm I) (cPlus y (r ^ 2)))]
    refine integral_congr_ae ?_
    filter_upwards [aeV] with t ht
    rw [← hmv t, ht, fPlus]
    ring
  have efu : (∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (uPath t) * uPath' t) =
      (∫ t in Ioi (0 : ℝ), Gm (uPath t) * uPath' t) +
        cMinus y (r ^ 2) * (I * ∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add iGu
      (Integrable.const_mul (Integrable.const_mul iJp I) (cMinus y (r ^ 2)))]
    refine integral_congr_ae ?_
    filter_upwards [aeU] with t ht
    rw [← hmu t, ht, fMinus]
    ring
  have ifv : IntegrableOn (fun t : ℝ => contourF y (r ^ 2) (vPath t) * vPath' t) (Ioi 0) := by
    refine Integrable.congr (Integrable.add iGv
      (Integrable.const_mul (Integrable.const_mul iJm I) (cPlus y (r ^ 2)))) ?_
    filter_upwards [aeV] with t ht
    simp only [Pi.add_apply]
    rw [← hmv t, ht, fPlus]
    ring
  have ifu : IntegrableOn (fun t : ℝ => contourF y (r ^ 2) (uPath t) * uPath' t) (Ioi 0) := by
    refine Integrable.congr (Integrable.add iGu
      (Integrable.const_mul (Integrable.const_mul iJp I) (cMinus y (r ^ 2)))) ?_
    filter_upwards [aeU] with t ht
    simp only [Pi.add_apply]
    rw [← hmu t, ht, fMinus]
    ring
  -- the `t ∓ i` terms
  have eT2 : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 ((t : ℂ) - I) r) = -I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        ∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (vPath t) * vPath' t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => kernel_gaussHat_sub_I y r ht
  have eT3 : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 ((t : ℂ) + I) r) = -I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        ∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (uPath t) * uPath' t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => kernel_gaussHat_add_I y r ht
  have iT2 : IntegrableOn (fun t : ℝ => ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 ((t : ℂ) - I) r) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul ifv (-I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ)))))
      (fun t ht => (kernel_gaussHat_sub_I y r ht).symm) measurableSet_Ioi
  have iT3 : IntegrableOn (fun t : ℝ => ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 ((t : ℂ) + I) r) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul ifu (-I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ))))
      (fun t ht => (kernel_gaussHat_add_I y r ht).symm) measurableSet_Ioi
  have e3 : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 ((t : ℂ) - I) r) =
      I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (∫ θ in (0 : ℝ)..π, semicircleIntegrand Gp θ) +
        cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * cPlus y (r ^ 2) *
          ∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t) := by
    rw [eT2, efv]
    linear_combination (-I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ)))) * eSG -
      (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * cPlus y (r ^ 2) *
        ∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t)) * Complex.I_sq
  have e4 : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 ((t : ℂ) + I) r) =
      -(I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
          (∫ θ in (0 : ℝ)..π, semicircleIntegrand (fun z => Gm (z - 1)) θ)) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * cMinus y (r ^ 2) *
          ∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t) := by
    rw [eT3, efu]
    linear_combination (I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ))) * eSH -
      (cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * cMinus y (r ^ 2) *
        ∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t)) * Complex.I_sq
  -- the `2t⁻⁴e^{−πρ/t}` term
  have e11 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * cMinus y (r ^ 2) =
      -(cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * cPlus y (r ^ 2)) := by
    simp only [cPlus, cMinus, gaussE_add, gaussE_sub_one, gaussE_one]
    ring
  have hk1 : ∀ s : ℝ, principalK (sigmaC y + 1) (1 + I * s) =
      principalK (sigmaC y - 1) (I * s - 1) := fun s => by
    rw [add_comm (1 : ℂ) (I * s)]; exact principalK_add_one_eq _ _
  have aeT1 : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      contourF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        contourF y (r ^ 2) (1 + I * s) + cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        contourF y (r ^ 2) (I * s - 1)) / 2 =
      contourF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * Gp (1 + I * s) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * Gm (I * s - 1)) / 2 := by
    filter_upwards [aeP1, aeM1] with s h1 h2
    rw [h1, h2, fPlus, fMinus]
    linear_combination (-(cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * cPlus y (r ^ 2)) / 2) * hk1 s +
      (-(principalK (sigmaC y - 1) (I * s - 1)) / 2) * e11
  have hinvd : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ => s⁻¹) (-(s ^ 2)⁻¹) (Ioi 0) s :=
    fun s hs => (hasDerivAt_inv (ne_of_gt hs)).hasDerivWithinAt
  have hinvinj : InjOn (fun s : ℝ => s⁻¹) (Ioi 0) := inv_injective.injOn
  have hinvimg : (fun s : ℝ => s⁻¹) '' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨s, hs, hsx⟩ => hsx ▸ inv_pos.mpr hs, fun hx => ⟨x⁻¹, inv_pos.mpr hx, inv_inv x⟩⟩
  have hT1i := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hinvd hinvinj
    (fun t : ℝ => ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 (t : ℂ) r)
  have hT1e := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hinvd hinvinj
    (fun t : ℝ => ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 (t : ℂ) r)
  rw [hinvimg] at hT1i hT1e
  have hpt : EqOn (fun s : ℝ => |(-(s ^ 2)⁻¹ : ℝ)| •
      (ckmrvEightKernel (imagPt y) (imagPt s⁻¹) * gaussHat 8 ((s⁻¹ : ℝ) : ℂ) r))
      (fun s : ℝ => contourF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
        contourF y (r ^ 2) (1 + I * s) + cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
        contourF y (r ^ 2) (I * s - 1)) / 2) (Ioi 0) :=
    fun s hs => kernel_gaussHat_inv y r hs
  have iA : IntegrableOn (fun s : ℝ => (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * Gp (1 + I * s) +
      cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * Gm (I * s - 1)) / 2) (Ioi 0) :=
    Integrable.div_const (Integrable.add (Integrable.const_mul iGp1 _)
      (Integrable.const_mul iGm1 _)) 2
  have iT1 : IntegrableOn (fun t : ℝ => ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 (t : ℂ) r) (Ioi 0) := by
    refine hT1i.mpr (IntegrableOn.congr_fun ?_ (fun s hs => (hpt hs).symm) measurableSet_Ioi)
    refine Integrable.congr (Integrable.sub iF0 iA) ?_
    filter_upwards [aeT1] with s hs
    simp only [Pi.sub_apply]
    exact hs.symm
  have eT1 : 2 * (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
      gaussHat 8 (t : ℂ) r) =
      2 * (∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (I * t)) -
        cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (∫ t in Ioi (0 : ℝ), Gp (1 + I * t)) -
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * ∫ t in Ioi (0 : ℝ), Gm (I * t - 1) := by
    rw [hT1e, setIntegral_congr_fun measurableSet_Ioi hpt, integral_congr_ae aeT1,
      integral_sub iF0 iA, integral_div, integral_add (Integrable.const_mul iGp1 _)
        (Integrable.const_mul iGm1 _), integral_const_mul, integral_const_mul]
    ring
  have e1 : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
        (2 * gaussHat 8 t r - gaussHat 8 (t - I) r - gaussHat 8 (t + I) r)) =
      2 * (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 (t : ℂ) r) -
        (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) *
          gaussHat 8 ((t : ℂ) - I) r) -
        ∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 ((t : ℂ) + I) r := by
    have iT12 : IntegrableOn (fun t : ℝ =>
        2 * (ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 (t : ℂ) r) -
          ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 ((t : ℂ) - I) r) (Ioi 0) :=
      Integrable.sub (Integrable.const_mul iT1 2) iT2
    rw [← integral_const_mul, ← integral_sub (Integrable.const_mul iT1 2) iT2,
      ← integral_sub iT12 iT3]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  -- the explicit principal parts: `Q' = −2π`
  have e9 : (∫ t in Ioi (0 : ℝ), principalK (sigmaC y + 1) (I * t)) -
      (∫ t in Ioi (0 : ℝ), principalK (sigmaC y - 1) (I * t)) =
        -4 * ((Real.arctan y⁻¹ : ℝ) : ℂ) := by
    rw [← integral_sub ikp ikm, sigmaC_eq hy, integral_principalK_sub_imag]
    simp
  have e10 : (∫ t in Ioi (0 : ℝ), principalK (I * y + 1) (I * t)) -
      (∫ t in Ioi (0 : ℝ), principalK (I * y - 1) (I * t)) = -4 * ((Real.arctan y : ℝ) : ℂ) := by
    rw [← integral_sub iJp iJm, integral_principalK_sub_imag]
    simp
  have e13 : ((Real.arctan y⁻¹ : ℝ) : ℂ) + ((Real.arctan y : ℝ) : ℂ) = π / 2 := by
    rw [Real.arctan_inv_of_pos hy]; push_cast; ring
  -- the Gaussian
  have hI4 : I ^ 4 = (1 : ℂ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Complex.I_sq]; norm_num
  have hpm2 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hπ2 : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hσ4 : sigmaC y ^ 4 = ((y⁻¹ ^ 4 : ℝ) : ℂ) := by
    rw [sigmaC_eq hy, mul_pow, hI4, one_mul]; norm_cast
  have hEσ : gaussE (r ^ 2) (sigmaC y) = ((Real.exp (-(π / y) * r ^ 2) : ℝ) : ℂ) := by
    rw [sigmaC_eq hy, gaussE_I_mul, Complex.ofReal_exp]; congr 1; push_cast; ring
  have e14 : cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * cPlus y (r ^ 2) * (2 * π) =
      ((y⁻¹ ^ 4 : ℝ) : ℂ) * (Real.exp (-(π / y) * r ^ 2) : ℂ) := by
    rw [cPlus, gaussE_add, gaussE_one,
      show ∀ A B c e : ℂ, e * (A / c * B) * c = (A / c * c) * (B * e) from
        fun _ _ _ _ => by ring, div_mul_cancel₀ _ hπ2, hσ4, hEσ]
    linear_combination (((y⁻¹ ^ 4 : ℝ) : ℂ) * ((Real.exp (-(π / y) * r ^ 2) : ℝ) : ℂ)) * hpm2
  -- the right-hand side
  have hsin : ((4 * Real.sin (π * r ^ 2 / 2) ^ 2 : ℝ) : ℂ) =
      2 - cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) - cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) := by
    have h1 : Real.sin (π * r ^ 2 / 2) ^ 2 = 1 / 2 - Real.cos (π * r ^ 2) / 2 := by
      rw [Real.sin_sq_eq_half_sub, show 2 * (π * r ^ 2 / 2) = π * r ^ 2 by ring]
    have h2 := Complex.two_cos ((π * r ^ 2 : ℝ) : ℂ)
    have h3 : cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) = cexp (((π * r ^ 2 : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    have h4 : cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) = cexp (-((π * r ^ 2 : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    have h5 : ((4 * (1 / 2 - Real.cos (π * r ^ 2) / 2) : ℝ) : ℂ) =
        2 - 2 * Complex.cos ((π * r ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cos]; push_cast; ring
    rw [h1, h3, h4, h5]
    linear_combination -h2
  have hF0eq : (∫ t in Ioi (0 : ℝ), ckmrvEightHatKernel (imagPt y) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) = ∫ t in Ioi (0 : ℝ), contourF y (r ^ 2) (I * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [contourF]
    rw [rightC_I_mul _ _ ht, gaussE_I_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [hsin, hF0eq]
  exact contour_algebra e1 eT1 e3 e4 e5 e6 e7 e8 e9 e10 rfl e11 e13 e14

/-! ## The Fourier transform of `φ` and the `E8` certificate -/

/-- The Fourier transform of `φ = 4 sin²(π|x|²/2) ∫ 𝒦(iβ, it) e^{−π|x|²t} dt` in dimension eight. -/
theorem fourier_ckmrvEightKernel_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) {φ : Ambient 8 → ℂ}
    (hφ : ∀ x : Ambient 8, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, ckmrvEightKernel (imagPt β) (imagPt t) * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ))
    (w : Ambient 8) :
    𝓕 φ w = ∫ t in Ioi 0, ckmrvEightKernel (imagPt β) (imagPt t) *
      (2 * gaussHat 8 t ‖w‖ - gaussHat 8 (t - I) ‖w‖ - gaussHat 8 (t + I) ‖w‖) := by
  obtain ⟨gp, hgp, hgpK⟩ := exists_ckmrvEightPlus_axis hβ hβ1
  obtain ⟨gm, hgm, hgmK⟩ := exists_ckmrvEightMinus_axis hβ hβ1
  have hd : Module.finrank ℝ (Ambient 8) = 8 := by simp [Ambient]
  refine fourier_of_axis_eight hd (g := fun t => (1 / 2 : ℂ) * (gp t + gm t))
    (K := fun t => ckmrvEightKernel (imagPt β) (imagPt t)) (β := β)
    (continuousOn_const.mul (hgp.add hgm))
    (((isBigO_eightPlusAxis_zero hβ hgpK).add (isBigO_eightMinusAxis_zero hβ hgmK)).const_mul_left _)
    (((isBigO_eightPlusAxis_atTop hgpK).add (isBigO_eightMinusAxis_atTop hgmK)).const_mul_left _)
    (fun x h1 h2 => ?_) hφ w
  rw [hgpK x h1 h2, hgmK x h1 h2, ckmrvEightKernel]
  ring

/-- **The `E8` Gaussian certificate, given the positivity (6.4)(1)**: for `0 < α ≠ π`, if
`𝒦̂(iq, it) ≥ 0` for all `q, t > 0`, then `e^{−α|·|²} + φ` is a Gaussian Schwartz certificate for
`E8`. The identity (**) is now proved (`ckmrv_contour_identity`). -/
theorem e8_exists_gaussianSchwartzCertificate {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (hpos : ∀ q t : ℝ, 0 < q → 0 < t → 0 ≤ (ckmrvEightHatKernel (imagPt q) (imagPt t)).re) :
    ∃ φ : SchwartzMap (Ambient 8) ℂ,
      GaussianSchwartzCertificate e8Set α (gaussianSchwartz hα + φ) := by
  obtain ⟨φ, hφ, hcert⟩ := e8_exists_gaussianSchwartzCertificate_of_pos hα hαπ hpos
  have hβ : 0 < α / π := div_pos hα Real.pi_pos
  have hβ1 : α / π ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq Real.pi_ne_zero).mp h)
  refine ⟨φ, hcert fun ξ hξ => ?_⟩
  rw [fourier_ckmrvEightKernel_axis hβ hβ1 hφ ξ]
  have h := ckmrv_contour_identity hβ hβ1 (r := ‖ξ‖) (norm_ne_zero_iff.mpr hξ)
  have hg1 : (α / π)⁻¹ = π / α := inv_div α π
  have hg2 : π / (α / π) = π ^ 2 / α := by rw [div_div_eq_mul_div, sq]
  rw [hg1, hg2] at h
  rw [gaussianKernel]
  exact h

end E8Leech
