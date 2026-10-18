import E8Leech.CKMRVContourCauchy
import E8Leech.CKMRVKernelReal
import E8Leech.CKMRVFourier
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Assembly of the CKMRV identity (**) in dimension eight

The semicircles of the two ideal triangles are reparametrized by `t ∈ (0, ∞)`:
`v(t) = it/(1+it)` (centre `1/2`) and `u(t) = it/(1−it)` (centre `−1/2`). Pointwise:

* `𝒦(iy, it)(t ∓ i)⁻⁴ e^{−πρ/(t ∓ i)} = −i e^{∓iπρ} f(v or u) (v' or u')` (the `STS` / `TST` forms);
* `2s²𝒦(iy, i/s) = 2𝒦̂(is) − 𝒦̂(is + 1) − 𝒦̂(is − 1)` (the right relation one);
* `k₊(v)v' = i·k(−1 + iy)(it)`, `k₋(u)u' = i·k(1 + iy)(it)` (Möbius pull-back of principal parts);
* `∫₀^∞ (k(ia + 1) − k(ia − 1))(it) dt = −4 arctan a`.
-/

namespace E8Leech

open Complex Filter Topology Set MeasureTheory
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The two semicircles parametrized by `t ∈ (0, ∞)` -/

/-- `v(t) = it/(1+it)` runs over the semicircle `C` (centre `1/2`) from `0` to `1`. -/
noncomputable def vPath (t : ℝ) : ℂ := I * t / (1 + I * t)

/-- `v'(t)`. -/
noncomputable def vPath' (t : ℝ) : ℂ := I / (1 + I * t) ^ 2

/-- `u(t) = it/(1−it)` runs over the semicircle `C − 1` (centre `−1/2`) from `0` to `−1`. -/
noncomputable def uPath (t : ℝ) : ℂ := I * t / (1 - I * t)

/-- `u'(t)`. -/
noncomputable def uPath' (t : ℝ) : ℂ := I / (1 - I * t) ^ 2

theorem one_add_I_mul_ne_zero (t : ℝ) : (1 : ℂ) + I * t ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem one_sub_I_mul_ne_zero (t : ℝ) : (1 : ℂ) - I * t ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem ofReal_one_add_sq (t : ℝ) : ((1 + t ^ 2 : ℝ) : ℂ) = (1 + I * t) * (1 - I * t) := by
  push_cast
  linear_combination (t : ℂ) ^ 2 * Complex.I_sq

theorem cexp_arctan_mul_I (t : ℝ) :
    cexp ((Real.arctan t : ℂ) * I) = (1 + I * t) / (Real.sqrt (1 + t ^ 2) : ℂ) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_arctan,
    Real.sin_arctan]
  push_cast
  ring

theorem cexp_two_arctan_mul_I (t : ℝ) :
    cexp (((2 * Real.arctan t : ℝ) : ℂ) * I) = (1 + I * t) / (1 - I * t) := by
  have hs : ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hs0 : ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have e : ((2 * Real.arctan t : ℝ) : ℂ) * I =
      (Real.arctan t : ℂ) * I + (Real.arctan t : ℂ) * I := by push_cast; ring
  rw [e, Complex.exp_add, cexp_arctan_mul_I, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero hs0 hs0) (one_sub_I_mul_ne_zero t)]
  linear_combination (-(1 + I * t)) * hs - (1 + I * t) * (t : ℂ) ^ 2 * Complex.I_sq

theorem cexp_pi_sub_two_arctan_mul_I (t : ℝ) :
    cexp (((π - 2 * Real.arctan t : ℝ) : ℂ) * I) = -((1 - I * t) / (1 + I * t)) := by
  have e : ((π - 2 * Real.arctan t : ℝ) : ℂ) * I = π * I - ((2 * Real.arctan t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e, Complex.exp_sub, Complex.exp_pi_mul_I, cexp_two_arctan_mul_I, neg_div, one_div_div]

theorem image_two_arctan : (fun t : ℝ => 2 * Real.arctan t) '' Ioi 0 = Ioo 0 π := by
  ext θ
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by linarith [Real.arctan_pos.mpr ht], by linarith [Real.arctan_lt_pi_div_two t]⟩
  · rintro ⟨h0, hπ⟩
    refine ⟨Real.tan (θ / 2), Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith), ?_⟩
    rw [Real.arctan_tan (by linarith) (by linarith)]
    ring

theorem image_pi_sub_two_arctan : (fun t : ℝ => π - 2 * Real.arctan t) '' Ioi 0 = Ioo 0 π := by
  ext θ
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by linarith [Real.arctan_lt_pi_div_two t], by linarith [Real.arctan_pos.mpr ht]⟩
  · rintro ⟨h0, hπ⟩
    refine ⟨Real.tan ((π - θ) / 2),
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith), ?_⟩
    rw [Real.arctan_tan (by linarith) (by linarith)]
    ring

theorem semicircleIntegrand_pi_sub_two_arctan (g : ℂ → ℂ) (t : ℝ) :
    |(-(2 / (1 + t ^ 2)) : ℝ)| • semicircleIntegrand g (π - 2 * Real.arctan t) =
      -(g (vPath t) * vPath' t) := by
  have h1 := one_add_I_mul_ne_zero t
  have h2 := one_sub_I_mul_ne_zero t
  have hpos : (0 : ℝ) < 2 / (1 + t ^ 2) := by positivity
  rw [abs_neg, abs_of_pos hpos, semicircleIntegrand, cexp_pi_sub_two_arctan_mul_I,
    Complex.real_smul]
  have hv : (1 / 2 : ℂ) + -((1 - I * t) / (1 + I * t)) / 2 = vPath t := by
    rw [vPath]; field_simp; ring
  have hc : ((2 / (1 + t ^ 2) : ℝ) : ℂ) * (I / 2 * -((1 - I * t) / (1 + I * t))) =
      -vPath' t := by
    rw [Complex.ofReal_div, ofReal_one_add_sq, vPath']; push_cast; field_simp
  rw [hv]
  linear_combination g (vPath t) * hc

theorem semicircleIntegrand_two_arctan (g : ℂ → ℂ) (t : ℝ) :
    |(2 / (1 + t ^ 2) : ℝ)| • semicircleIntegrand (fun z => g (z - 1)) (2 * Real.arctan t) =
      g (uPath t) * uPath' t := by
  have h1 := one_add_I_mul_ne_zero t
  have h2 := one_sub_I_mul_ne_zero t
  have hpos : (0 : ℝ) < 2 / (1 + t ^ 2) := by positivity
  rw [abs_of_pos hpos, semicircleIntegrand, cexp_two_arctan_mul_I, Complex.real_smul]
  have hu : (1 / 2 : ℂ) + (1 + I * t) / (1 - I * t) / 2 - 1 = uPath t := by
    rw [uPath]; field_simp; ring
  have hc : ((2 / (1 + t ^ 2) : ℝ) : ℂ) * (I / 2 * ((1 + I * t) / (1 - I * t))) = uPath' t := by
    rw [Complex.ofReal_div, ofReal_one_add_sq, uPath']; push_cast; field_simp
  simp only [hu]
  linear_combination g (uPath t) * hc

/-- **The semicircle `C` in the `t`-parametrization** (`θ = π − 2 arctan t`). -/
theorem semicircle_conv_v (g : ℂ → ℂ) :
    (IntegrableOn (semicircleIntegrand g) (Ioo 0 π) ↔
      IntegrableOn (fun t : ℝ => g (vPath t) * vPath' t) (Ioi 0)) ∧
    ∫ θ in Ioo 0 π, semicircleIntegrand g θ = -∫ t in Ioi 0, g (vPath t) * vPath' t := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => π - 2 * Real.arctan t)
      (-(2 / (1 + t ^ 2))) (Ioi 0) t := fun t _ => by
    have h := ((Real.hasDerivAt_arctan t).const_mul 2).const_sub π
    have e : -(2 * (1 / (1 + t ^ 2))) = -(2 / (1 + t ^ 2)) := by ring
    rw [e] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => π - 2 * Real.arctan t) (Ioi 0) := fun a _ b _ h => by
    simp only at h
    exact Real.arctan_injective (by linarith)
  have hk : EqOn (fun t : ℝ => |(-(2 / (1 + t ^ 2)) : ℝ)| •
      semicircleIntegrand g (π - 2 * Real.arctan t))
      (fun t => -(g (vPath t) * vPath' t)) (Ioi 0) := fun t _ =>
    semicircleIntegrand_pi_sub_two_arctan g t
  have h1 := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj
    (semicircleIntegrand g)
  have h2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj
    (semicircleIntegrand g)
  rw [image_pi_sub_two_arctan] at h1 h2
  refine ⟨h1.trans ((integrableOn_congr_fun hk measurableSet_Ioi).trans
    (integrable_neg_iff (f := fun t : ℝ => g (vPath t) * vPath' t))), ?_⟩
  rw [h2, setIntegral_congr_fun measurableSet_Ioi hk, integral_neg]

/-- **The semicircle `C − 1` in the `t`-parametrization** (`θ = 2 arctan t`). -/
theorem semicircle_conv_u (g : ℂ → ℂ) :
    (IntegrableOn (semicircleIntegrand (fun z => g (z - 1))) (Ioo 0 π) ↔
      IntegrableOn (fun t : ℝ => g (uPath t) * uPath' t) (Ioi 0)) ∧
    ∫ θ in Ioo 0 π, semicircleIntegrand (fun z => g (z - 1)) θ =
      ∫ t in Ioi 0, g (uPath t) * uPath' t := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => 2 * Real.arctan t)
      (2 / (1 + t ^ 2)) (Ioi 0) t := fun t _ => by
    have h := (Real.hasDerivAt_arctan t).const_mul 2
    have e : 2 * (1 / (1 + t ^ 2)) = 2 / (1 + t ^ 2) := by ring
    rw [e] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => 2 * Real.arctan t) (Ioi 0) := fun a _ b _ h => by
    simp only at h
    exact Real.arctan_injective (by linarith)
  have hk : EqOn (fun t : ℝ => |(2 / (1 + t ^ 2) : ℝ)| •
      semicircleIntegrand (fun z => g (z - 1)) (2 * Real.arctan t))
      (fun t => g (uPath t) * uPath' t) (Ioi 0) := fun t _ =>
    semicircleIntegrand_two_arctan g t
  have h1 := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj
    (semicircleIntegrand (fun z => g (z - 1)))
  have h2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj
    (semicircleIntegrand (fun z => g (z - 1)))
  rw [image_two_arctan] at h1 h2
  exact ⟨h1.trans (integrableOn_congr_fun hk measurableSet_Ioi),
    by rw [h2, setIntegral_congr_fun measurableSet_Ioi hk]⟩

/-- A function bounded by `C/(1 + Im z)²` and continuous on the closed triangle is integrable on
the semicircle. -/
theorem integrableOn_semicircleIntegrand {g : ℂ → ℂ} (hgc : ContinuousOn g idealTriangleCl)
    {C : ℝ} (hC : ∀ z ∈ idealTriangleCl, ‖g z‖ ≤ C / (1 + z.im) ^ 2) :
    IntegrableOn (semicircleIntegrand g) (Ioo 0 π) := by
  have hC0 : 0 ≤ C := by
    have h := hC _ (one_add_I_mul_mem one_pos)
    have hpos : 0 < (1 + ((1 : ℂ) + I * (1 : ℝ)).im) ^ 2 := by norm_num
    have := (norm_nonneg _).trans h
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hpos)
  have hSc : ContinuousOn (semicircleIntegrand g) (Ioo 0 π) := by
    have hp : Continuous fun θ : ℝ => (1 / 2 : ℂ) + cexp (θ * I) / 2 := by fun_prop
    have h := continuousOn_comp_line hgc hp (T := Ioo 0 π) fun θ hθ => semicircle_mem hθ.1 hθ.2
    exact (Continuous.continuousOn (by fun_prop)).mul h
  have hSb : ∀ θ ∈ Ioo (0 : ℝ) π, ‖semicircleIntegrand g θ‖ ≤ C / 2 := fun θ hθ => by
    simp only [semicircleIntegrand, norm_mul, norm_div, Complex.norm_I,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_ofNat]
    have hm := semicircle_mem hθ.1 hθ.2
    have h := hC _ hm
    have h1 : 1 ≤ (1 + ((1 / 2 : ℂ) + cexp (θ * I) / 2).im) ^ 2 := by
      have := hm.1
      nlinarith
    have : C / (1 + ((1 / 2 : ℂ) + cexp (θ * I) / 2).im) ^ 2 ≤ C := div_le_self hC0 h1
    linarith
  refine Integrable.mono' (integrable_const (C / 2)) (hSc.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hSb x hx

/-! ## Simplifying `gaussHat 8` and `gaussE` -/

theorem gaussHat_eight {a : ℂ} (ha : a ≠ 0) (r : ℝ) :
    gaussHat 8 a r = (a ^ 4)⁻¹ * cexp (-(π * (r : ℂ) ^ 2) / a) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h8 : ((8 : ℕ) : ℂ) / 2 = ((4 : ℕ) : ℂ) := by norm_num
  rw [gaussHat, h8, Complex.cpow_natCast, div_mul_eq_div_div, div_self hπ, one_div, inv_pow]
  congr 2
  rw [div_eq_div_iff (mul_ne_zero hπ ha) ha]
  ring

theorem gaussE_I_mul (ρ s : ℝ) : gaussE ρ (I * s) = cexp (-((π : ℂ) * ρ * s)) := by
  rw [gaussE]
  congr 1
  linear_combination ((π : ℂ) * ρ * s) * Complex.I_sq

theorem gaussE_one_add (ρ : ℝ) (z : ℂ) :
    gaussE ρ (1 + z) = cexp (π * I * ρ) * gaussE ρ z := by
  simp only [gaussE, ← Complex.exp_add]; ring_nf

theorem gaussE_sub_one (ρ : ℝ) (z : ℂ) :
    gaussE ρ (z - 1) = cexp (-(π * I * ρ)) * gaussE ρ z := by
  simp only [gaussE, ← Complex.exp_add]; ring_nf

theorem cexp_neg_mul_cexp (w : ℂ) : cexp (-w) * cexp w = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-! ## Points of the paths -/

theorem rightC_I_mul (K : ℍ → ℍ → ℂ) (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    rightC K τ (I * t) = K τ (imagPt t) := by
  simp only [rightC]; rw [← coe_imagPt ht, ofComplex_apply]

theorem rightC_coe (K : ℍ → ℍ → ℂ) (τ z : ℍ) : rightC K τ (z : ℂ) = K τ z := by
  simp only [rightC, ofComplex_apply]

theorem im_vPath (t : ℝ) : (vPath t).im = t / (1 + t ^ 2) := by
  rw [vPath, Complex.div_im]
  simp [Complex.normSq_apply]
  ring

theorem im_uPath (t : ℝ) : (uPath t).im = t / (1 + t ^ 2) := by
  rw [uPath, Complex.div_im]
  simp [Complex.normSq_apply]
  ring

theorem vPath_div_one_sub (t : ℝ) : vPath t / (1 - vPath t) = I * t := by
  have h1 := one_add_I_mul_ne_zero t
  rw [vPath]
  field_simp
  ring

theorem uPath_div_add_one (t : ℝ) : uPath t / (uPath t + 1) = I * t := by
  have h1 := one_sub_I_mul_ne_zero t
  rw [uPath]
  field_simp
  ring

theorem vPath_sub_one (t : ℝ) : vPath t - 1 = -1 / (1 + I * t) := by
  have h1 := one_add_I_mul_ne_zero t
  rw [vPath]; field_simp; ring

theorem uPath_add_one (t : ℝ) : uPath t + 1 = 1 / (1 - I * t) := by
  have h1 := one_sub_I_mul_ne_zero t
  rw [uPath]; field_simp; ring

/-! ## The `t ∓ i` terms are semicircle integrals -/

/-- `𝒦(τ, it) (t − i)⁻⁴ e^{−πρ/(t−i)} = −i e^{−iπρ} f(v) v'` (from `𝒦̂ = 𝒦 |_{−2} STS`). -/
theorem kernel_gaussHat_sub_I (y r : ℝ) {t : ℝ} (ht : 0 < t) :
    ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 ((t : ℂ) - I) r =
      -I * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * (contourF y (r ^ 2) (vPath t) * vPath' t) := by
  have hD := one_add_I_mul_ne_zero t
  have htI : (t : ℂ) - I = -I * (1 + I * t) := by linear_combination (t : ℂ) * Complex.I_sq
  have hne : (t : ℂ) - I ≠ 0 := by rw [htI]; exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hD
  have hvim : 0 < (vPath t).im := by rw [im_vPath]; positivity
  have hexp : cexp (-(π * (r : ℂ) ^ 2) / ((t : ℂ) - I)) =
      cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) * gaussE (r ^ 2) (vPath t) := by
    rw [gaussE, ← Complex.exp_add]
    congr 1
    have e1 : -(π * (r : ℂ) ^ 2) / ((t : ℂ) - I) = -(π * I * (r : ℂ) ^ 2) / (1 + I * t) := by
      rw [htI, div_eq_div_iff (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hD) hD]
      linear_combination (-((π : ℂ) * (r : ℂ) ^ 2 * (1 + I * t))) * Complex.I_sq
    rw [e1, vPath]
    push_cast
    field_simp
    ring
  have h4 : (-I * (1 + I * (t : ℂ))) ^ 4 = (1 + I * t) ^ 4 := by
    linear_combination (1 + I * (t : ℂ)) ^ 4 * (I ^ 2 - 1) * Complex.I_sq
  rw [gaussHat_eight hne, hexp, contourF, rightC_hat_eq_STS hvim, vPath_div_one_sub,
    rightC_I_mul _ _ ht, htI, h4, vPath_sub_one, vPath']
  generalize (1 + I * (t : ℂ)) = D
  linear_combination (ckmrvEightKernel (imagPt y) (imagPt t) * cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
    gaussE (r ^ 2) (vPath t) * (D ^ 4)⁻¹) * Complex.I_sq

/-- `𝒦(τ, it) (t + i)⁻⁴ e^{−πρ/(t+i)} = −i e^{iπρ} f(u) u'` (from `𝒦̂ = 𝒦 |_{−2} TST`). -/
theorem kernel_gaussHat_add_I (y r : ℝ) {t : ℝ} (ht : 0 < t) :
    ckmrvEightKernel (imagPt y) (imagPt t) * gaussHat 8 ((t : ℂ) + I) r =
      -I * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * (contourF y (r ^ 2) (uPath t) * uPath' t) := by
  have hE := one_sub_I_mul_ne_zero t
  have htI : (t : ℂ) + I = I * (1 - I * t) := by linear_combination (t : ℂ) * Complex.I_sq
  have hne : (t : ℂ) + I ≠ 0 := by rw [htI]; exact mul_ne_zero I_ne_zero hE
  have huim : 0 < (uPath t).im := by rw [im_uPath]; positivity
  have hexp : cexp (-(π * (r : ℂ) ^ 2) / ((t : ℂ) + I)) =
      cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * gaussE (r ^ 2) (uPath t) := by
    rw [gaussE, ← Complex.exp_add]
    congr 1
    have e1 : -(π * (r : ℂ) ^ 2) / ((t : ℂ) + I) = π * I * (r : ℂ) ^ 2 / (1 - I * t) := by
      rw [htI, div_eq_div_iff (mul_ne_zero I_ne_zero hE) hE]
      linear_combination (-((π : ℂ) * (r : ℂ) ^ 2 * (1 - I * t))) * Complex.I_sq
    rw [e1, uPath]
    push_cast
    field_simp
    ring
  have h4 : (I * (1 - I * (t : ℂ))) ^ 4 = (1 - I * t) ^ 4 := by
    linear_combination (1 - I * (t : ℂ)) ^ 4 * (I ^ 2 - 1) * Complex.I_sq
  have hT := rightC_hat_eq_TST (τ := imagPt y) huim
  rw [gaussHat_eight hne, hexp, contourF, hT, uPath_div_add_one, rightC_I_mul _ _ ht, htI, h4,
    uPath_add_one, uPath']
  generalize (1 - I * (t : ℂ)) = E
  linear_combination (ckmrvEightKernel (imagPt y) (imagPt t) * cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) *
    gaussE (r ^ 2) (uPath t) * (E ^ 4)⁻¹) * Complex.I_sq

/-! ## The `2t⁻⁴e^{−πρ/t}` term: `t ↦ 1/s` and the right relation one -/

theorem slash_T_inv_apply' (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] ModularGroup.T⁻¹) z = f (ModularGroup.T⁻¹ • z) := by
  have h := ckmrv_slash_T_apply_smul k (f ∣[k] ModularGroup.T⁻¹) (ModularGroup.T⁻¹ • z)
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one, smul_inv_smul] at h
  exact h.symm

theorem coe_T_inv_smul' (z : ℍ) : ((ModularGroup.T⁻¹ • z : ℍ) : ℂ) = (z : ℂ) - 1 := by
  have h := coe_T_smul (ModularGroup.T⁻¹ • z)
  rw [smul_inv_smul] at h
  rw [h]; ring

/-- `2s²𝒦(τ, i/s) = 2𝒦̂(τ, is) − 𝒦̂(τ, is + 1) − 𝒦̂(τ, is − 1)`. -/
theorem kernel_imagPt_inv (τ : ℍ) {s : ℝ} (hs : 0 < s) :
    2 * (s : ℂ) ^ 2 * ckmrvEightKernel τ (imagPt s⁻¹) =
      2 * rightC ckmrvEightHatKernel τ (I * s) - rightC ckmrvEightHatKernel τ (1 + I * s) -
        rightC ckmrvEightHatKernel τ (I * s - 1) := by
  have hP := congrFun (ckmrvEightPlusKernel_right_rel_one τ) (imagPt s)
  have hM := congrFun (ckmrvEightMinusKernel_right_rel_one τ) (imagPt s)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    ckmrv_slash_T_apply_smul, slash_T_inv_apply', ckmrv_slash_S_apply, neg_neg, zpow_two,
    S_smul_imagPt hs, coe_imagPt hs] at hP hM
  have e2 : (1 : ℂ) + I * s = ((ModularGroup.T • imagPt s : ℍ) : ℂ) := by
    rw [coe_T_smul, coe_imagPt hs]; ring
  have e3 : I * (s : ℂ) - 1 = ((ModularGroup.T⁻¹ • imagPt s : ℍ) : ℂ) := by
    rw [coe_T_inv_smul', coe_imagPt hs]
  rw [rightC_I_mul _ _ hs, e2, e3, rightC_coe, rightC_coe]
  simp only [ckmrvEightKernel, ckmrvEightHatKernel]
  linear_combination (hP - hM) / 2 + (s : ℂ) ^ 2 * (ckmrvEightPlusKernel τ (imagPt s⁻¹) +
    ckmrvEightMinusKernel τ (imagPt s⁻¹)) * Complex.I_sq

/-- The `t ↦ 1/s` integrand: `s⁻²·𝒦(τ, i/s)·gaussHat(1/s) = f(is) − (e^{−iπρ}f(1+is) + e^{iπρ}f(is−1))/2`. -/
theorem kernel_gaussHat_inv (y r : ℝ) {s : ℝ} (hs : 0 < s) :
    |(-(s ^ 2)⁻¹ : ℝ)| • (ckmrvEightKernel (imagPt y) (imagPt s⁻¹) *
        gaussHat 8 ((s⁻¹ : ℝ) : ℂ) r) =
      contourF y (r ^ 2) (I * s) - (cexp (-(π * I * ((r ^ 2 : ℝ) : ℂ))) *
          contourF y (r ^ 2) (1 + I * s) +
        cexp (π * I * ((r ^ 2 : ℝ) : ℂ)) * contourF y (r ^ 2) (I * s - 1)) / 2 := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsi : ((s⁻¹ : ℝ) : ℂ) ≠ 0 := by push_cast; exact inv_ne_zero hs0
  have hK := kernel_imagPt_inv (imagPt y) hs
  have hX : gaussE (r ^ 2) (I * s) = cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) :=
    gaussE_I_mul _ _
  have hg : cexp (-(π * (r : ℂ) ^ 2) / ((s⁻¹ : ℝ) : ℂ)) =
      cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) := by
    congr 1; rw [Complex.ofReal_inv, div_inv_eq_mul]; push_cast; ring
  have hss : (((s ^ 2)⁻¹ : ℝ) : ℂ) * ((((s⁻¹ : ℝ) : ℂ)) ^ 4)⁻¹ = (s : ℂ) ^ 2 := by
    push_cast
    rw [inv_pow, inv_inv, inv_mul_eq_div, div_eq_iff (pow_ne_zero 2 hs0)]
    ring
  have hpm := cexp_neg_mul_cexp (π * I * ((r ^ 2 : ℝ) : ℂ))
  rw [abs_neg, abs_of_pos (by positivity), Complex.real_smul, gaussHat_eight hsi, hg]
  simp only [contourF, gaussE_one_add, gaussE_sub_one, hX]
  linear_combination (cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) / 2) * hK +
    (cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s)) / 2 *
      (rightC ckmrvEightHatKernel (imagPt y) (1 + I * s) +
        rightC ckmrvEightHatKernel (imagPt y) (I * s - 1))) * hpm +
    (ckmrvEightKernel (imagPt y) (imagPt s⁻¹) * cexp (-((π : ℂ) * ((r ^ 2 : ℝ) : ℂ) * s))) * hss

end E8Leech
