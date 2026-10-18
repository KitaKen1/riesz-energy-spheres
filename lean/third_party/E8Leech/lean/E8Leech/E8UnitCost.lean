import E8Leech.CKMRVContourFinal
import E8Leech.NormalizedLaplaceSlack
import E8Leech.AeCertificates
import E8Leech.PositiveMixtureCertificates

/-!
# The `E8` analytic unit-cost input from the kernel inequalities

With (**) proved (`ckmrv_contour_identity`), the `E8` Gaussian certificates exist for every
`0 < α ≠ π` as soon as `𝒦̂(iq, it) ≥ 0` ((6.4)(1)). This file wires them into
`AnalyticUnitCostInput e8Set s √2`.

The downstream interface asks for continuity of the slack profile on a compact rectangle only to
extract a positive lower bound. Here the lower bound is produced directly from
* `𝒦̂ ≥ 0` everywhere,
* a uniform positive lower bound on the block `[3,4] × [1,2]`,
* a uniform linear lower bound `𝒦̂(iq, it) ≥ c t` for large `t` (`q ∈ [3,4]`),
so that neither joint continuity nor measurability of the kernel integrals is needed: the
measurable potential used in the end is an explicit quadratic minorant of the slack.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter Topology
open UpperHalfPlane hiding I
open scoped ENNReal Real SchwartzMap FourierTransform

/-! ## A slack interface with explicit lower bounds -/

theorem uniform_quadratic_slack_of_laplace_lower_bounds {a b r : ℝ}
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4) (φ K : ℝ × ℝ → ℝ)
    {A : ℝ} (hA : 0 < A) (hAlower : ∀ α ∈ Icc a b, ∀ u ∈ Icc 0 (7 / 8 * r), A ≤ φ (α, u))
    {B : ℝ} (hB : 0 < B) (hBlower : ∀ α ∈ Icc a b, ∀ t ∈ Icc (1 : ℝ) 2, B ≤ K (α, t))
    (hKnonneg : ∀ α ∈ Icc a b, ∀ t : ℝ, 0 < t → 0 ≤ K (α, t))
    (hint : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun t => K (α, t) * Real.exp (-Real.pi * u ^ 2 * t)) (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), K (α, t) * Real.exp (-Real.pi * u ^ 2 * t)) :
    ∃ k : ℝ, 0 < k ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ∀ α ∈ Icc a b, ∀ u : ℝ, 0 ≤ u → u < r * (1 - t) → k * t ^ 2 ≤ φ (α, u) := by
  have hB' : 0 < B * Real.exp (-8 * Real.pi) := mul_pos hB (Real.exp_pos _)
  refine ⟨min (4 * A) (4 * (B * Real.exp (-8 * Real.pi)) * r ^ 4),
    lt_min (by positivity) (by positivity), ?_⟩
  intro t ht hhalf α hα u hu hclose
  apply quadratic_slack_of_sine_factor_bounds hA hB' hr hroot
    (fun u => φ (α, u))
    (fun u => ∫ v in Ioi (0 : ℝ), K (α, v) * Real.exp (-Real.pi * u ^ 2 * v))
    (hAlower α hα) ?_ (hfactor α hα) ht hhalf hu hclose
  intro v hv
  apply laplace_factor_lower_from_unit_block ?_ (hKnonneg α hα) (hBlower α hα) (hint α hα v hv)
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hvsq : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv0 hv.2 2
  rcases hroot with h | h <;> nlinarith

/-! ## Elementary lower bounds -/

/-- Jordan's inequality on `[a, 49π/64]`. -/
theorem sin_ge_min_of_mem {x a : ℝ} (ha : 0 < a) (hax : a ≤ x) (hx : x ≤ 49 * π / 64) :
    min (2 * a / π) (15 / 32) ≤ Real.sin x := by
  have hπ := Real.pi_pos
  rcases le_or_gt x (π / 2) with h | h
  · have hj := Real.mul_le_sin (by linarith) h
    have h2 : 2 * a / π ≤ 2 / π * x := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) hπ.le
    exact (min_le_left _ _).trans (h2.trans hj)
  · rw [← Real.sin_pi_sub]
    have hj := Real.mul_le_sin (x := π - x) (by linarith) (by linarith)
    have h2 : (15 / 32 : ℝ) ≤ 2 / π * (π - x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
      linarith
    exact (min_le_right _ _).trans (h2.trans hj)

/-- A Laplace transform of a nonnegative function growing at least linearly. -/
theorem laplace_lower_of_linear {K : ℝ → ℝ} {c₁ T ε S : ℝ} (hc₁ : 0 < c₁) (hε : 0 < ε)
    (hK0 : ∀ t, 0 < t → 0 ≤ K t) (hKT : ∀ t, T ≤ t → c₁ * t ≤ K t)
    (hint : IntegrableOn (fun t => K t * Real.exp (-ε * t)) (Ioi 0)) (hS : T ≤ S) (hS0 : 0 < S) :
    c₁ * S ^ 2 * Real.exp (-(2 * ε * S)) ≤ ∫ t in Ioi (0 : ℝ), K t * Real.exp (-ε * t) := by
  have hsub : Icc S (2 * S) ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hS0 ht.1
  have h1 : ∫ t in Icc S (2 * S), K t * Real.exp (-ε * t) ≤
      ∫ t in Ioi (0 : ℝ), K t * Real.exp (-ε * t) := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hK0 t ht) (Real.exp_pos _).le
  have h2 : ∫ _ in Icc S (2 * S), c₁ * S * Real.exp (-(2 * ε * S)) ≤
      ∫ t in Icc S (2 * S), K t * Real.exp (-ε * t) := by
    refine setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set hsub)
      measurableSet_Icc fun t ht => ?_
    have hKt := hKT t (hS.trans ht.1)
    have he : Real.exp (-(2 * ε * S)) ≤ Real.exp (-ε * t) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2])
    calc c₁ * S * Real.exp (-(2 * ε * S)) ≤ c₁ * t * Real.exp (-ε * t) := by
          apply mul_le_mul (by nlinarith [ht.1]) he (Real.exp_pos _).le (by nlinarith [ht.1])
      _ ≤ K t * Real.exp (-ε * t) :=
          mul_le_mul_of_nonneg_right hKt (Real.exp_pos _).le
  have h3 : ∫ _ in Icc S (2 * S), c₁ * S * Real.exp (-(2 * ε * S)) =
      c₁ * S ^ 2 * Real.exp (-(2 * ε * S)) := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  linarith

/-- `4 sin²(πρ²/2) ∫ K e^{−πρ²t}` is bounded below for `0 < ρ² ≤ 49/32`. -/
theorem sin_sq_laplace_lower {K : ℝ → ℝ} {c₁ T ρ : ℝ} (hc₁ : 0 < c₁) (hT : 1 ≤ T)
    (hK0 : ∀ t, 0 < t → 0 ≤ K t) (hKT : ∀ t, T ≤ t → c₁ * t ≤ K t)
    (hρ : 0 < ρ) (hρmax : ρ ^ 2 ≤ 49 / 32)
    (hint : IntegrableOn (fun t => K t * Real.exp (-Real.pi * ρ ^ 2 * t)) (Ioi 0)) :
    min (4 * c₁ * Real.exp (-2) / π ^ 2)
        (4 * min (1 / (π * T)) (15 / 32) ^ 2 * (c₁ * T ^ 2 * Real.exp (-(49 * π / 16 * T)))) ≤
      4 * Real.sin (Real.pi * ρ ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), K t * Real.exp (-Real.pi * ρ ^ 2 * t) := by
  have hπ := Real.pi_pos
  set ε := π * ρ ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεmax : ε ≤ 49 * π / 32 := by rw [hεdef]; nlinarith
  have hint' : IntegrableOn (fun t => K t * Real.exp (-ε * t)) (Ioi 0) := by
    refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hεdef]; ring_nf
  have hsin_eq : Real.sin (Real.pi * ρ ^ 2 / 2) = Real.sin (ε / 2) := by rw [hεdef]
  have hI : ∫ t in Ioi (0 : ℝ), K t * Real.exp (-Real.pi * ρ ^ 2 * t) =
      ∫ t in Ioi (0 : ℝ), K t * Real.exp (-ε * t) := by
    congr 1; ext t; simp only [hεdef]; ring_nf
  rw [hsin_eq, hI]
  have hTpos : 0 < T := by linarith
  rcases le_or_gt ε (1 / T) with hsmall | hlarge
  · -- `S = 1/ε`
    have hS : T ≤ 1 / ε := by
      rw [le_div_iff₀ hε]; rw [le_div_iff₀ hTpos] at hsmall; linarith
    have hL := laplace_lower_of_linear hc₁ hε hK0 hKT hint' hS (by positivity)
    have hval : c₁ * (1 / ε) ^ 2 * Real.exp (-(2 * ε * (1 / ε))) = c₁ / ε ^ 2 * Real.exp (-2) := by
      rw [show 2 * ε * (1 / ε) = 2 by field_simp]; ring
    rw [hval] at hL
    have hsin : ε / π ≤ Real.sin (ε / 2) := by
      have hx : ε / 2 ≤ π / 2 := by
        have : ε ≤ 1 := hsmall.trans (by rw [div_le_one hTpos]; exact hT)
        linarith [Real.pi_gt_three]
      have := Real.mul_le_sin (by positivity) hx
      calc ε / π = 2 / π * (ε / 2) := by ring
        _ ≤ _ := this
    have hsin2 : (ε / π) ^ 2 ≤ Real.sin (ε / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsin 2
    refine (min_le_left _ _).trans ?_
    calc 4 * c₁ * Real.exp (-2) / π ^ 2 = 4 * (ε / π) ^ 2 * (c₁ / ε ^ 2 * Real.exp (-2)) := by
          field_simp
      _ ≤ 4 * Real.sin (ε / 2) ^ 2 * ∫ t in Ioi (0 : ℝ), K t * Real.exp (-ε * t) := by
          gcongr
  · -- `S = T`
    have hL := laplace_lower_of_linear hc₁ hε hK0 hKT hint' le_rfl hTpos
    have hexp : Real.exp (-(49 * π / 16 * T)) ≤ Real.exp (-(2 * ε * T)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsin : min (1 / (π * T)) (15 / 32) ≤ Real.sin (ε / 2) := by
      have h := sin_ge_min_of_mem (a := 1 / (2 * T)) (x := ε / 2) (by positivity)
        (by rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hTpos] at hlarge; nlinarith)
        (by linarith)
      have he : 2 * (1 / (2 * T)) / π = 1 / (π * T) := by field_simp
      rwa [he] at h
    have hm : 0 ≤ min (1 / (π * T)) (15 / 32) := le_min (by positivity) (by norm_num)
    have hsin2 : min (1 / (π * T)) (15 / 32) ^ 2 ≤ Real.sin (ε / 2) ^ 2 :=
      pow_le_pow_left₀ hm hsin 2
    refine (min_le_right _ _).trans ?_
    calc 4 * min (1 / (π * T)) (15 / 32) ^ 2 * (c₁ * T ^ 2 * Real.exp (-(49 * π / 16 * T)))
        ≤ 4 * Real.sin (ε / 2) ^ 2 * (c₁ * T ^ 2 * Real.exp (-(2 * ε * T))) := by
          gcongr
      _ ≤ 4 * Real.sin (ε / 2) ^ 2 * ∫ t in Ioi (0 : ℝ), K t * Real.exp (-ε * t) := by
          gcongr

/-! ## The `E8` certificate family -/

/-- (6.4)(1) for `d = 8`: `𝒦̂(iq, it) ≥ 0` for all `q, t > 0`. -/
abbrev E8KernelNonneg : Prop :=
  ∀ q t : ℝ, 0 < q → 0 < t → 0 ≤ (ckmrvEightHatKernel (imagPt q) (imagPt t)).re

/-- `K(q, v) = Re 𝒦̂(iq, iv)`. -/
def e8DualKernel (p : ℝ × ℝ) : ℝ := (ckmrvEightHatKernel (imagPt p.1) (imagPt p.2)).re

/-- The `E8` certificates, with the values of the auxiliary part. -/
theorem e8_exists_gaussianSchwartzCertificate' {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (hpos : E8KernelNonneg) :
    ∃ φ : SchwartzMap (Ambient 8) ℂ,
      (∀ x : Ambient 8, x ≠ 0 → φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ)) ∧
      GaussianSchwartzCertificate e8Set α (gaussianSchwartz hα + φ) := by
  obtain ⟨φ, hφ, hcert⟩ := e8_exists_gaussianSchwartzCertificate_of_pos hα hαπ hpos
  have hβ : 0 < α / π := div_pos hα Real.pi_pos
  have hβ1 : α / π ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq Real.pi_ne_zero).mp h)
  refine ⟨φ, hφ, hcert fun ξ hξ => ?_⟩
  rw [fourier_ckmrvEightKernel_axis hβ hβ1 hφ ξ]
  have h := ckmrv_contour_identity hβ hβ1 (r := ‖ξ‖) (norm_ne_zero_iff.mpr hξ)
  have hg1 : (α / π)⁻¹ = π / α := inv_div α π
  have hg2 : π / (α / π) = π ^ 2 / α := by rw [div_div_eq_mul_div, sq]
  rw [hg1, hg2] at h
  rw [gaussianKernel]
  exact h

/-- The unit vector `e₀` of `ℝ⁸`. -/
def e8Unit : Ambient 8 := EuclideanSpace.single (0 : Fin 8) (1 : ℝ)

theorem norm_smul_e8Unit {ρ : ℝ} (hρ : 0 ≤ ρ) : ‖ρ • e8Unit‖ = ρ := by
  have h1 : ‖e8Unit‖ = 1 := by simp [e8Unit]
  rw [norm_smul, h1, mul_one, Real.norm_of_nonneg hρ]

theorem smul_e8Unit_ne_zero {ρ : ℝ} (hρ : 0 < ρ) : ρ • e8Unit ≠ 0 := fun h => by
  have := congrArg norm h
  rw [norm_smul_e8Unit hρ.le, norm_zero] at this
  exact hρ.ne' this

/-- The certificate family: `e^{−α|x|²} + φ_α` for `0 < α ≠ π`, and `0` otherwise. -/
def e8CertFamily (hP : E8KernelNonneg) (α : ℝ) : 𝓢(Ambient 8, ℂ) :=
  if h : 0 < α ∧ α ≠ π then
    gaussianSchwartz h.1 + (e8_exists_gaussianSchwartzCertificate' h.1 h.2 hP).choose
  else 0

theorem e8CertFamily_cert (hP : E8KernelNonneg) {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    GaussianSchwartzCertificate e8Set α (e8CertFamily hP α) := by
  rw [e8CertFamily, dif_pos ⟨hα, hαπ⟩]
  exact (e8_exists_gaussianSchwartzCertificate' hα hαπ hP).choose_spec.2

theorem e8CertFamily_apply (hP : E8KernelNonneg) {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    {x : Ambient 8} (hx : x ≠ 0) :
    e8CertFamily hP α x = (gaussianKernel α x : ℂ) +
      ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  rw [e8CertFamily, dif_pos ⟨hα, hαπ⟩, add_apply, gaussianSchwartz_apply,
    (e8_exists_gaussianSchwartzCertificate' hα hαπ hP).choose_spec.1 x hx]

/-- The radial profile of the slack `e^{−αρ²} − f_α(ρ e₀)`. -/
def e8SlackProfile (hP : E8KernelNonneg) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-p.1 * p.2 ^ 2) - (e8CertFamily hP p.1 (p.2 • e8Unit)).re

theorem e8SlackProfile_norm (hP : E8KernelNonneg) (α : ℝ) (v : Ambient 8) :
    e8SlackProfile hP (α, ‖v‖) = gaussianKernel α v - (e8CertFamily hP α v).re := by
  simp only [e8SlackProfile, gaussianKernel]
  congr 1
  by_cases h : 0 < α ∧ α ≠ π
  · by_cases hv : v = 0
    · subst hv; simp
    · have hv' : ‖v‖ • e8Unit ≠ 0 := smul_e8Unit_ne_zero (norm_pos_iff.mpr hv)
      rw [e8CertFamily_apply hP h.1 h.2 hv', e8CertFamily_apply hP h.1 h.2 hv]
      simp only [gaussianKernel, norm_smul_e8Unit (norm_nonneg v)]
  · rw [e8CertFamily, dif_neg h]
    simp

theorem integrableOn_ckmrvEightKernel_laplace {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) {r : ℝ}
    (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) := by
  have hp := integrableOn_ckmrvEightPlusKernel_laplace_imagAxis hβ hβ1 hr
  have hm := integrableOn_ckmrvEightMinusKernel_laplace_imagAxis hβ hβ1 hr
  refine IntegrableOn.congr_fun (Integrable.div_const (Integrable.add hp hm) 2)
    (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, ckmrvEightKernel]
  ring

theorem integrableOn_ckmrvEightHatKernel_laplace {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) {r : ℝ}
    (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightHatKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) := by
  have hp := integrableOn_ckmrvEightPlusKernel_laplace_imagAxis hβ hβ1 hr
  have hm := integrableOn_ckmrvEightMinusKernel_laplace_imagAxis hβ hβ1 hr
  refine IntegrableOn.congr_fun (Integrable.div_const (Integrable.sub hp hm) 2)
    (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, ckmrvEightHatKernel]
  ring

theorem integrableOn_e8DualKernel {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) {u : ℝ} (hu : u ≠ 0) :
    IntegrableOn (fun v => e8DualKernel (q, v) * Real.exp (-Real.pi * u ^ 2 * v)) (Ioi 0) := by
  have h := Integrable.re (integrableOn_ckmrvEightHatKernel_laplace hq hq1 hu)
  refine IntegrableOn.congr_fun h (fun v _ => ?_) measurableSet_Ioi
  simp only [e8DualKernel, RCLike.re_to_complex, Complex.re_mul_ofReal]
  congr 2
  ring

/-- **The slack as a dual Laplace transform** (Cohn–Miller duality). -/
theorem e8SlackProfile_eq (hP : E8KernelNonneg) {α ρ : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (hρ : 0 < ρ) :
    e8SlackProfile hP (α, ρ) = (π / α) ^ 4 * (4 * Real.sin (Real.pi * ρ ^ 2 / 2) ^ 2 *
      ∫ v in Ioi (0 : ℝ), e8DualKernel (π / α, v) * Real.exp (-Real.pi * ρ ^ 2 * v)) := by
  have hβ : 0 < α / π := div_pos hα Real.pi_pos
  have hβ1 : α / π ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq Real.pi_ne_zero).mp h)
  have hn := norm_smul_e8Unit hρ.le
  have hint := integrableOn_ckmrvEightKernel_laplace hβ hβ1 (r := ρ) hρ.ne'
  have hre : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
      (Real.exp (-(π * ρ ^ 2) * t) : ℂ)).re =
      -((π / α) ^ 4 * ∫ v in Ioi (0 : ℝ), e8DualKernel (π / α, v) *
        Real.exp (-Real.pi * ρ ^ 2 * v)) := by
    have h1 : (∫ t in Ioi (0 : ℝ), ckmrvEightKernel (imagPt (α / π)) (imagPt t) *
        (Real.exp (-(π * ρ ^ 2) * t) : ℂ)).re = ∫ t in Ioi (0 : ℝ),
          (ckmrvEightKernel (imagPt (α / π)) (imagPt t) * (Real.exp (-(π * ρ ^ 2) * t) : ℂ)).re := by
      rw [← RCLike.re_to_complex, ← integral_re hint]
      rfl
    rw [h1, ← integral_const_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hc : -(((α / π : ℝ) : ℂ) ^ 4)⁻¹ = ((-((α / π) ^ 4)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    have hpi : (π / α) ^ 4 = ((α / π) ^ 4)⁻¹ := by rw [← inv_pow, inv_div]
    rw [ckmrvEightKernel_imagPt hβ, hc, mul_assoc, Complex.re_ofReal_mul, Complex.re_mul_ofReal,
      inv_div, hpi]
    simp only [e8DualKernel]
    rw [show -Real.pi * ρ ^ 2 * t = -(π * ρ ^ 2) * t by ring]
    ring
  simp only [e8SlackProfile]
  rw [e8CertFamily_apply hP hα hαπ (smul_e8Unit_ne_zero hρ), hn, Complex.add_re,
    Complex.ofReal_re, Complex.re_ofReal_mul, hre]
  simp only [gaussianKernel, hn]
  ring

/-! ## Lower bounds of the slack -/

/-- The explicit quadratic minorant `min(1/4, ((r − ρ)⁺/r)²)`. -/
def quadMinorant (r ρ : ℝ) : ℝ := min (1 / 4) ((max 0 (r - ρ) / r) ^ 2)

theorem continuous_quadMinorant (r : ℝ) : Continuous (quadMinorant r) := by
  unfold quadMinorant
  exact continuous_const.min (((continuous_const.max
    (continuous_const.sub continuous_id)).div_const r).pow 2)

/-- **The `E8` analytic unit-cost input from the kernel inequalities**: (6.4)(1), a uniform
lower bound on the block `[3,4] × [1,2]` and a uniform linear lower bound for large `t`. -/
theorem e8_analyticUnitCostInput_of_kernel_bounds {s : ℝ} (hs : 0 < s) (hP : E8KernelNonneg)
    (hblock : ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ v ∈ Icc (1 : ℝ) 2,
      B ≤ e8DualKernel (q, v))
    (hlin : ∃ c₁ T : ℝ, 0 < c₁ ∧ 1 ≤ T ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ e8DualKernel (q, t)) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput e8Set s (Real.sqrt 2) C⁻¹ (1 / 8) := by
  obtain ⟨B, hB, hBlow⟩ := hblock
  obtain ⟨c₁, T, hc₁, hT, hlinb⟩ := hlin
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hπ := Real.pi_pos
  have ha : 0 < π / 4 := by positivity
  have hab : π / 4 < π / 3 := by linarith
  have hgood : ∀ α ∈ Icc (π / 4) (π / 3), 0 < α ∧ α ≠ π := fun α hα =>
    ⟨gaussian_compact_interval_pos hα, by intro h; rw [h] at hα; linarith [hα.2]⟩
  have hq : ∀ α ∈ Icc (π / 4) (π / 3), π / α ∈ Icc (3 : ℝ) 4 := fun α hα =>
    gaussian_dual_compact_interval hα
  have hKnn : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ e8DualKernel (q, v) := fun q hq v hv =>
    hP q v (by linarith [hq.1]) hv
  have hq1 : ∀ q ∈ Icc (3 : ℝ) 4, q ≠ 1 := fun q hq => by linarith [hq.1]
  -- the lower bound `A` of the slack on `[π/4, π/3] × [0, 7√2/8]`
  set m := min (1 / (π * T)) (15 / 32) with hmdef
  have hm : 0 < m := lt_min (by positivity) (by norm_num)
  set L := min (4 * c₁ * Real.exp (-2) / π ^ 2)
      (4 * m ^ 2 * (c₁ * T ^ 2 * Real.exp (-(49 * π / 16 * T)))) with hLdef
  have hL : 0 < L := lt_min (by positivity) (by positivity)
  have hApos : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u : ℝ, 0 < u → u ^ 2 ≤ 49 / 32 →
      81 * L ≤ e8SlackProfile hP (α, u) := by
    intro α hα u hu hu2
    obtain ⟨hα0, hαπ⟩ := hgood α hα
    have hqa := hq α hα
    rw [e8SlackProfile_eq hP hα0 hαπ hu]
    have hlow := sin_sq_laplace_lower (K := fun v => e8DualKernel (π / α, v)) hc₁ hT
      (fun t ht => hKnn _ hqa t ht) (fun t ht => hlinb _ hqa t ht) hu hu2
      (integrableOn_e8DualKernel (by linarith [hqa.1]) (hq1 _ hqa) hu.ne')
    have h81 : (81 : ℝ) ≤ (π / α) ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hqa.1 4
      norm_num at this ⊢
      linarith
    calc 81 * L ≤ (π / α) ^ 4 * L := by gcongr
      _ ≤ _ := by gcongr
  have hu2 : ∀ u : ℝ, 0 ≤ u → u ≤ 7 / 8 * Real.sqrt 2 → u ^ 2 ≤ 49 / 32 := by
    intro u h0 h1
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [hr2]
  have hAlower : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u ∈ Icc 0 (7 / 8 * Real.sqrt 2),
      81 * L ≤ e8SlackProfile hP (α, u) := by
    intro α hα u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      have hf : Continuous fun u : ℝ => e8SlackProfile hP (α, u) := by
        simp only [e8SlackProfile]
        exact (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).sub
          (Complex.continuous_re.comp ((e8CertFamily hP α).continuous.comp
            (continuous_id.smul continuous_const)))
      refine ge_of_tendsto (hf.continuousAt.continuousWithinAt (s := Ioi 0)) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 7 / 8 * Real.sqrt 2 by positivity)]
        with u' hu'
      exact hApos α hα u' hu'.1 (hu2 u' hu'.1.le hu'.2.le)
    · exact hApos α hα u hpos (hu2 u hu.1 hu.2)
  -- the block lower bound and the factorization for the normalized kernel
  have hBlower : ∀ α ∈ Icc (π / 4) (π / 3), ∀ t ∈ Icc (1 : ℝ) 2,
      B ≤ gaussianDualLaplaceKernel 4 e8DualKernel (α, t) := by
    intro α hα t ht
    have hqa := hq α hα
    have hk := hBlow _ hqa t ht
    have h1 : (1 : ℝ) ≤ (π / α) ^ 4 := one_le_pow₀ (by linarith [hqa.1])
    simp only [gaussianDualLaplaceKernel]
    exact hk.trans (le_mul_of_one_le_left (hB.le.trans hk) h1)
  have hKnonneg : ∀ α ∈ Icc (π / 4) (π / 3), ∀ t : ℝ, 0 < t →
      0 ≤ gaussianDualLaplaceKernel 4 e8DualKernel (α, t) := fun α hα t ht =>
    gaussianDualLaplaceKernel_nonneg 4 e8DualKernel hKnn hα ht
  have hint : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u ∈ Icc (7 / 8 * Real.sqrt 2) (Real.sqrt 2),
      IntegrableOn (fun t => gaussianDualLaplaceKernel 4 e8DualKernel (α, t) *
        Real.exp (-Real.pi * u ^ 2 * t)) (Ioi (0 : ℝ)) volume := by
    intro α hα u hu
    have hqa := hq α hα
    have hu0 : u ≠ 0 := by
      have : 0 < 7 / 8 * Real.sqrt 2 := by positivity
      linarith [hu.1]
    exact integrableOn_gaussianDualLaplaceKernel 4 e8DualKernel α u
      (integrableOn_e8DualKernel (by linarith [hqa.1]) (hq1 _ hqa) hu0)
  have hfactor : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u ∈ Icc (7 / 8 * Real.sqrt 2) (Real.sqrt 2),
      e8SlackProfile hP (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), gaussianDualLaplaceKernel 4 e8DualKernel (α, t) *
          Real.exp (-Real.pi * u ^ 2 * t) := by
    intro α hα u hu
    obtain ⟨hα0, hαπ⟩ := hgood α hα
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
    rw [integral_gaussianDualLaplaceKernel, e8SlackProfile_eq hP hα0 hαπ hu0]
    ring
  obtain ⟨k, hk, hlower⟩ := uniform_quadratic_slack_of_laplace_lower_bounds hr (Or.inl hr2)
    (e8SlackProfile hP) (gaussianDualLaplaceKernel 4 e8DualKernel) (by positivity : (0 : ℝ) < 81 * L)
    hAlower hB hBlower hKnonneg hint hfactor
  -- the gap for the true slack
  have hcertAE : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      GaussianSchwartzCertificate e8Set α (e8CertFamily hP α) :=
    ae_certificate_of_forall_ne π fun α hα hαπ => e8CertFamily_cert hP hα hαπ
  have hgapT := gaussian_gap_ae_of_certificates hs.le 9 (e8_latticeRieszEnergy_ne_top (by norm_num))
    (e8CertFamily hP) hcertAE (e8SlackProfile hP) (fun α v => e8SlackProfile_norm hP α v)
  -- the quadratic minorant is below the slack
  have hVle : ∀ α ∈ Icc (π / 4) (π / 3), ∀ ρ : ℝ, 0 ≤ ρ →
      ENNReal.ofReal (k * quadMinorant (Real.sqrt 2) ρ) ≤
        ENNReal.ofReal (e8SlackProfile hP (α, ρ)) := by
    intro α hα ρ hρ
    rcases le_or_gt (Real.sqrt 2) ρ with hfar | hnear
    · have h0 : quadMinorant (Real.sqrt 2) ρ = 0 := by
        simp only [quadMinorant, max_eq_left (by linarith : Real.sqrt 2 - ρ ≤ 0)]
        norm_num
      rw [h0, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    · apply ENNReal.ofReal_le_ofReal
      set sv := (Real.sqrt 2 - ρ) / Real.sqrt 2 with hsv
      have hsv0 : 0 < sv := div_pos (by linarith) hr
      have hq : quadMinorant (Real.sqrt 2) ρ = min (1 / 4) (sv ^ 2) := by
        simp only [quadMinorant, max_eq_right (by linarith : (0 : ℝ) ≤ Real.sqrt 2 - ρ), hsv]
      rw [hq]
      rcases le_or_gt sv (1 / 2) with hsmall | hbig
      · have hlim : Tendsto (fun t : ℝ => k * t ^ 2) (𝓝[<] sv) (𝓝 (k * sv ^ 2)) :=
          ((continuous_const.mul (continuous_pow 2)).tendsto sv).mono_left nhdsWithin_le_nhds
        have hle : k * sv ^ 2 ≤ e8SlackProfile hP (α, ρ) := by
          refine le_of_tendsto hlim ?_
          filter_upwards [Ioo_mem_nhdsLT hsv0] with t ht
          refine hlower t ht.1 (by linarith [ht.2]) α hα ρ hρ ?_
          have : t < (Real.sqrt 2 - ρ) / Real.sqrt 2 := ht.2
          rw [lt_div_iff₀ hr] at this
          linarith
        exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hk.le).trans hle
      · have hle := hlower (1 / 2) (by norm_num) le_rfl α hα ρ hρ (by
          have : (1 / 2 : ℝ) < (Real.sqrt 2 - ρ) / Real.sqrt 2 := hbig
          rw [lt_div_iff₀ hr] at this
          linarith)
        have : k * min (1 / 4) (sv ^ 2) ≤ k * (1 / 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hk.le
          exact (min_le_left _ _).trans (by norm_num)
        exact this.trans hle
  -- the measurable minorant potential
  let V : ℝ → Ambient 8 → Ambient 8 → ℝ≥0∞ := fun α x y =>
    if α ∈ Icc (π / 4) (π / 3) then ENNReal.ofReal (k * quadMinorant (Real.sqrt 2) (dist x y))
    else 0
  have hV : Measurable (fun p : ℝ × (Ambient 8 × Ambient 8) => V p.1 p.2.1 p.2.2) := by
    refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
    exact ENNReal.measurable_ofReal.comp (continuous_const.mul ((continuous_quadMinorant _).comp
      (continuous_dist.comp (continuous_snd.fst.prodMk continuous_snd.snd)))).measurable
  have hgapV : ∀ μ : Measure (Configuration (Ambient 8)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy e8Set (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow 8) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow 8) ∂μ := by
    intro μ hprob hμ hρ henergy
    filter_upwards [hgapT μ hprob hμ hρ henergy] with α hα
    refine le_trans (add_le_add le_rfl (lintegral_mono fun c =>
      orderedWindowEnergy_mono_potential (fun x y => ?_) c _)) hα
    by_cases hαI : α ∈ Icc (π / 4) (π / 3)
    · simp only [V, if_pos hαI]
      exact hVle α hαI _ dist_nonneg
    · simp only [V, if_neg hαI]
      exact zero_le
  have hlowerV : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ α ∈ Icc (π / 4) (π / 3),
      ∀ x y : Ambient 8, x ≠ y → dist x y < Real.sqrt 2 * (1 - t) →
        ENNReal.ofReal (k * t ^ 2) ≤ V α x y := by
    intro t ht hhalf α hα x y _ hclose
    simp only [V, if_pos hα]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hk.le
    have hd : 0 ≤ dist x y := dist_nonneg
    have hpos : 0 < Real.sqrt 2 - dist x y := by nlinarith
    simp only [quadMinorant, max_eq_right hpos.le]
    apply le_min (by nlinarith)
    have h1 : t ≤ (Real.sqrt 2 - dist x y) / Real.sqrt 2 := by
      rw [le_div_iff₀ hr]; nlinarith
    exact pow_le_pow_left₀ ht.le h1 2
  exact ⟨rieszIntervalGapCoefficient s (π / 4) (π / 3) k,
    rieszIntervalGapCoefficient_pos hs ha hab hk,
    analyticUnitCostInput_of_gaussian_gap_interval hs ha hab hk e8Set countable_e8Set
      (Real.sqrt 2) V hV hgapV hlowerV⟩

end E8Leech
