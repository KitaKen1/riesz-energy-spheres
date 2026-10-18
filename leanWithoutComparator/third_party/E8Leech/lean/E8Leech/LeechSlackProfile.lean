import E8Leech.LeechCKMRVCertificate
import E8Leech.AeCertificates

/-!
# The Leech certificate family and its slack

For `0 < α ≠ π` the certificate function is `f_α = e^{−α|·|²} + φ_α`, with `φ_α` the Schwartz
function of the `𝒦`-profile at `τ = iα/π`. Its slack against the Gaussian is explicit at every
radius `ρ ≥ 0`:

`e^{−αρ²} − f_α(ρ e) = (π/α)¹² · Re P_𝒦̂,π/α(πρ²)`   (`leechSlackProfile_eq`),

by `P_𝒦,y = −y^{−12} P_𝒦̂,1/y`. The real part of the `𝒦̂`-profile in the truncated form with cut `1`
is `leechHatProfile_re_eq`; the integrand of its second integral is integrable
(`integrableOn_leechAxisKernel_trunc`).

`LeechFourierIdentities` is the identity (**) in dimension 24 for all `α`; with
`LeechKernelInequalities` it makes `f_α` a Gaussian certificate (`leechCertFamily_cert`). Both are
hypotheses and are not proved here.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real FourierTransform SchwartzMap

/-- `K̂(q, t) = Re 𝒦̂⁽²⁴⁾(iq, it)`. -/
def leechDualKernel (p : ℝ × ℝ) : ℝ := (ckmrvLeechHatKernel (imagPt p.1) (imagPt p.2)).re

/-- The identity (**) in dimension 24, for every `α` and every Schwartz function with the
`𝒦`-profile. -/
def LeechFourierIdentities : Prop :=
  ∀ α : ℝ, 0 < α → α ≠ π → ∀ φ : 𝓢(Ambient 24, ℂ),
    (∀ x : Ambient 24, φ x = leechAxisRadialProfile 1 (α / π) (π * ‖x‖ ^ 2)) →
      LeechFourierIdentity α φ

theorem div_pi_pos {α : ℝ} (hα : 0 < α) : 0 < α / π := div_pos hα Real.pi_pos

theorem div_pi_ne_one {α : ℝ} (hαπ : α ≠ π) : α / π ≠ 1 := fun h =>
  hαπ ((div_eq_one_iff_eq Real.pi_ne_zero).mp h)

/-! ## The certificate family -/

/-- The certificate family: `e^{−α|x|²} + φ_α` for `0 < α ≠ π`, and `0` otherwise. -/
def leechCertFamily (α : ℝ) : 𝓢(Ambient 24, ℂ) :=
  if h : 0 < α ∧ α ≠ π then
    gaussianSchwartz h.1 + (exists_schwartz_leechAxisRadialProfile (Ambient 24) 1
      (div_pi_pos h.1) (div_pi_ne_one h.2)).choose
  else 0

theorem leechCertFamily_apply {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (x : Ambient 24) :
    leechCertFamily α x = (gaussianKernel α x : ℂ) +
      leechAxisRadialProfile 1 (α / π) (π * ‖x‖ ^ 2) := by
  rw [leechCertFamily, dif_pos ⟨hα, hαπ⟩, add_apply, gaussianSchwartz_apply,
    (exists_schwartz_leechAxisRadialProfile (Ambient 24) 1 (div_pi_pos hα)
      (div_pi_ne_one hαπ)).choose_spec.1 x]

/-- **The family consists of Gaussian certificates**, given the kernel inequalities and the Fourier
identities. -/
theorem leechCertFamily_cert (H : LeechKernelInequalities) (hF : LeechFourierIdentities) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) : GaussianSchwartzCertificate leechSet α (leechCertFamily α) := by
  rw [leechCertFamily, dif_pos ⟨hα, hαπ⟩]
  have hspec := (exists_schwartz_leechAxisRadialProfile (Ambient 24) 1 (div_pi_pos hα)
    (div_pi_ne_one hαπ)).choose_spec.1
  exact leech_gaussianSchwartzCertificate_of_ckmrv hα hαπ H _ hspec (hF α hα hαπ _ hspec)

/-! ## The slack -/

/-- The unit vector `e₀` of `ℝ²⁴`. -/
def leechUnit : Ambient 24 := EuclideanSpace.single (0 : Fin 24) (1 : ℝ)

theorem norm_smul_leechUnit {ρ : ℝ} (hρ : 0 ≤ ρ) : ‖ρ • leechUnit‖ = ρ := by
  have h1 : ‖leechUnit‖ = 1 := by simp [leechUnit]
  rw [norm_smul, h1, mul_one, Real.norm_of_nonneg hρ]

/-- The radial profile of the slack `e^{−αρ²} − f_α(ρ e₀)`. -/
def leechSlackProfile (p : ℝ × ℝ) : ℝ :=
  Real.exp (-p.1 * p.2 ^ 2) - (leechCertFamily p.1 (p.2 • leechUnit)).re

theorem leechSlackProfile_norm (α : ℝ) (v : Ambient 24) :
    leechSlackProfile (α, ‖v‖) = gaussianKernel α v - (leechCertFamily α v).re := by
  simp only [leechSlackProfile, gaussianKernel]
  congr 1
  by_cases h : 0 < α ∧ α ≠ π
  · rw [leechCertFamily_apply h.1 h.2, leechCertFamily_apply h.1 h.2,
      norm_smul_leechUnit (norm_nonneg v)]
    simp only [gaussianKernel, norm_smul_leechUnit (norm_nonneg v)]
  · rw [leechCertFamily, dif_neg h]
    simp

/-- **The slack is `(π/α)¹²` times the `𝒦̂`-profile at `q = π/α`**, at every radius. -/
theorem leechSlackProfile_eq {α ρ : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hρ : 0 ≤ ρ) :
    leechSlackProfile (α, ρ) =
      (π / α) ^ 12 * (leechAxisRadialProfile (-1) (π / α) (π * ρ ^ 2)).re := by
  have hy := div_pi_pos hα
  have hy1 := div_pi_ne_one hαπ
  have hinv : (α / π)⁻¹ = π / α := inv_div α π
  have hpow : ((α / π) ^ 12)⁻¹ = (π / α) ^ 12 := by rw [← inv_pow, hinv]
  simp only [leechSlackProfile]
  rw [leechCertFamily_apply hα hαπ, norm_smul_leechUnit hρ, Complex.add_re, Complex.ofReal_re,
    leechAxisRadialProfile_one_eq hy hy1, hinv,
    show -(((α / π : ℝ) : ℂ) ^ 12)⁻¹ = ((-((α / π) ^ 12)⁻¹ : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, hpow, gaussianKernel, norm_smul_leechUnit hρ]
  ring

/-! ## The truncated kernel -/

/-- The integrand of the second integral of the truncated form is integrable. -/
theorem integrableOn_leechAxisKernel_trunc (s : ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) {b p : ℝ}
    (hb : 0 < b) (hp : 0 ≤ p) :
    IntegrableOn (fun t : ℝ => (leechAxisKernel s β t -
      (leechAxisCusp s β 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
        leechAxisCusp s β 1 * (Real.exp (2 * π * t) : ℂ))) * (Real.exp (-b * t) : ℂ)) (Ioi p) := by
  obtain ⟨g, hg, hgK, -, hg01, -, hsub⟩ := exists_leechAxis s hβ hβ1
  have hπ := Real.pi_pos
  have isub := integrableOn_sub_cuspProfile (b := b) hg hg01
    (show (fun t => g t - cuspProfile (leechAxisCusp s β 0) (leechAxisCusp s β 1)
      (leechAxisCusp s β 2) (leechAxisCusp s β 3) (2 * π) t) =O[atTop]
        fun t => t * Real.exp ((-π + π / 4) * t) from hsub) (by linarith)
  have iQ := integrableOn_cuspProfile 0 0 (leechAxisCusp s β 2) (leechAxisCusp s β 3) le_rfl hb
  have hsubset : Ioi p ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_le_of_lt hp ht
  have hsum := (isub.mono_set hsubset).add (iQ.mono_set hsubset)
  refine (hsum.congr_fun_ae ?_ : _)
  have hfin : volume ({β, β⁻¹} : Set ℝ) = 0 := (Set.toFinite {β, β⁻¹}).measure_zero _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({β, β⁻¹} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  filter_upwards [ae_restrict_of_ae hae] with t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  simp only [Pi.add_apply, cuspProfile, hgK t ht.1 ht.2, Real.exp_zero, zero_mul,
    Complex.ofReal_one, mul_one, zero_add]
  ring

/-- The real part of the integrand of the second integral, for `𝒦̂`. -/
theorem leechHat_trunc_integrand_re (q b t : ℝ) :
    ((leechAxisKernel (-1) q t - (leechAxisCusp (-1) q 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
      leechAxisCusp (-1) q 1 * (Real.exp (2 * π * t) : ℂ))) * (Real.exp (-b * t) : ℂ)).re =
      (leechDualKernel (q, t) - ((leechAxisCusp (-1) q 0).re * t +
        (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t)) * Real.exp (-b * t) := by
  rw [Complex.re_mul_ofReal, ← Complex.ofReal_mul, Complex.sub_re, Complex.add_re,
    Complex.re_mul_ofReal, Complex.re_mul_ofReal, leechAxisKernel_neg_one, leechDualKernel]
  ring

/-- The truncated real kernel times `e^{−bt}` is integrable on `(1, ∞)` for `b > 0`. -/
theorem integrableOn_leechDualKernel_trunc {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) {b : ℝ}
    (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (leechDualKernel (q, t) - ((leechAxisCusp (-1) q 0).re * t +
      (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t)) * Real.exp (-b * t)) (Ioi 1) := by
  have h := Integrable.re (integrableOn_leechAxisKernel_trunc (-1) hq hq1 hb zero_le_one)
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  simp only [RCLike.re_to_complex]
  exact leechHat_trunc_integrand_re q b t

/-- **The real part of the `𝒦̂`-profile in the truncated form with cut `1`.** -/
theorem leechHatProfile_re_eq {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) {b : ℝ} (hb : 0 < b) :
    (leechAxisRadialProfile (-1) q b).re =
      4 * Real.sin (b / 2) ^ 2 *
        ((∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t)) +
          ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
            ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
              Real.exp (2 * π * t)) * Real.exp (-b * t)) +
        Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * 1) *
          ((leechAxisCusp (-1) q 0).re +
            ((leechAxisCusp (-1) q 1).re + 1 * (leechAxisCusp (-1) q 0).re) * (b - 2 * π)) := by
  have hKim : ∀ t : ℝ, 0 < t → (leechAxisKernel (-1) q t).im = 0 := fun t ht =>
    leechAxisKernel_im im_neg_one hq ht
  have hA := leechAxisCusp_im im_neg_one hq 0
  have hB := leechAxisCusp_im im_neg_one hq 1
  rw [leechAxisRadialProfile_truncated (-1) hq hq1 hb zero_le_one]
  have hkre : ∀ t : ℝ, (leechAxisKernel (-1) q t).re = leechDualKernel (q, t) := fun t => by
    rw [leechAxisKernel_neg_one, leechDualKernel]
  generalize leechAxisCusp (-1) q 0 = A at *
  generalize leechAxisCusp (-1) q 1 = B at *
  have hz : ∀ t : ℝ, 0 < t → (leechAxisKernel (-1) q t -
      (A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ))).im = 0 := by
    intro t ht
    rw [← Complex.ofReal_mul, Complex.sub_im, Complex.add_im, Complex.im_mul_ofReal,
      Complex.im_mul_ofReal, hKim t ht, hA, hB]
    ring
  have hzre : ∀ t : ℝ, (leechAxisKernel (-1) q t -
      (A * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) + B * (Real.exp (2 * π * t) : ℂ))).re =
      leechDualKernel (q, t) - (A.re * t + B.re) * Real.exp (2 * π * t) := by
    intro t
    rw [← Complex.ofReal_mul, Complex.sub_re, Complex.add_re, Complex.re_mul_ofReal,
      Complex.re_mul_ofReal, hkre]
    ring
  rw [setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioc fun t ht => by
      rw [Complex.im_mul_ofReal, hKim t ht.1, zero_mul],
    setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioi fun t ht => by
      rw [Complex.im_mul_ofReal, hz t (lt_trans zero_lt_one ht), zero_mul]]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.re_mul_ofReal, Complex.ofReal_re,
    hzre, hkre]

end E8Leech
