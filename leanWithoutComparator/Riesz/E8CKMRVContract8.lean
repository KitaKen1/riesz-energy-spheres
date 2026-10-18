import Riesz.E8GaussianContact8

/-! The CKMRV Laplace–sine contract for the actual E8 Gaussian certificates.

Cohn–Kumar–Miller–Radchenko–Viazovska (Annals 196 (2022), (5.1)/(5.2) with `τ = iβ`,
Lemma 6.2) write the auxiliary function and its Fourier transform, for `x, ξ ≠ 0`, as
  `f_β(x) = exp(-πβ|x|²) + 4 sin²(π|x|²/2) ∫_0^∞ K(iβ,it) exp(-π|x|² t) dt`,
  `𝓕f_β(ξ) = 4 sin²(π|ξ|²/2) ∫_0^∞ K̂(iβ,it) exp(-π|ξ|² t) dt`,
with the S-duality `K(iβ,it) = -β⁻⁴ K̂(i/β,it)` and the single E8 kernel inequality
(6.4)(1): `K̂(iu,it) > 0` for all `u, t > 0`.

`E8LaplaceSineData8` records exactly these facts for arbitrary real kernels. We prove that
they give CKMRV-shaped certificates for every `β > 0`, hence `S8s4Target`. Values at the
origin follow by continuity, so the `r = 0` formulas (5.3)/(5.4) are not needed; contact and
Fourier zeros come from `sin²(π|v|²/2) = 0` on the even lattice. Constructing the kernels,
proving the two Laplace–sine formulas and the kernel inequality is NOT done here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace SphericalRiesz

/-- The Laplace–sine transform `4 sin²(π|x|²/2) ∫_0^∞ k(t) exp(-π|x|² t) dt`. -/
def e8LaplaceSine8 (k : ℝ → ℝ) (x : E8Ambient) : ℝ :=
  4 * Real.sin (Real.pi*‖x‖^2/2)^2 *
    ∫ t : ℝ in Set.Ioi 0, k t * Real.exp (-(Real.pi*‖x‖^2*t))

/-- The analytic facts CKMRV supply for E8, stated for arbitrary real kernels
(`K u t` stands for `K(iu,it)` and `Khat u t` for `K̂(iu,it)`). -/
structure E8LaplaceSineData8 where
  K : ℝ → ℝ → ℝ
  Khat : ℝ → ℝ → ℝ
  f : ∀ β : ℝ, 0 < β → 𝓢(E8Ambient, ℂ)
  f_eq : ∀ (β : ℝ) (hβ : 0 < β) (x : E8Ambient), x ≠ 0 →
    f β hβ x = ((Real.exp (-(Real.pi*β*‖x‖^2)) + e8LaplaceSine8 (K β) x : ℝ) : ℂ)
  fourier_eq : ∀ (β : ℝ) (hβ : 0 < β) (ξ : E8Ambient), ξ ≠ 0 →
    (𝓕 (f β hβ)) ξ = ((e8LaplaceSine8 (Khat β) ξ : ℝ) : ℂ)
  duality : ∀ β : ℝ, 0 < β → ∀ t : ℝ, 0 < t → K β t = -((β^4)⁻¹ * Khat β⁻¹ t)
  positivity : ∀ u : ℝ, 0 < u → ∀ t : ℝ, 0 < t → 0 ≤ Khat u t

theorem e8Lattice_sin_half_norm_sq {v : E8Ambient} (hv : v ∈ e8Lattice) :
    Real.sin (Real.pi*‖v‖^2/2) = 0 := by
  obtain ⟨k, hk⟩ := e8Lattice_even ⟨v, hv⟩
  have hk' : ‖v‖^2 = 2*(k:ℝ) := hk
  rw [hk', show Real.pi*(2*(k:ℝ))/2 = (k:ℝ)*Real.pi by ring]
  exact Real.sin_nat_mul_pi k

theorem e8LaplaceSine8_lattice (k : ℝ → ℝ) {v : E8Ambient} (hv : v ∈ e8Lattice) :
    e8LaplaceSine8 k v = 0 := by
  rw [e8LaplaceSine8, e8Lattice_sin_half_norm_sq hv]
  ring

theorem e8LaplaceSine8_nonneg {k : ℝ → ℝ} (hk : ∀ t : ℝ, 0 < t → 0 ≤ k t) (x : E8Ambient) :
    0 ≤ e8LaplaceSine8 k x := by
  apply mul_nonneg (by positivity)
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (hk t ht) (Real.exp_pos _).le

theorem e8LaplaceSine8_nonpos {k : ℝ → ℝ} (hk : ∀ t : ℝ, 0 < t → k t ≤ 0) (x : E8Ambient) :
    e8LaplaceSine8 k x ≤ 0 := by
  have h : 0 ≤ e8LaplaceSine8 (fun t => -k t) x :=
    e8LaplaceSine8_nonneg (fun t ht => neg_nonneg.mpr (hk t ht)) x
  have hneg : e8LaplaceSine8 (fun t => -k t) x = -e8LaplaceSine8 k x := by
    unfold e8LaplaceSine8
    rw [← mul_neg, ← integral_neg]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [neg_mul]
  linarith

/-- A closed set containing every nonzero vector contains the origin. -/
theorem e8_mem_of_isClosed_of_ne_zero {S : Set E8Ambient} (hS : IsClosed S)
    (h : ∀ x : E8Ambient, x ≠ 0 → x ∈ S) (y : E8Ambient) : y ∈ S := by
  have hsub : ({0}ᶜ : Set E8Ambient) ⊆ S := fun x hx => h x hx
  have hcl : closure ({0}ᶜ : Set E8Ambient) ⊆ S := hS.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : E8Ambient)).closure_eq] at hcl
  exact hcl (Set.mem_univ y)

/-- The Laplace–sine data give a CKMRV-shaped certificate at every `β > 0`. -/
theorem E8LaplaceSineData8.certificate (D : E8LaplaceSineData8) {β : ℝ} (hβ : 0 < β) :
    E8GaussianContactCertificate8 β (D.f β hβ) := by
  set F : 𝓢(E8Ambient, ℂ) := 𝓕 (D.f β hβ) with hF
  have hFeq : ∀ ξ : E8Ambient, ξ ≠ 0 → F ξ = ((e8LaplaceSine8 (D.Khat β) ξ : ℝ) : ℂ) := by
    intro ξ hξ
    rw [hF]
    exact D.fourier_eq β hβ ξ hξ
  have hfc : Continuous (fun x : E8Ambient => D.f β hβ x) := (D.f β hβ).continuous
  have hgc : Continuous (fun x : E8Ambient => Real.exp (-(Real.pi*β*‖x‖^2))) := by fun_prop
  have hFim : Continuous (fun ξ : E8Ambient => (F ξ).im) := Complex.continuous_im.comp F.continuous
  have hFre : Continuous (fun ξ : E8Ambient => (F ξ).re) := Complex.continuous_re.comp F.continuous
  have hKnonpos : ∀ t : ℝ, 0 < t → D.K β t ≤ 0 := by
    intro t ht
    rw [D.duality β hβ t ht]
    have := D.positivity β⁻¹ (inv_pos.mpr hβ) t ht
    have hc : 0 < (β^4)⁻¹ := by positivity
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine e8_mem_of_isClosed_of_ne_zero (S := {x | (D.f β hβ x).im = 0})
      (isClosed_eq (Complex.continuous_im.comp hfc) continuous_const) ?_ x
    intro y hy
    show (D.f β hβ y).im = 0
    rw [D.f_eq β hβ y hy, Complex.ofReal_im]
  · intro ξ
    refine e8_mem_of_isClosed_of_ne_zero (S := {ξ | (F ξ).im = 0})
      (isClosed_eq hFim continuous_const) ?_ ξ
    intro y hy
    show (F y).im = 0
    rw [hFeq y hy, Complex.ofReal_im]
  · intro ξ
    refine e8_mem_of_isClosed_of_ne_zero (S := {ξ | 0 ≤ (F ξ).re})
      (isClosed_le continuous_const hFre) ?_ ξ
    intro y hy
    show 0 ≤ (F y).re
    rw [hFeq y hy, Complex.ofReal_re]
    exact e8LaplaceSine8_nonneg (D.positivity β hβ) y
  · intro x
    refine e8_mem_of_isClosed_of_ne_zero
      (S := {x | (D.f β hβ x).re ≤ Real.exp (-(Real.pi*β*‖x‖^2))})
      (isClosed_le (Complex.continuous_re.comp hfc) hgc) ?_ x
    intro y hy
    show (D.f β hβ y).re ≤ Real.exp (-(Real.pi*β*‖y‖^2))
    rw [D.f_eq β hβ y hy, Complex.ofReal_re]
    have := e8LaplaceSine8_nonpos hKnonpos y
    linarith
  · intro v hv hv0
    rw [D.f_eq β hβ v hv0, Complex.ofReal_re, e8LaplaceSine8_lattice _ hv, add_zero]
  · intro v hv hv0
    rw [hFeq v hv0, e8LaplaceSine8_lattice _ hv, Complex.ofReal_zero]

/-- The CKMRV Laplace–sine contract implies the original main target. -/
theorem S8s4Target_of_laplaceSineData (D : E8LaplaceSineData8) : S8s4Target :=
  S8s4Target_of_schwartz_input
    (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩))

#print axioms e8Lattice_sin_half_norm_sq
#print axioms e8LaplaceSine8_lattice
#print axioms e8LaplaceSine8_nonneg
#print axioms e8LaplaceSine8_nonpos
#print axioms e8_mem_of_isClosed_of_ne_zero
#print axioms E8LaplaceSineData8.certificate
#print axioms S8s4Target_of_laplaceSineData

end SphericalRiesz
