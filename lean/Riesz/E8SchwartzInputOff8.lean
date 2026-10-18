import Riesz.SphereGaussianSchwartzProfile8

/-! The sharp lower Gaussian profile of `S⁸` from certificates at the scales `β ≠ 1`.

`E8SharpGaussianSchwartzInput8` asks for a Schwartz function below the Gaussian `exp(-π β |x|²)`
with nonnegative Fourier transform and the sharp value `𝓕f(0) - f(0) = Θ_{E8}(β) - 1` at EVERY
scale `β > 0`.  The proof of the profile uses it only at a scale `α L²` with a free dilation
`L > 1` near one, so one scale can be avoided: the same profile follows from the input at the
scales `β ≠ 1`.  This matters because the kernel inequality of `E8` gives the certificates away
from the self-dual scale `β = 1` (the scale `α = π` of the Gaussian `exp(-α |x|²)`). -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap
namespace SphericalRiesz

/-- A dilation `L > 1` near one that keeps the theta value and avoids the scale `α L² = 1`. -/
theorem e8GaussianThetaReal8_exists_near_one_dilation_ne {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ L : ℝ, 1 < L ∧ α*L^2 ≠ 1 ∧ e8GaussianThetaReal8 α-ε < e8GaussianThetaReal8 (α*L^2) := by
  have hc : ContinuousAt e8GaussianThetaReal8 α :=
    e8GaussianThetaReal8_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hα)
  have hL : Tendsto (fun L : ℝ => α*L^2) (𝓝[>] (1 : ℝ)) (𝓝 α) := by
    have h : ContinuousAt (fun L : ℝ => α*L^2) 1 := by fun_prop
    simpa only [one_pow, mul_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hc.tendsto.comp hL
  have he : ∀ᶠ L in 𝓝[>] (1 : ℝ), e8GaussianThetaReal8 α-ε < e8GaussianThetaReal8 (α*L^2) :=
    (tendsto_order.mp ht).1 _ (by linarith)
  have hlo : ∀ᶠ L in 𝓝[>] (1 : ℝ), 1 < L := self_mem_nhdsWithin
  have hne : ∀ᶠ L in 𝓝[>] (1 : ℝ), α*L^2 ≠ 1 := by
    rcases lt_or_ge α 1 with hα1 | hα1
    · filter_upwards [(tendsto_order.mp hL).2 1 hα1] with L hL1
      exact hL1.ne
    · filter_upwards [hlo] with L hL1
      have hsq : 1 < L^2 := by nlinarith
      have : α < α*L^2 := by nlinarith
      linarith
  obtain ⟨L, ⟨hL1, hLne⟩, hLθ⟩ := ((hlo.and hne).and he).exists
  exact ⟨L, hL1, hLne, hLθ⟩

/-- The all-scale Gaussian input of `E8` away from the self-dual scale `β = 1`, stated with
actual Schwartz maps, the Fourier transform of Mathlib, the Gaussian and the theta sum of `E8`. -/
def E8SharpGaussianSchwartzInputOff8 : Prop :=
  ∀ β : ℝ, 0 < β → β ≠ 1 → ∃ f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ),
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧
    (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*β*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = e8GaussianThetaReal8 β-1

/-- The input at every scale gives the input away from `β = 1`. -/
theorem E8SharpGaussianSchwartzInput8.off (h : E8SharpGaussianSchwartzInput8) :
    E8SharpGaussianSchwartzInputOff8 :=
  fun β hβ _ => h β hβ

/-- The sharp lower Gaussian profile of `S⁸` needs the Gaussian input only at the scales
`β ≠ 1`. -/
theorem sphereGaussianSharpProfileLower8_of_schwartz_input_off
    (hG8 : E8SharpGaussianSchwartzInputOff8) : SphereGaussianSharpProfileLower8 := by
  intro N hN hN0 X α hα ε hε
  obtain ⟨L,hL,hLne,hθ⟩ :=
    e8GaussianThetaReal8_exists_near_one_dilation_ne hα (by positivity : 0 < ε/2)
  obtain ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,_hwc,_hw,_hpart,hLip⟩ :=
    sphere8_exists_finite_cutoff_square_partition L hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  obtain ⟨f,hFnonneg,hFreal,hminor,hvalue⟩ := hG8 (α*L^2) (by positivity) hLne
  have he := sphereGaussian8_uniform_lower_of_schwartz ρ hρ' hr g hc hpos L α hL0.le hα.le
    hLip f hFnonneg hFreal hminor hN hN0 (ε/2) (by positivity)
  filter_upwards [he] with k hk
  have hx := hk (fun i => X k i)
  change e8GaussianThetaReal8 α-ε ≤
    (∑ p, ∑ q, sphereGaussianKernel8 (sphereGaussianScale8 (N k) α) (X k p) (X k q))/(N k : ℝ)
  linarith

/-- The main target `S8s4Target` from the Gaussian input away from `β = 1`. -/
theorem S8s4Target_of_schwartz_input_off (hG8 : E8SharpGaussianSchwartzInputOff8) :
    S8s4Target :=
  S8s4Target_of_gaussian_profile (sphereGaussianSharpProfileLower8_of_schwartz_input_off hG8)

end SphericalRiesz
