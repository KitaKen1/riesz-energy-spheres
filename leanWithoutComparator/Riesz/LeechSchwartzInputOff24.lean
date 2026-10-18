import Riesz.LeechProfileLower24

/-! The sharp lower Gaussian profile of `S²⁴` from certificates at the scales `β ≠ 1`.

`LeechSharpGaussianSchwartzInput24` asks for a Schwartz function below the Gaussian
`exp(-π β |x|²)` with nonnegative Fourier transform and the sharp value
`𝓕f(0) - f(0) = Θ_Leech(β) - 1` at EVERY scale `β > 0`.  The proof of the profile uses it only
at a scale `α L²` with a free dilation `L > 1` near one, so one scale can be avoided: the same
profile follows from the input at the scales `β ≠ 1`.  The kernel inequalities of the Leech
lattice give the certificates away from the self-dual scale `β = 1` (the scale `α = π` of the
Gaussian `exp(-α |x|²)`), as for `E8` (`Riesz/E8SchwartzInputOff8.lean`). -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology FourierTransform SchwartzMap
namespace SphericalRiesz

/-- A dilation `L > 1` near one that keeps the theta value and avoids the scale `α L² = 1`. -/
theorem leechGaussianThetaReal24_exists_near_one_dilation_ne {α ε : ℝ} (hα : 0 < α)
    (hε : 0 < ε) :
    ∃ L : ℝ, 1 < L ∧ α*L^2 ≠ 1 ∧
      leechGaussianThetaReal24 α-ε < leechGaussianThetaReal24 (α*L^2) := by
  have hc : ContinuousAt leechGaussianThetaReal24 α :=
    leechGaussianThetaReal24_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hα)
  have hL : Tendsto (fun L : ℝ => α*L^2) (𝓝[>] (1 : ℝ)) (𝓝 α) := by
    have h : ContinuousAt (fun L : ℝ => α*L^2) 1 := by fun_prop
    simpa only [one_pow, mul_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hc.tendsto.comp hL
  have he : ∀ᶠ L in 𝓝[>] (1 : ℝ),
      leechGaussianThetaReal24 α-ε < leechGaussianThetaReal24 (α*L^2) :=
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

/-- The all-scale Gaussian input of the Leech lattice away from the self-dual scale `β = 1`. -/
def LeechSharpGaussianSchwartzInputOff24 : Prop :=
  ∀ β : ℝ, 0 < β → β ≠ 1 → ∃ f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ),
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧
    (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*β*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = leechGaussianThetaReal24 β-1

/-- The input at every scale gives the input away from `β = 1`. -/
theorem LeechSharpGaussianSchwartzInput24.off (h : LeechSharpGaussianSchwartzInput24) :
    LeechSharpGaussianSchwartzInputOff24 :=
  fun β hβ _ => h β hβ

/-- The sharp lower Gaussian profile of `S²⁴` needs the Gaussian input only at the scales
`β ≠ 1`. -/
theorem sphereGaussianSharpProfileLower24_of_schwartz_input_off
    (hG24 : LeechSharpGaussianSchwartzInputOff24) : SphereGaussianSharpProfileLower24 := by
  intro N hN hN0 X α hα ε hε
  obtain ⟨L,hL,hLne,hθ⟩ :=
    leechGaussianThetaReal24_exists_near_one_dilation_ne hα (by positivity : 0 < ε/2)
  obtain ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,_hwc,_hw,_hpart,hLip⟩ :=
    sphere24_exists_finite_cutoff_square_partition L hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  obtain ⟨f,hFnonneg,hFreal,hminor,hvalue⟩ := hG24 (α*L^2) (by positivity) hLne
  have he := sphereGaussian24_uniform_lower_of_schwartz ρ hρ' hr g hc hpos L α hL0.le hα.le
    hLip f hFnonneg hFreal hminor hN hN0 (ε/2) (by positivity)
  filter_upwards [he] with k hk
  have hx := hk (fun i => X k i)
  change leechGaussianThetaReal24 α-ε ≤
    (∑ p, ∑ q, sphereGaussianKernel24 (sphereGaussianScale24 (N k) α) (X k p) (X k q))/(N k : ℝ)
  linarith

end SphericalRiesz
