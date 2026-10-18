import Riesz.SpherePartitionGaussianComparison8

/-! Configuration-uniform sphere Gaussian localization from explicit actual
Schwartz inputs. The only deep input below is a precisely stated, UNPROVED
all-scale E8 minorant existence proposition. It is not an axiom or a proof
of that proposition. Finite PSD, Gaussian comparison, uniform actual sphere
rows/backgrounds, exact density and L decreasing to one are proved here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
namespace SphericalRiesz

theorem spherePartitionSchwartzRow8_sum_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hN : 0 < N) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a H δ : ℝ)
    (hrow : ∀ x, |(N : ℝ)*spherePartitionSchwartzRow8 ρ hρ g f a x-H| < δ) :
    H-δ ≤ ∑ p, spherePartitionSchwartzRow8 ρ hρ g f a (X p) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp (p : Fin N) : H-δ ≤ (N : ℝ)*spherePartitionSchwartzRow8 ρ hρ g f a (X p) := by
    have h := (abs_lt.mp (hrow (X p))).1
    linarith
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N))) => hp p)
  have hs' : (N : ℝ)*(H-δ) ≤ (N : ℝ)*(∑ p, spherePartitionSchwartzRow8 ρ hρ g f a (X p)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] using hs
  nlinarith

theorem sphereGaussian8_uniform_lower_of_schwartz {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (L α : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight8 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates8 (g i) x-
        rotatedSphereEqualAreaCoordinates8 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2)))
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hN0 : ∀ k, 0 < N k) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ X : Fin (N k) → Sphere8,
      ((𝓕 f) 0).re+1-(f 0).re-ε ≤
        (∑ p, ∑ q, sphereGaussianKernel8 (sphereGaussianScale8 (N k) α) (X p) (X q))/(N k : ℝ) := by
  intro ε hε
  let δ : ℝ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrow := spherePartitionSchwartzRow8_density_uniform ρ hρ hr g hc hpos f hN hN0 δ hδ
  have hbg : ∀ᶠ k in atTop, (N k : ℝ)*
      spherePartitionSchwartzBackground8 ρ hρ g f (spherePartitionDensityScale8 (N k)) < ((𝓕 f) 0).re+δ :=
    (tendsto_order.mp (spherePartitionSchwartzBackground8_density_tendsto ρ hρ hr g hc hpos f hN hN0)).2
      _ (by linarith)
  filter_upwards [hrow,hbg] with k hk hb
  intro X
  have hmin : ∀ x y, spherePartitionSchwartzKernel8 ρ hρ g f (spherePartitionDensityScale8 (N k)) x y ≤
      sphereGaussianKernel8 (sphereGaussianScale8 (N k) α) x y := by
    intro x y
    rw [sphereGaussianScale8_eq_partition_density]
    exact spherePartitionSchwartzKernel8_gaussian_le ρ hρ g hpos L α _ hL hα hLip f hminor x y
  have hsum := spherePartitionSchwartzRow8_sum_lower ρ hρ g (hN0 k) X f _ _ _ hk
  have hd := spherePartitionGaussian8_normalized_lower ρ hρ g hc hpos (hN0 k) X f
    hFnonneg hFreal (spherePartitionDensityScale8 (N k)) (sphereGaussianScale8 (N k) α) hmin
  dsimp [δ] at *
  linarith

theorem e8GaussianThetaReal8_continuousOn : ContinuousOn e8GaussianThetaReal8 (Ioi 0) := by
  exact Complex.continuous_re.comp_continuousOn e8ThetaImag_continuousOn

theorem e8GaussianThetaReal8_exists_near_one_dilation {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ L : ℝ, 1 < L ∧ e8GaussianThetaReal8 α-ε < e8GaussianThetaReal8 (α*L^2) := by
  have hc : ContinuousAt e8GaussianThetaReal8 α :=
    e8GaussianThetaReal8_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hα)
  have hL : Tendsto (fun L : ℝ => α*L^2) (𝓝[>] (1 : ℝ)) (𝓝 α) := by
    have h : ContinuousAt (fun L : ℝ => α*L^2) 1 := by fun_prop
    simpa only [one_pow, mul_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hc.tendsto.comp hL
  have he : ∀ᶠ L in 𝓝[>] (1 : ℝ), e8GaussianThetaReal8 α-ε < e8GaussianThetaReal8 (α*L^2) :=
    (tendsto_order.mp ht).1 _ (by linarith)
  have hlo : ∀ᶠ L in 𝓝[>] (1 : ℝ), 1 < L := self_mem_nhdsWithin
  exact (hlo.and he).exists

/-- The missing all-scale Gaussian input, stated using actual Schwartz maps,
actual Mathlib Fourier transform, actual Gaussian and actual E8 theta.
No proof of this existence statement is supplied by defining it. -/
def E8SharpGaussianSchwartzInput8 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ),
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧
    (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*β*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = e8GaussianThetaReal8 β-1

theorem sphereGaussianSharpProfileLower8_of_schwartz_input (hG8 : E8SharpGaussianSchwartzInput8) :
    SphereGaussianSharpProfileLower8 := by
  intro N hN hN0 X α hα ε hε
  obtain ⟨L,hL,hθ⟩ := e8GaussianThetaReal8_exists_near_one_dilation hα (by positivity : 0 < ε/2)
  obtain ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,_hwc,_hw,_hpart,hLip⟩ :=
    sphere8_exists_finite_cutoff_square_partition L hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  obtain ⟨f,hFnonneg,hFreal,hminor,hvalue⟩ := hG8 (α*L^2) (by positivity)
  have he := sphereGaussian8_uniform_lower_of_schwartz ρ hρ' hr g hc hpos L α hL0.le hα.le
    hLip f hFnonneg hFreal hminor hN hN0 (ε/2) (by positivity)
  filter_upwards [he] with k hk
  have hx := hk (fun i => X k i)
  change e8GaussianThetaReal8 α-ε ≤
    (∑ p, ∑ q, sphereGaussianKernel8 (sphereGaussianScale8 (N k) α) (X k p) (X k q))/(N k : ℝ)
  linarith

theorem S8s4Target_of_schwartz_input (hG8 : E8SharpGaussianSchwartzInput8) : S8s4Target :=
  S8s4Target_of_gaussian_profile (sphereGaussianSharpProfileLower8_of_schwartz_input hG8)

end SphericalRiesz
