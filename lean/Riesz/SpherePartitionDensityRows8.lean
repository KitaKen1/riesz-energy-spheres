import Riesz.SpherePartitionUniformRows8
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual density scale a_N=(N/A8)^(1/8), with exact N=a_N^8*A8,
and uniform original sphere rows/backgrounds along every positive cardinality
sequence tending to infinity. No sharp Gaussian certificate is provided. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
namespace SphericalRiesz

def spherePartitionDensityScale8 (N : ℕ) : ℝ :=
  ((N : ℝ)/sphereArea8.real univ)^((8 : ℝ)⁻¹)

theorem spherePartitionDensityScale8_pos {N : ℕ} (hN : 0 < N) :
    0 < spherePartitionDensityScale8 N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  exact Real.rpow_pos_of_pos (div_pos hNR hA) _

theorem spherePartitionDensityScale8_pow (N : ℕ) :
    (spherePartitionDensityScale8 N)^8 = (N : ℝ)/sphereArea8.real univ := by
  apply Real.rpow_inv_natCast_pow
  · have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
    exact div_nonneg (Nat.cast_nonneg _) hA.le
  · decide

theorem spherePartitionDensityScale8_mass (N : ℕ) :
    (spherePartitionDensityScale8 N)^8*sphereArea8.real univ = (N : ℝ) := by
  have hA : sphereArea8.real univ ≠ 0 := by rw [sphereArea8_mass_real]; positivity
  rw [spherePartitionDensityScale8_pow, div_mul_cancel₀ _ hA]

theorem spherePartitionDensityScale8_tendsto :
    Tendsto spherePartitionDensityScale8 atTop atTop := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ => (N : ℝ)/sphereArea8.real univ) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hN.eventually (eventually_ge_atTop (b*sphereArea8.real univ))] with N hN
    exact (le_div_iff₀ hA).mpr hN
  exact (tendsto_rpow_atTop (by positivity : 0 < (8 : ℝ)⁻¹)).comp hdiv

theorem spherePartitionSchwartzRow8_density_uniform {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN0 : ∀ n, 0 < N n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(N n : ℝ)*spherePartitionSchwartzRow8 ρ hρ g f (spherePartitionDensityScale8 (N n)) x-
        ((𝓕 f) 0).re| < ε := by
  have h := spherePartitionSchwartzRow8_uniform ρ hρ hr g hc hpos f
    (spherePartitionDensityScale8_tendsto.comp hN) (fun n => spherePartitionDensityScale8_pos (hN0 n))
  simpa only [Function.comp_apply, spherePartitionDensityScale8_mass] using h

theorem spherePartitionSchwartzBackground8_density_tendsto {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN0 : ∀ n, 0 < N n) :
    Tendsto (fun n => (N n : ℝ)*
      spherePartitionSchwartzBackground8 ρ hρ g f (spherePartitionDensityScale8 (N n)))
      atTop (𝓝 ((𝓕 f) 0).re) := by
  have h := spherePartitionSchwartzBackground8_scaled_tendsto ρ hρ hr g hc hpos f
    (spherePartitionDensityScale8_tendsto.comp hN) (fun n => spherePartitionDensityScale8_pos (hN0 n))
  simpa only [Function.comp_apply, spherePartitionDensityScale8_mass] using h

theorem sphere8_exists_uniform_partition_schwartz_rows (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ∃ hρ : 0 < ρ, ρ ≤ 1/8 ∧
      ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
        Continuous (sphereChartCutoff8 ρ hρ) ∧
        (∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) ∧
        (∀ x, (∑ i, (sphereFiniteCutoffWeight8 ρ hρ g i x)^2) = 1) ∧
        (∀ i x y, sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0 →
          sphereFiniteCutoffWeight8 ρ hρ g i y ≠ 0 →
          dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates8 (g i) x-
            rotatedSphereEqualAreaCoordinates8 (g i) y‖) ∧
        (∀ (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (N : ℕ → ℕ),
          Tendsto N atTop atTop → (∀ n, 0 < N n) →
          ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
            |(N n : ℝ)*spherePartitionSchwartzRow8 ρ hρ g f (spherePartitionDensityScale8 (N n)) x-
              ((𝓕 f) 0).re| < ε) := by
  obtain ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,_hwc,_hw,hpart,hLip⟩ :=
    sphere8_exists_finite_cutoff_square_partition L hL
  exact ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,hpart,hLip,
    fun f N hN hN0 => spherePartitionSchwartzRow8_density_uniform ρ hρ' hr g hc hpos f hN hN0⟩

end SphericalRiesz
