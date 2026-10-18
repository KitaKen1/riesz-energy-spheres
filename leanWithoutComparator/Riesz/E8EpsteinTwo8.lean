import Riesz.E8EpsteinStrip8

/-! The removable point `s = 2` of the all-exponent coefficient.

At `u = 1` the candidate `π^(-u) Γ(u) 2^(-u) 240 ζ(u) ζ(u-3)` is a product of the pole of `ζ` at `1`
and the trivial zero `ζ(-2) = 0`. Writing `ζ(u) ζ(u-3) = ((u-1) ζ(u)) · (ζ(u-3)/(u-1))`, the residue
`(u-1) ζ(u) → 1` and the slope `ζ(u-3)/(u-1) → ζ'(-2)` give the limit `π⁻¹ · 120 · ζ'(-2)`. The
completed theta value is continuous at `1` and agrees with the candidate at nearby real points, so
`C₂ = A₈^(-1/4) · 120 · Re ζ'(-2)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem riemannZeta_slope_neg_two :
    Tendsto (fun u : ℂ => riemannZeta (u-3)/(u-1)) (𝓝[≠] (1:ℂ)) (𝓝 (deriv riemannZeta (-2))) := by
  have hd : HasDerivAt riemannZeta (deriv riemannZeta (-2)) (-2) :=
    (differentiableAt_riemannZeta (by norm_num)).hasDerivAt
  have hs := hd.tendsto_slope_zero
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  have hmap : Tendsto (fun u : ℂ => u-1) (𝓝[≠] (1:ℂ)) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun u : ℂ => u-1) (𝓝 (1:ℂ)) (𝓝 ((1:ℂ)-1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_ne_zero.mpr hu
  have h := hs.comp hmap
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [Function.comp_apply, smul_eq_mul, hz, sub_zero]
  rw [show (-2:ℂ)+(u-1) = u-3 by ring, div_eq_inv_mul]

theorem e8CompletedCandidate_tendsto_one :
    Tendsto e8CompletedCandidate (𝓝[≠] (1:ℂ))
      (𝓝 ((Real.pi:ℂ)^(-(1:ℂ)) * Complex.Gamma 1 *
        ((2:ℂ)^(-(1:ℂ)) * (240 * (1 * deriv riemannZeta (-2)))))) := by
  have hpi : Tendsto (fun u : ℂ => (Real.pi:ℂ)^(-u)) (𝓝[≠] (1:ℂ)) (𝓝 ((Real.pi:ℂ)^(-(1:ℂ)))) := by
    have hc : ContinuousAt (fun u : ℂ => (Real.pi:ℂ)^(-u)) 1 :=
      (continuousAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hΓ : Tendsto Complex.Gamma (𝓝[≠] (1:ℂ)) (𝓝 (Complex.Gamma 1)) := by
    have hc : ContinuousAt Complex.Gamma 1 :=
      (Complex.differentiableAt_Gamma 1 (fun m h => by
        have hre := congrArg Complex.re h
        simp at hre
        linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).continuousAt
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have htwo : Tendsto (fun u : ℂ => (2:ℂ)^(-u)) (𝓝[≠] (1:ℂ)) (𝓝 ((2:ℂ)^(-(1:ℂ)))) := by
    have hc : ContinuousAt (fun u : ℂ => (2:ℂ)^(-u)) 1 :=
      (continuousAt_id.neg.const_cpow (Or.inl (by norm_num)))
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hres := riemannZeta_residue_one
  have hslope := riemannZeta_slope_neg_two
  have hprod := (hres.mul hslope).const_mul (240:ℂ)
  have hall := (hpi.mul hΓ).mul (htwo.mul hprod)
  apply hall.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu1 : u-1 ≠ 0 := sub_ne_zero.mpr hu
  simp only [e8CompletedCandidate, e8EpsteinCandidate]
  field_simp

theorem e8ThetaCompleted_at_one :
    e8ThetaCompleted (1:ℂ) = (Real.pi:ℂ)^(-(1:ℂ)) * Complex.Gamma 1 *
      ((2:ℂ)^(-(1:ℂ)) * (240 * (1 * deriv riemannZeta (-2)))) := by
  have hreal : Tendsto (fun u : ℝ => (u:ℂ)) (𝓝[≠] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : u ≠ 1 := Set.mem_compl_singleton_iff.mp hu
      exact Set.mem_compl_singleton_iff.mpr (by exact_mod_cast hu')
  have hc : ContinuousAt e8ThetaCompleted (1:ℂ) :=
    (e8ThetaCompleted_differentiableAt (by norm_num) (by norm_num)).continuousAt
  have h1 : Tendsto (fun u : ℝ => e8ThetaCompleted (u:ℂ)) (𝓝[≠] (1:ℝ)) (𝓝 (e8ThetaCompleted 1)) :=
    (hc.tendsto.comp ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)) |>.congr
      (fun u => by simp)
  have h2 := e8CompletedCandidate_tendsto_one.comp hreal
  apply tendsto_nhds_unique h1
  apply h2.congr'
  have hnear : ∀ᶠ u : ℝ in 𝓝[≠] (1:ℝ), u ∈ Ioo (0:ℝ) 4 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hnear, self_mem_nhdsWithin] with u hu hu1
  exact (e8ThetaCompleted_eq_candidate_real hu.1 hu.2 hu1).symm

/-- The coefficient at `s = 2`: `C₂ = A₈^(-1/4) · 120 · Re ζ'(-2)`. -/
theorem sphereRieszCoefficient8_two :
    sphereRieszCoefficient8 2 =
      (sphereArea8.real univ)^(-((2:ℝ)/8)) * (120 * (deriv riemannZeta (-2)).re) := by
  unfold sphereRieszCoefficient8
  rw [e8GaussianRieszProfileRpow8_integral_eq (by norm_num) (by norm_num)]
  have h1 : (((2:ℝ)/2:ℝ):ℂ) = 1 := by norm_num
  rw [h1, e8ThetaCompleted_at_one, Complex.Gamma_one]
  have hP : (Real.pi:ℂ)^(-(1:ℂ)) = ((Real.pi⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_neg_one]
    push_cast
    rfl
  have h2 : (2:ℂ)^(-(1:ℂ)) = (((2:ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_neg_one]
    push_cast
    rfl
  rw [hP, h2]
  have hre : ((((Real.pi⁻¹:ℝ):ℂ) * 1 * ((((2:ℝ)⁻¹:ℝ):ℂ) * (240 * (1 * deriv riemannZeta (-2)))))).re =
      Real.pi⁻¹ * (120 * (deriv riemannZeta (-2)).re) := by
    simp only [mul_one, one_mul, ← mul_assoc]
    rw [show (((Real.pi⁻¹:ℝ):ℂ) * (((2:ℝ)⁻¹:ℝ):ℂ) * 240) = (((Real.pi⁻¹ * 120 : ℝ)):ℂ) by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hre]
  have hΓ : Real.Gamma ((2:ℝ)/2) = 1 := by norm_num
  have hpi : Real.pi^((2:ℝ)/2) = Real.pi := by norm_num
  rw [hΓ, hpi, div_one]
  field_simp

#print axioms riemannZeta_slope_neg_two
#print axioms e8CompletedCandidate_tendsto_one
#print axioms e8ThetaCompleted_at_one
#print axioms sphereRieszCoefficient8_two

end SphericalRiesz
