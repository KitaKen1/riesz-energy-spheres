import Riesz.SphereLogEnergy8

/-! The universal sharp lower bound for the logarithmic energy on S⁸ (stage LOG, first half).

With `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα` and the E8 profile
`g(α) = α⁻¹ (Θ(α) - α⁻⁴ - 1 + 1_{(0,1)}(α))` (integrable: it is the real part of
`α⁻¹ f_modif(α)` of the strong FE pair minus `1_{(1,∞)} α⁻⁵`), Fatou with the majorant
`1_{(1,∞)} α⁻⁵` (from `F ≥ -min(1, α⁻⁴)`) and `F + 1 ≥ 0` on `(0,1)` gives
`liminf J_N ≥ ∫ g` uniformly over configurations. Hence, under the sharp sphere Gaussian
profile (G8 / CKMRV contract), for every `η > 0` and all large `N` and every configuration,
`(E_log - W N² + (N/8) log N)/N ≥ C_log - η`,
`C_log = ½ (∫ g + κ - log π + ¼ log A₈)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The weighted logarithmic E8 profile `α⁻¹ (Θ(α) - α⁻⁴ - 1 + 1_{(0,1)}(α))`. -/
def e8GaussianLogProfile8 (α : ℝ) : ℝ :=
  α⁻¹*(e8GaussianThetaReal8 α-(α^4)⁻¹-1+(Ioo (0:ℝ) 1).indicator 1 α)

theorem e8GaussianLogProfile8_ae :
    e8GaussianLogProfile8 =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t).re -
        (Ioi 1).indicator (fun t : ℝ => t^(-5:ℝ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  have hc : (t:ℂ)^((0:ℂ)-1) = ((t⁻¹:ℝ):ℂ) := by
    rw [zero_sub, Complex.cpow_neg_one, Complex.ofReal_inv]
  have h4 : ((t^(-(4:ℝ)) : ℝ) : ℂ) = ((t:ℂ)^4)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_ofNat, Complex.ofReal_inv, Complex.ofReal_pow]
  have h5 : t^(-5:ℝ) = t⁻¹*(t^4)⁻¹ := by
    rw [Real.rpow_neg ht0.le, show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  simp only [WeakFEPair.f_modif, e8ThetaFEPair, Pi.add_apply, hc, smul_eq_mul]
  unfold e8GaussianLogProfile8 e8GaussianThetaReal8
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hA : t ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    have hB : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, hsmall⟩
    simp only [indicator_of_notMem hA, indicator_of_mem hB, h4, Pi.one_apply, one_mul,
      sub_zero]
    try rw [Complex.re_ofReal_mul]
    have hre : (0+(e8ThetaImag t-((t:ℂ)^4)⁻¹*1)).re = (e8ThetaImag t).re-(t^4)⁻¹ := by
      rw [zero_add, mul_one, Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
        Complex.ofReal_re]
    rw [hre]
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, zero_add, add_zero]
    rw [Complex.re_ofReal_mul, h5]
    simp only [Complex.sub_re, Complex.one_re]
    ring

theorem e8GaussianLogProfile8_integrable : IntegrableOn e8GaussianLogProfile8 (Ioi 0) := by
  have hmod : IntegrableOn (fun t : ℝ => ((t:ℂ)^((0:ℂ)-1)) • e8ThetaFEPair.f_modif t) (Ioi 0) :=
    (e8ThetaFEPair.isStrongFEPair_toStrongFEPair.hasMellin (0:ℂ)).1
  have h5 : IntegrableOn (fun t : ℝ => t^(-5:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hl := (h5.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  exact (hmod.re.sub hl).congr_fun_ae e8GaussianLogProfile8_ae.symm

/-- The majorant `1_{(1,∞)} α⁻¹ α⁻⁴` for the logarithmic Fatou argument. -/
def logMajorant8 (α : ℝ) : ℝ := (Ioi (1:ℝ)).indicator (fun α => α⁻¹*(α^4)⁻¹) α

theorem logMajorant8_integrable : IntegrableOn logMajorant8 (Ioi 0) := by
  have h5 : IntegrableOn (fun t : ℝ => t^(-5:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have h5' : IntegrableOn (fun t : ℝ => t⁻¹*(t^4)⁻¹) (Ioi 1) := by
    refine h5.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
    dsimp only
    rw [Real.rpow_neg ht0.le, show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  exact (h5'.integrable_indicator measurableSet_Ioi).integrableOn

theorem logMajorant8_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ logMajorant8 α := by
  unfold logMajorant8
  by_cases h : α ∈ Ioi (1:ℝ)
  · rw [indicator_of_mem h]; positivity
  · rw [indicator_of_notMem h]

theorem sphereGaussianCenteredScaled8_log_lower {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≠ 1) (X : Configuration N) :
    -logMajorant8 α ≤
      α⁻¹*(sphereGaussianCenteredScaled8 α X+(Ioo (0:ℝ) 1).indicator 1 α) := by
  rcases lt_or_gt_of_ne hα1 with hsmall | hlarge
  · have hB : α ∈ Ioo (0:ℝ) 1 := ⟨hα, hsmall⟩
    have hA : α ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    unfold logMajorant8
    rw [indicator_of_notMem hA, indicator_of_mem hB, Pi.one_apply, neg_zero]
    exact mul_nonneg (inv_nonneg.mpr hα.le)
      (sphereGaussianCenteredScaled8_add_one_nonneg hN hα.le X)
  · have hA : α ∈ Ioi (1:ℝ) := hlarge
    have hB : α ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    unfold logMajorant8
    rw [indicator_of_mem hA, indicator_of_notMem hB, add_zero]
    have h := sphereGaussianCenteredScaled8_weighted_lower_rpow hN 0 hα X
    rw [sphereGaussianMajorant8_large 0 hlarge.le] at h
    have he : α^((0:ℝ)/2-1) = α⁻¹ := by
      rw [show (0:ℝ)/2-1 = -1 by norm_num, Real.rpow_neg_one]
    have he5 : α^((0:ℝ)/2-5) = α⁻¹*(α^4)⁻¹ := by
      rw [show (0:ℝ)/2-5 = -5 by norm_num, Real.rpow_neg hα.le,
        show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [he, he5] at h
    exact h

theorem sphereGaussianCenteredScaled8_log_profile_eventually
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianLogProfile8 α-ε ≤
        α⁻¹*(sphereGaussianCenteredScaled8 α (X k)+(Ioo (0:ℝ) 1).indicator 1 α) := by
  intro ε hε
  have hw : 0 < α⁻¹ := inv_pos.mpr hα
  filter_upwards [hp (ε*α) (mul_pos hε hα)] with k hk
  have hb := sphereGaussianCenteredScaled8_ge_flat (hN k) hα (X k)
  have he : α⁻¹*(ε*α) = ε := by field_simp
  unfold e8GaussianLogProfile8
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_log_integral_lower
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, Configuration (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      e8GaussianThetaReal8 α-ε ≤ sphereGaussianFullScaled8 α (X k))
    {C : ℝ} (hC : ∀ k, sphereLogProfileIntegral8 (X k) ≤ C) :
    (∫ α : ℝ in Ioi 0, e8GaussianLogProfile8 α) ≤ C := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  exact integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := e8GaussianLogProfile8) (M := logMajorant8)
    (f := fun k α => α⁻¹*(sphereGaussianCenteredScaled8 α (X k)+(Ioo (0:ℝ) 1).indicator 1 α))
    e8GaussianLogProfile8_integrable
    (fun k => sphereGaussianCenteredScaled8_log_integrable (hN k) (X k))
    logMajorant8_integrable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact logMajorant8_nonneg hα)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with α hα hα1
      exact sphereGaussianCenteredScaled8_log_lower (hN k) hα hα1 (X k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled8_log_profile_eventually hN X hα (hp α hα))
    hC

/-- The conjectured logarithmic coefficient, as a Gaussian profile integral. -/
def sphereLogCoefficient8 : ℝ :=
  (1/2)*((∫ α : ℝ in Ioi 0, e8GaussianLogProfile8 α)+logGaussianConst-
    Real.log Real.pi+(1/4)*Real.log (sphereArea8.real univ))

/-- Universal sharp lower bound for the logarithmic energy from the pointwise sharp sphere
Gaussian profile. -/
theorem sphere8_log_lower_of_gaussian_profile (hp : SphereGaussianSharpProfileLower8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, sphereLogCoefficient8-η ≤ normalizedEnergyLog8 X := by
  classical
  intro η hη
  by_contra h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : Configuration N, normalizedEnergyLog8 X < sphereLogCoefficient8-η := by
    intro k
    by_contra hk
    apply h
    refine ⟨k+1, fun N hN X => ?_⟩
    by_contra hX
    exact hk ⟨N, hN, X, lt_of_not_ge hX⟩
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  set K := logGaussianConst-Real.log Real.pi+(1/4)*Real.log (sphereArea8.real univ) with hK
  have hJ : ∀ k, sphereLogProfileIntegral8 (X k) ≤ (∫ α : ℝ in Ioi 0, e8GaussianLogProfile8 α)-2*η := by
    intro k
    have h1 := normalizedEnergyLog8_gaussian_mellin (hN0 k) (X k)
    have h2 := hX k
    unfold sphereLogCoefficient8 at h2
    rw [h1] at h2
    linarith
  have hc := sphereGaussianSequence_log_integral_lower hN0 X (hp N ht hN0 X) hJ
  linarith

/-- The universal logarithmic lower bound under the CKMRV Laplace–sine contract. -/
theorem sphere8_log_lower_of_laplaceSineData (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Configuration N, sphereLogCoefficient8-η ≤ normalizedEnergyLog8 X :=
  sphere8_log_lower_of_gaussian_profile
    (sphereGaussianSharpProfileLower8_of_schwartz_input
      (e8SharpGaussianSchwartzInput8_of_contact (fun _ hβ => ⟨_, D.certificate hβ⟩)))

#print axioms e8GaussianLogProfile8_ae
#print axioms e8GaussianLogProfile8_integrable
#print axioms logMajorant8_integrable
#print axioms logMajorant8_nonneg
#print axioms sphereGaussianCenteredScaled8_log_lower
#print axioms sphereGaussianCenteredScaled8_log_profile_eventually
#print axioms sphereGaussianSequence_log_integral_lower
#print axioms sphere8_log_lower_of_gaussian_profile
#print axioms sphere8_log_lower_of_laplaceSineData

end SphericalRiesz
