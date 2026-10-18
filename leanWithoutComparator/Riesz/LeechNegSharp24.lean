import Riesz.LeechNegBlock24
import Riesz.NegMassSplit8
import Riesz.SphereStratification24

/-! # Negative exponents `-2 < s < 0` on `S²⁴` for every large `N`, and the sharp statements

Two parts.

* Every large size.  The block configurations exist at the rational sizes `M = (d m)²⁴` only.
  For a size `N` between two rational sizes the `M ≤ N` points of a block are kept (against
  `M σ`) and the `N - M` missing points are chosen one per cell of an exact-mass stratification
  of the whole sphere at their own scale (against `(N-M) σ`), jointly for the subtracted
  macroscopic kernel with the density factor of `N` and one Gaussian window: Cauchy–Schwarz with
  two densities, the substitution `β = l α` with `l = (N/M)^(1/12) ∈ [1,2]`, and cell costs
  `B N/L²` as soon as `N - M ≤ N/L¹⁴`.  A diagonal choice over the tolerance index and the
  transfer theorem give configurations of every large size with normalized energy at least
  `C_s - η`.
* Statements.  The continuous constant is the actual double integral of `|x-y|^|s|`, the two
  stratification hypotheses are discharged by `Riesz.SphereStratification24`, and the results
  are stated in the form of the conjecture: the lower half without hypotheses, the universal
  upper half and the two-sided statement under all-scale Leech contact certificates (stage G24,
  not proved in this project). -/

section

/-! Negative exponents on S²⁴ for every large `N` (stage NEG, all `N`).

The block configurations exist at the rational sizes `M = (d m)²⁴` only.  For a size `N` between
two rational sizes the `M ≤ N` points of a block are kept (against `M σ`) and the `r = N - M`
missing points are chosen one per cell of an exact-mass stratification of the whole sphere at
their own scale (against `r σ`), jointly for the subtracted macroscopic kernel with the density
factor `c_N` and one Gaussian window.

* Cauchy–Schwarz with two densities: `D(μ₁+μ₂, (M+r) σ) ≤ 2 D(μ₁, M σ) + 2 D(μ₂, r σ)`.
* The kept points at the scale of `N`: `c_N α = c_M (l α)` with `l = (N/M)^(1/12) ∈ [1,2]`, so the
  kept part of the macroscopic end is the block integral up to the substitution `β = l α`.
* The added points: `Σ_j c_N d_j² = (N/r)^(1/12) Σ_j c_r d_j² ≤ B (N/r)^(1/12) r ≤ B N/L²` as
  soon as `r ≤ N/L¹⁴`, and the background of the residual window is at most `N/L²`.

Hence, for every tolerance index `L`, every large `N` carries a configuration with a Gaussian
window and a small macroscopic end, and a diagonal choice with the transfer theorem gives
configurations of every large size whose normalized negative-exponent energy is at least
`C_s - η`.  The two stratifications are hypotheses of this file; they are discharged
separately. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

/-! ### Rational sizes below a given size -/

def rationalSizeFloorIndex24 (d N : ℕ) : ℕ :=
  ⌊((N:ℝ) ^ (1/24:ℝ))/(d:ℝ)⌋₊

def rationalSizeFloor24 (d N : ℕ) : ℕ := (d*rationalSizeFloorIndex24 d N)^24

theorem rationalSizeFloorIndex24_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (rationalSizeFloorIndex24 d) atTop atTop :=
  tendsto_nat_floor_atTop.comp (rationalSizeIndex24_argument_tendsto d hd)

theorem rationalSizeFloor24_le (d N : ℕ) (hd : 0 < d) : rationalSizeFloor24 d N ≤ N := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hx : 0 ≤ ((N:ℝ) ^ (1/24:ℝ))/(d:ℝ) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hdR.le
  have hr : ((d*rationalSizeFloorIndex24 d N:ℕ):ℝ) ≤ (N:ℝ) ^ (1/24:ℝ) := by
    have h := Nat.floor_le hx
    change (rationalSizeFloorIndex24 d N:ℝ) ≤ _ at h
    have hh := (le_div_iff₀ hdR).mp h
    push_cast
    linarith
  have hpow := pow_le_pow_left₀ (by positivity) hr 24
  rw [real_twentyFourth_root_pow] at hpow
  exact_mod_cast hpow

theorem rationalSizeFloor24_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (rationalSizeFloor24 d N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp
    (rationalSizeIndex24_argument_tendsto d hd)).pow 24
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hnz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (((rationalSizeFloorIndex24 d N:ℕ):ℝ)/((N:ℝ)^(1/24:ℝ)/(d:ℝ)))^24 = _
  rw [div_pow, div_pow, real_twentyFourth_root_pow]
  unfold rationalSizeFloor24
  push_cast
  field_simp [hnz, hdz]

/-! ### The density ratio between two sizes -/

/-- The ratio `(N/M)^(1/12)` of the Gaussian density factors of the sizes `N` and `M`. -/
def sphereScaleRatio24 (M N : ℕ) : ℝ := ((N:ℝ)/(M:ℝ))^(1/12:ℝ)

theorem real_twelfth_root_pow {x : ℝ} (hx : 0 ≤ x) : (x^(1/12:ℝ))^12 = x := by
  simpa using Real.rpow_inv_natCast_pow hx (by decide : (12:ℕ) ≠ 0)

theorem sphereScaleRatio24_pos {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    0 < sphereScaleRatio24 M N := by
  unfold sphereScaleRatio24
  exact Real.rpow_pos_of_pos (div_pos (by exact_mod_cast hN) (by exact_mod_cast hM)) _

theorem sphereScaleRatio24_pow (M N : ℕ) : (sphereScaleRatio24 M N)^12 = (N:ℝ)/(M:ℝ) := by
  unfold sphereScaleRatio24
  exact real_twelfth_root_pow (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg M))

theorem sphereScaleRatio24_one_le {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    1 ≤ sphereScaleRatio24 M N := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h : (1:ℝ) ≤ (N:ℝ)/(M:ℝ) := by
    rw [le_div_iff₀ hMR, one_mul]
    exact_mod_cast hMN
  unfold sphereScaleRatio24
  exact Real.one_le_rpow h (by norm_num)

theorem sphereScaleRatio24_le_two {M N : ℕ} (hM : 0 < M) (hN2 : (N:ℝ) ≤ 2*(M:ℝ)) :
    sphereScaleRatio24 M N ≤ 2 := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have h : (N:ℝ)/(M:ℝ) ≤ 2 := by
    rw [div_le_iff₀ hMR]
    exact hN2
  have h0 : 0 ≤ (N:ℝ)/(M:ℝ) := div_nonneg (Nat.cast_nonneg N) hMR.le
  unfold sphereScaleRatio24
  calc ((N:ℝ)/(M:ℝ))^(1/12:ℝ) ≤ (2:ℝ)^(1/12:ℝ) := Real.rpow_le_rpow h0 h (by norm_num)
    _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

/-- The Gaussian scale of the size `N` in terms of the size `M`. -/
theorem sphereGaussianScale24_ratio {M N : ℕ} (hM : 0 < M) (α : ℝ) :
    sphereGaussianScale24 N α = sphereGaussianScale24 M (sphereScaleRatio24 M N*α) := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have harea := sphereAreaD_univ_pos 24
  have h : ((N:ℝ)/(sphereAreaD 24).real univ)^(1/12:ℝ) =
      ((N:ℝ)/(M:ℝ))^(1/12:ℝ)*((M:ℝ)/(sphereAreaD 24).real univ)^(1/12:ℝ) := by
    rw [← Real.mul_rpow (div_nonneg (Nat.cast_nonneg N) hMR.le) (div_nonneg hMR.le harea.le),
      div_mul_div_comm, mul_comm (N:ℝ) (M:ℝ), mul_div_mul_left _ _ hMR.ne']
  unfold sphereGaussianScale24 sphereScaleRatio24
  rw [h]
  ring

theorem sphereGaussianDensityFactor24_ratio {M N : ℕ} (hM : 0 < M) :
    sphereGaussianDensityFactor24 N = sphereScaleRatio24 M N*sphereGaussianDensityFactor24 M := by
  have h := sphereGaussianScale24_ratio (N := N) hM 1
  simp only [sphereGaussianScale24_eq_factor, mul_one] at h
  rw [h]
  ring

/-- The defect of the kept points at the scale of the larger size. -/
theorem sphereGaussianDefect24_kept {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (Y : ConfigurationD 24 M) {α : ℝ} (hα : 0 ≤ α) :
    sphereGaussianDefect24 (sphereGaussianScale24 N α) (M:ℝ) Y =
      (M:ℝ)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1) := by
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [sphereGaussianCenteredScaled24_add_one hM
    (mul_nonneg (sphereScaleRatio24_pos hM hN).le hα) Y, ← sphereGaussianScale24_ratio hM α,
    mul_div_cancel₀ _ hMR]

/-! ### Two densities -/

/-- Cauchy–Schwarz with two densities for a combined configuration: kept points against their
own number, added points against their own number. -/
theorem combinedConfiguration24_massSplit_le {ι : Type*} [Fintype ι] {n N : ℕ}
    (x : ι → SphereD 24) (z : Fin n → SphereD 24) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianDefect24 t (N:ℝ) (combinedConfiguration24 x z hcard hx hz havoid) ≤
      2*gaussianMeasureDefect t (Fintype.card ι:ℝ)
          (finitePointMeasure (fun i => (x i : AmbientD 24))) ambientSphereProbability24+
        2*gaussianMeasureDefect t (n:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 24)))
          ambientSphereProbability24 := by
  rw [sphereGaussianDefect24_eq_diffuse ht, diffuseGaussianDefect_eq_measureDefect ht]
  have hfpm : finitePointMeasure (fun i : Fin N =>
      ((combinedConfiguration24 x z hcard hx hz havoid i : SphereD 24) : AmbientD 24)) =
      finitePointMeasure (fun a : ι ⊕ Fin n => ((Sum.elim x z a : SphereD 24) : AmbientD 24)) := by
    unfold finitePointMeasure
    exact Equiv.sum_comp ((Fintype.equivFinOfCardEq
      (show Fintype.card (ι ⊕ Fin n) = N by
        rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm)
      (fun a => Measure.dirac ((Sum.elim x z a : SphereD 24) : AmbientD 24))
  have hfun : (fun a : ι ⊕ Fin n => ((Sum.elim x z a : SphereD 24) : AmbientD 24)) =
      Sum.elim (fun i => (x i : AmbientD 24)) (fun j => (z j : AmbientD 24)) := by
    funext a
    cases a <;> rfl
  have hNsum : (N:ℝ) = (Fintype.card ι:ℝ)+(n:ℝ) := by exact_mod_cast hcard.symm
  rw [hfpm, hfun, finitePointMeasure_sum_elim, hNsum]
  exact gaussianMeasureDefect_mass_add_le ht _ _ _ _ _

theorem ambientRestricted24_univ : ambientRestricted24 univ = ambientSphereProbability24 := by
  unfold ambientRestricted24 ambientSphereProbability24
  rw [Measure.restrict_univ]

/-- For `r` points against `r σ` on the whole sphere the neutralized Gaussian energy is the
ambient defect. -/
theorem wholeSphere_residualEnergy_eq_defect {r : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (z : Fin r → SphereD 24) :
    residualNeutralizedEnergy (sphereRestrictedProbability24 univ) (sphereGaussianKernel24 t)
        (fun _ => 0) z =
      gaussianMeasureDefect t (r:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 24)))
        ambientSphereProbability24 := by
  have hR : (sphereProbabilityD 24) univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  have hmass : (r:ℝ) = (r:ℝ)*(sphereProbabilityD 24).real univ := by
    rw [probReal_univ, mul_one]
  rw [residualGaussianEnergy24_eq_defect ht z univ hR hmass, ambientRestricted24_univ]

/-- Substitution `β = l α` in a weighted integral over an initial interval. -/
theorem rpow_weighted_comp_mul_integral {p l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w) (f : ℝ → ℝ) :
    (∫ α in Ioc (0:ℝ) w, α^p*f (l*α)) = l^(-(p+1))*∫ β in Ioc (0:ℝ) (l*w), β^p*f β := by
  have hlw : 0 ≤ l*w := mul_nonneg hl.le hw
  rw [← intervalIntegral.integral_of_le hw, ← intervalIntegral.integral_of_le hlw]
  set g : ℝ → ℝ := fun β => β^p*f β with hg
  have hpt : Set.EqOn (fun α : ℝ => α^p*f (l*α)) (fun α => l^(-p)*g (l*α)) (uIcc 0 w) := by
    intro α hα
    rw [uIcc_of_le hw] at hα
    have hα0 : 0 ≤ α := hα.1
    simp only [hg]
    rw [Real.mul_rpow hl.le hα0]
    have hll : l^(-p)*l^p = 1 := by
      rw [← Real.rpow_add hl]
      simp
    calc α^p*f (l*α) = (l^(-p)*l^p)*α^p*f (l*α) := by rw [hll]; ring
      _ = l^(-p)*(l^p*α^p*f (l*α)) := by ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left g hl.ne', mul_zero, smul_eq_mul]
  rw [show (-(p+1)) = -p+(-1) by ring, Real.rpow_add hl, Real.rpow_neg_one]
  ring

/-- The macroscopic end of a configuration obtained by adding points: the kept part is the
macroscopic end of the kept configuration up to the substitution `β = l α`, the added part is the
neutralized energy of the subtracted macroscopic kernel on the whole sphere. -/
theorem addedConfiguration24_macroEnd_le {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {M r N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (Y : ConfigurationD 24 M) (z : Fin r → SphereD 24)
    (hcard : Fintype.card (Fin M)+r = N) (hz : Function.Injective z)
    (havoid : ∀ j, z j ∉ range (⇑Y)) {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α
        (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)+1)) ≤
      2*((sphereScaleRatio24 M N)^(-(s/2-1+1))*
        ∫ β in Ioc (0:ℝ) (sphereScaleRatio24 M N*w),
          β^(s/2-1)*(sphereGaussianCenteredScaled24 β Y+1))+
        2/(N:ℝ)*residualNeutralizedEnergy (sphereRestrictedProbability24 univ)
          (negMacroKernel24 (sphereGaussianDensityFactor24 N) (s/2-1) 1) (fun _ => 0) z := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hMN : (M:ℝ) ≤ N := by
    have h : (Fintype.card (Fin M):ℝ)+(r:ℝ) = N := by exact_mod_cast hcard
    rw [Fintype.card_fin] at h
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hc : 0 < sphereGaussianDensityFactor24 N := sphereGaussianDensityFactor24_pos hN
  have hp : -2 < s/2-1 := by linarith
  have hl : 0 < sphereScaleRatio24 M N := sphereScaleRatio24_pos hM hN
  have hRu : (sphereProbabilityD 24) univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  have : IsProbabilityMeasure (sphereRestrictedProbability24 univ) :=
    sphereRestrictedProbability24_probability _ hRu
  obtain ⟨hNEint, hNEeq⟩ := negMacro_residualNeutralizedEnergy_eq hc.le hp zero_le_one
    (sphereRestrictedProbability24 univ) z
  set E : ℝ → ℝ := fun α => residualNeutralizedEnergy (sphereRestrictedProbability24 univ)
    (sphereGaussianKernel24 (sphereGaussianDensityFactor24 N*α)) (fun _ => 0) z with hE
  have hE0 : ∀ α : ℝ, 0 < α → 0 ≤ E α := by
    intro α hα
    have ht : 0 ≤ sphereGaussianDensityFactor24 N*α := mul_nonneg hc.le hα.le
    simp only [hE]
    rw [wholeSphere_residualEnergy_eq_defect ht z]
    exact gaussianMeasureDefect_nonneg ht _ _ _
  -- the kept part is integrable after the substitution
  have hGint : IntegrableOn
      (fun β : ℝ => β^(s/2-1)*(sphereGaussianCenteredScaled24 β Y+1)) (Ioi 0) :=
    sphereGaussianCenteredScaled24_neg_integrable hs hs0 hM Y
  have hGl : IntegrableOn (fun α : ℝ => (sphereScaleRatio24 M N*α)^(s/2-1)*
      (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun β : ℝ => β^(s/2-1)*(sphereGaussianCenteredScaled24 β Y+1)) 0 hl).mpr
      (by rw [mul_zero]; exact hGint)
  have hKint : IntegrableOn (fun α : ℝ => α^(s/2-1)*
      (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hGl.const_mul ((sphereScaleRatio24 M N)^(-(s/2-1))))
      (fun α hα => ?_) measurableSet_Ioi
    have hα0 : (0:ℝ) < α := hα
    show (sphereScaleRatio24 M N)^(-(s/2-1))*((sphereScaleRatio24 M N*α)^(s/2-1)*
        (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)) =
      α^(s/2-1)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)
    rw [Real.mul_rpow hl.le hα0.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hl,
      neg_add_cancel, Real.rpow_zero, one_mul]
  have hKintw : IntegrableOn (fun α : ℝ => α^(s/2-1)*
      (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)) (Ioc 0 w) :=
    hKint.mono_set Ioc_subset_Ioi_self
  have hpt : ∀ α ∈ Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α
      (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)+1) ≤
      2*(α^(s/2-1)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1))+
        2/(N:ℝ)*(α^(s/2-1)*E α) := by
    intro α hα
    have hα0 : 0 < α := hα.1
    have ht : 0 ≤ sphereGaussianDensityFactor24 N*α := mul_nonneg hc.le hα0.le
    have hwα : 0 ≤ α^(s/2-1) := Real.rpow_nonneg hα0.le _
    have hF := sphereGaussianCenteredScaled24_add_one hN hα0.le
      (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)
    have hD := combinedConfiguration24_massSplit_le (⇑Y) z hcard Y.injective hz havoid ht
    have hY : gaussianMeasureDefect (sphereGaussianDensityFactor24 N*α)
        (Fintype.card (Fin M):ℝ) (finitePointMeasure (fun i => (Y i : AmbientD 24)))
        ambientSphereProbability24 =
        (M:ℝ)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1) := by
      rw [Fintype.card_fin, ← diffuseGaussianDefect_eq_measureDefect ht,
        ← sphereGaussianDefect24_eq_diffuse ht, ← sphereGaussianScale24_eq_factor,
        sphereGaussianDefect24_kept hM hN Y hα0.le]
    have hres := wholeSphere_residualEnergy_eq_defect ht z
    have hK0 : 0 ≤ sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1 :=
      sphereGaussianCenteredScaled24_add_one_nonneg hM (mul_nonneg hl.le hα0.le) Y
    rw [sphereGaussianScale24_eq_factor] at hF
    rw [hY, ← hres] at hD
    have hbound : sphereGaussianCenteredScaled24 α
        (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)+1 ≤
        2*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)+2/(N:ℝ)*E α := by
      rw [hF, div_le_iff₀ hNR]
      have he : (2*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)+
          2/(N:ℝ)*E α)*(N:ℝ) =
          2*((N:ℝ)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1))+2*E α := by
        calc (2*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)+
              2/(N:ℝ)*E α)*(N:ℝ)
            = 2*((N:ℝ)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1))+
              2*E α*((N:ℝ)/(N:ℝ)) := by ring
          _ = _ := by rw [div_self hNR.ne', mul_one]
      rw [he]
      have hMK : (M:ℝ)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1) ≤
          (N:ℝ)*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1) :=
        mul_le_mul_of_nonneg_right hMN hK0
      simp only [hE]
      linarith
    calc α^(s/2-1)*(sphereGaussianCenteredScaled24 α
          (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)+1)
        ≤ α^(s/2-1)*(2*(sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1)+
            2/(N:ℝ)*E α) := mul_le_mul_of_nonneg_left hbound hwα
      _ = _ := by ring
  have hFint : IntegrableOn (fun α : ℝ => α^(s/2-1)*(sphereGaussianCenteredScaled24 α
      (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)+1)) (Ioc 0 w) :=
    (sphereGaussianCenteredScaled24_neg_integrable hs hs0 hN _).mono_set Ioc_subset_Ioi_self
  have hEint1 : IntegrableOn (fun α : ℝ => α^(s/2-1)*E α) (Ioc 0 1) := hNEint
  have hEint : IntegrableOn (fun α : ℝ => α^(s/2-1)*E α) (Ioc 0 w) :=
    hEint1.mono_set (Ioc_subset_Ioc_right hw1)
  have hmono : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*E α) ≤ ∫ α in Ioc (0:ℝ) 1, α^(s/2-1)*E α := by
    apply setIntegral_mono_set hEint1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact mul_nonneg (Real.rpow_nonneg hα.1.le _) (hE0 α hα.1)
    · exact (Ioc_subset_Ioc_right hw1).eventuallyLE
  calc (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α
        (combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid)+1))
      ≤ ∫ α in Ioc (0:ℝ) w, (2*(α^(s/2-1)*
          (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1))+
            2/(N:ℝ)*(α^(s/2-1)*E α)) :=
        setIntegral_mono_on hFint ((hKintw.const_mul 2).add (hEint.const_mul _))
          measurableSet_Ioc hpt
    _ = 2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*
          (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1))+
          2/(N:ℝ)*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*E α) := by
        rw [integral_add (hKintw.const_mul 2) (hEint.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*
          (sphereGaussianCenteredScaled24 (sphereScaleRatio24 M N*α) Y+1))+
          2/(N:ℝ)*(∫ α in Ioc (0:ℝ) 1, α^(s/2-1)*E α) := by
        have h2N : 0 ≤ 2/(N:ℝ) := by positivity
        linarith [mul_le_mul_of_nonneg_left hmono h2N]
    _ = _ := by
        rw [rpow_weighted_comp_mul_integral hl hw
          (fun β => sphereGaussianCenteredScaled24 β Y+1)]
        simp only [hE]
        rw [hNEeq]

/-! ### Adding points to a configuration with a window and a small macroscopic end -/

/-- Exact-mass stratifications of the whole sphere with cells at their own density scale:
`r` cells of probability `1/r` with `Σ_j c_r d_j² ≤ B r`. -/
def SphereCellStratifiable24 (B : ℝ) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ C : Fin r → Set (SphereD 24), ∃ dm : Fin r → ℝ,
    (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
    (⋃ j, C j) = univ ∧
    (∀ j, sphereProbabilityD 24 (C j) = sphereProbabilityD 24 univ/(r:ℝ≥0∞)) ∧
    (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
    ∑ j, sphereGaussianDensityFactor24 r*(dm j)^2 ≤ B*r

/-- Adding `r ≤ N/L¹⁴` points on the whole sphere to a configuration of `M` points keeps its
Gaussian window and its macroscopic end, up to the scale ratio `l = (N/M)^(1/12) ∈ [1,2]` and
fixed factors. -/
theorem exists_added_configuration24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {L : ℕ} (hL : 2 ≤ L)
    {Bst : ℝ} (hBst : 0 ≤ Bst) (hsph : SphereCellStratifiable24 Bst)
    {M r N : ℕ} (hM : 0 < M) (hr : 0 < r) (hMN : M+r = N)
    (hrN : (r:ℝ) ≤ 1/(L:ℝ)^14*(N:ℝ)) (hN2 : (N:ℝ) ≤ 2*(M:ℝ))
    (Y : ConfigurationD 24 M) (Φ Ψ : ℝ → ℝ)
    (hW : ∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α Y ≤ Φ α)
    (hMac : ∀ w : ℝ, 0 < w → w ≤ 1 →
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α Y+1)) ≤ Ψ w) :
    ∃ X : ConfigurationD 24 N,
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/(L:ℝ))*Φ (sphereScaleRatio24 M N*α)+
          (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1/2 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
          4*Ψ (sphereScaleRatio24 M N*w)+2*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) := by
  have hp : -2 < s/2-1 := by linarith
  have hp2 : 0 < s/2+1 := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hNpos : 0 < N := by omega
  have hMleN : M ≤ N := by omega
  have hrleN : r ≤ N := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hrNR : (r:ℝ) ≤ N := by exact_mod_cast hrleN
  have hcN : 0 < sphereGaussianDensityFactor24 N := sphereGaussianDensityFactor24_pos hNpos
  have hl1 : 1 ≤ sphereScaleRatio24 M N := sphereScaleRatio24_one_le hM hMleN
  have hl2 : sphereScaleRatio24 M N ≤ 2 := sphereScaleRatio24_le_two hM hN2
  have hl0 : 0 < sphereScaleRatio24 M N := by linarith
  have ht₀ : 0 ≤ sphereGaussianScale24 N (1/(L:ℝ)) := (sphereGaussianScale24_pos hNpos hη).le
  -- the cells of the whole sphere at the scale of the added points
  obtain ⟨C, dm, hCm, hCd, hCu, hCmassA, hdiam, hsum⟩ := hsph r hr
  have hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (r:ℝ≥0∞)⁻¹ := by
    intro i
    rw [hCmassA i, measure_univ, one_div]
  -- one joint choice
  obtain ⟨z, hz, _, havoid, hNE0, hjoint⟩ := exists_leech_neg_joint_residual24 hr hr hcN.le hp
    ht₀ (zero_le_one : (0:ℝ) ≤ 1) (⇑Y) C hCm hCd hCmass dm hdiam
  rw [show s/2-1+2 = s/2+1 by ring, hCu] at hjoint
  rw [hCu] at hNE0
  -- the cell costs at the density of `N`
  have hy0 : 0 < sphereScaleRatio24 r N := sphereScaleRatio24_pos hr hNpos
  have hy12 : (sphereScaleRatio24 r N)^12 = (N:ℝ)/(r:ℝ) := sphereScaleRatio24_pow r N
  have hL14 : (L:ℝ)^14 = (L:ℝ)^2*(L:ℝ)^12 := by ring
  have hL12 : (0:ℝ) < (L:ℝ)^12 := pow_pos hL0 12
  have hxL : (L:ℝ)^14 ≤ (N:ℝ)/(r:ℝ) := by
    rw [le_div_iff₀ hrR]
    have h := mul_le_mul_of_nonneg_left hrN (pow_pos hL0 14).le
    have e : (L:ℝ)^14*(1/(L:ℝ)^14*(N:ℝ)) = N := by
      rw [← mul_assoc, mul_one_div_cancel (pow_pos hL0 14).ne', one_mul]
    rw [e] at h
    linarith
  have hyL : (L:ℝ) ≤ sphereScaleRatio24 r N := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (12:ℕ) ≠ 0) hy0.le
    rw [hy12]
    calc (L:ℝ)^12 = 1*(L:ℝ)^12 := (one_mul _).symm
      _ ≤ (L:ℝ)^2*(L:ℝ)^12 := mul_le_mul_of_nonneg_right (one_le_pow₀ hL1) hL12.le
      _ = (L:ℝ)^14 := hL14.symm
      _ ≤ (N:ℝ)/(r:ℝ) := hxL
  have hyL2 : sphereScaleRatio24 r N*(L:ℝ)^2 ≤ (N:ℝ)/(r:ℝ) := by
    have h11 : (L:ℝ)^2 ≤ (sphereScaleRatio24 r N)^11 :=
      (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 11)).trans (pow_le_pow_left₀ hL0.le hyL 11)
    calc sphereScaleRatio24 r N*(L:ℝ)^2
        ≤ sphereScaleRatio24 r N*(sphereScaleRatio24 r N)^11 :=
          mul_le_mul_of_nonneg_left h11 hy0.le
      _ = (sphereScaleRatio24 r N)^12 := by ring
      _ = (N:ℝ)/(r:ℝ) := hy12
  have hyr : sphereScaleRatio24 r N*(r:ℝ) ≤ 1/(L:ℝ)^2*(N:ℝ) := by
    rw [show 1/(L:ℝ)^2*(N:ℝ) = (N:ℝ)/(L:ℝ)^2 by ring, le_div_iff₀ (pow_pos hL0 2)]
    calc sphereScaleRatio24 r N*(r:ℝ)*(L:ℝ)^2 = (sphereScaleRatio24 r N*(L:ℝ)^2)*(r:ℝ) := by ring
      _ ≤ ((N:ℝ)/(r:ℝ))*(r:ℝ) := mul_le_mul_of_nonneg_right hyL2 hrR.le
      _ = N := div_mul_cancel₀ _ hrR.ne'
  have hsumN : sphereGaussianDensityFactor24 N*∑ j, (dm j)^2 ≤ Bst*(1/(L:ℝ)^2*(N:ℝ)) := by
    have h1 : sphereGaussianDensityFactor24 N*∑ j, (dm j)^2 =
        sphereScaleRatio24 r N*∑ j, sphereGaussianDensityFactor24 r*(dm j)^2 := by
      rw [sphereGaussianDensityFactor24_ratio (N := N) hr, ← Finset.mul_sum]
      ring
    rw [h1]
    calc sphereScaleRatio24 r N*∑ j, sphereGaussianDensityFactor24 r*(dm j)^2
        ≤ sphereScaleRatio24 r N*(Bst*(r:ℝ)) := mul_le_mul_of_nonneg_left hsum hy0.le
      _ = Bst*(sphereScaleRatio24 r N*(r:ℝ)) := by ring
      _ ≤ Bst*(1/(L:ℝ)^2*(N:ℝ)) := mul_le_mul_of_nonneg_left hyr hBst
  have hcost : sphereGaussianDensityFactor24 N/(s/2+1)*∑ j, (dm j)^2 ≤
      (Bst*(1/(L:ℝ)^2*(N:ℝ)))/(s/2+1) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hsumN hp2.le
  -- the background of the residual window
  have hBcap : (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N (1/(L:ℝ))) ≤
      (L:ℝ)^12 := by
    have h := sphereGaussianBackground24_scaled_cap hNpos hη
    have e : ((1/(L:ℝ))^12)⁻¹ = (L:ℝ)^12 := by rw [one_div, inv_pow, inv_inv]
    rw [e] at h
    exact h
  have hB0 := sphereGaussianBackground24_nonneg (sphereGaussianScale24 N (1/(L:ℝ)))
  have hNB0 : 0 ≤ (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N (1/(L:ℝ))) :=
    mul_nonneg hNR.le hB0
  have hc12 : 1/(L:ℝ)^14*(L:ℝ)^12 = 1/(L:ℝ)^2 := by
    rw [hL14, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hL12.ne', mul_one]
  have hrB : (r:ℝ)*((r:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N (1/(L:ℝ)))) ≤
      1/(L:ℝ)^2*(N:ℝ) := by
    calc (r:ℝ)*((r:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N (1/(L:ℝ))))
        ≤ (r:ℝ)*((N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N (1/(L:ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrNR hB0) hrR.le
      _ ≤ (1/(L:ℝ)^14*(N:ℝ))*(L:ℝ)^12 :=
          mul_le_mul hrN hBcap hNB0 (mul_nonneg (one_div_nonneg.mpr (pow_pos hL0 14).le) hNR.le)
      _ = (1/(L:ℝ)^14*(L:ℝ)^12)*(N:ℝ) := by ring
      _ = 1/(L:ℝ)^2*(N:ℝ) := by rw [hc12]
  have hLpow : 1/(L:ℝ)^14 ≤ 1/(L:ℝ)^2 :=
    one_div_le_one_div_of_le (pow_pos hL0 2) (pow_le_pow_right₀ hL1 (by norm_num))
  have hr2 : (r:ℝ) ≤ 1/(L:ℝ)^2*(N:ℝ) :=
    hrN.trans (mul_le_mul_of_nonneg_right hLpow hNR.le)
  have hLN0 : 0 ≤ 1/(L:ℝ)^2*(N:ℝ) := mul_nonneg (one_div_nonneg.mpr (pow_pos hL0 2).le) hNR.le
  have hRbound : (r:ℝ)+(Bst*(1/(L:ℝ)^2*(N:ℝ)))/(s/2+1)+
      (r:ℝ)*((r:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N (1/(L:ℝ)))) ≤
      (N:ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
    have h1 : (Bst*(1/(L:ℝ)^2*(N:ℝ)))/(s/2+1) ≤ ((Bst+1)*(1/(L:ℝ)^2*(N:ℝ)))/(s/2+1) := by
      refine div_le_div_of_nonneg_right ?_ hp2.le
      linarith
    have e : (N:ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) =
        1/(L:ℝ)^2*(N:ℝ)+((Bst+1)*(1/(L:ℝ)^2*(N:ℝ)))/(s/2+1)+1/(L:ℝ)^2*(N:ℝ) := by
      unfold leechNegBlockConst24
      ring
    rw [e]
    linarith
  have hcell0 : 0 ≤ cellPairSum (sphereGaussianKernel24
      (sphereGaussianScale24 N (1/(L:ℝ)))) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel24_nonneg _ _ _
  have hcellN : cellPairSum (sphereGaussianKernel24 (sphereGaussianScale24 N (1/(L:ℝ)))) z ≤
      (N:ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by linarith
  have hNE : residualNeutralizedEnergy (sphereRestrictedProbability24 univ)
      (negMacroKernel24 (sphereGaussianDensityFactor24 N) (s/2-1) 1) (fun _ => 0) z ≤
      (N:ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by linarith
  have hcard : Fintype.card (Fin M)+r = N := by
    rw [Fintype.card_fin]
    exact hMN
  refine ⟨combinedConfiguration24 (⇑Y) z hcard Y.injective hz havoid, ?_, ?_⟩
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration24_fullScaled_le hNpos (⇑Y) z hcard Y.injective hz havoid
      hη.le hα hη
    rw [one_div_one_div] at hfull
    have hS0 : 0 ≤ ∑ a, ∑ b, sphereGaussianKernel24 (sphereGaussianScale24 N α) (Y a) (Y b) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
        sphereGaussianKernel24_nonneg _ _ _
    have hkept : (∑ a, ∑ b, sphereGaussianKernel24 (sphereGaussianScale24 N α) (Y a) (Y b))/
        (N:ℝ) ≤ sphereGaussianFullScaled24 (sphereScaleRatio24 M N*α) Y := by
      unfold sphereGaussianFullScaled24
      rw [← sphereGaussianScale24_ratio hM α]
      exact div_le_div_of_nonneg_left hS0 hMR (by exact_mod_cast hMleN)
    have hlα : 1/(L:ℝ) ≤ sphereScaleRatio24 M N*α := by
      calc 1/(L:ℝ) ≤ α := hα
        _ = 1*α := (one_mul α).symm
        _ ≤ sphereScaleRatio24 M N*α := mul_le_mul_of_nonneg_right hl1 hαpos.le
    have hΦ := hW _ hlα
    have hres : cellPairSum (sphereGaussianKernel24
        (sphereGaussianScale24 N (1/(L:ℝ)))) z/(N:ℝ) ≤ leechNegBlockConst24 s Bst/(L:ℝ)^2 := by
      rw [div_le_iff₀ hNR]
      linarith
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hkept.trans hΦ) (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))
  · -- the macroscopic end
    intro w hw hw2
    have hw1 : w ≤ 1 := by linarith
    have hmain := addedConfiguration24_macroEnd_le hs hs0 hM hNpos Y z hcard hz havoid hw.le hw1
    have hlw0 : 0 < sphereScaleRatio24 M N*w := mul_pos hl0 hw
    have hlw1 : sphereScaleRatio24 M N*w ≤ 1 := by
      calc sphereScaleRatio24 M N*w ≤ 2*(1/2) := mul_le_mul hl2 hw2 hw.le (by norm_num)
        _ = 1 := by norm_num
    have hΨ := hMac _ hlw0 hlw1
    have hI0 : 0 ≤ ∫ β in Ioc (0:ℝ) (sphereScaleRatio24 M N*w),
        β^(s/2-1)*(sphereGaussianCenteredScaled24 β Y+1) :=
      setIntegral_nonneg measurableSet_Ioc fun β hβ => mul_nonneg (Real.rpow_nonneg hβ.1.le _)
        (sphereGaussianCenteredScaled24_add_one_nonneg hM hβ.1.le Y)
    have hle : (sphereScaleRatio24 M N)^(-(s/2-1+1)) ≤ 2 := by
      calc (sphereScaleRatio24 M N)^(-(s/2-1+1)) ≤ (sphereScaleRatio24 M N)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hl1 (by linarith)
        _ = sphereScaleRatio24 M N := Real.rpow_one _
        _ ≤ 2 := hl2
    have h1 : (sphereScaleRatio24 M N)^(-(s/2-1+1))*
        (∫ β in Ioc (0:ℝ) (sphereScaleRatio24 M N*w),
          β^(s/2-1)*(sphereGaussianCenteredScaled24 β Y+1)) ≤
        2*Ψ (sphereScaleRatio24 M N*w) := by
      calc _ ≤ 2*(∫ β in Ioc (0:ℝ) (sphereScaleRatio24 M N*w),
            β^(s/2-1)*(sphereGaussianCenteredScaled24 β Y+1)) :=
            mul_le_mul_of_nonneg_right hle hI0
        _ ≤ 2*Ψ (sphereScaleRatio24 M N*w) := by linarith
    have h2N : 2/(N:ℝ)*residualNeutralizedEnergy (sphereRestrictedProbability24 univ)
        (negMacroKernel24 (sphereGaussianDensityFactor24 N) (s/2-1) 1) (fun _ => 0) z ≤
        2*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hNE (by positivity : (0:ℝ) ≤ 2/(N:ℝ))
      have e : 2/(N:ℝ)*((N:ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) =
          2*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
      rw [e] at h
      exact h
    linarith

/-! ### Every large size -/

/-- For every tolerance index, every large size carries a configuration with the window and the
macroscopic end of a block, up to fixed factors. -/
theorem exists_leech_neg_allN_block24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {Bst : ℝ}
    (hBst : 0 ≤ Bst) (hstrat : LeechResidualStratifiable24 Bst)
    (hsph : SphereCellStratifiable24 Bst) {L : ℕ} (hL : 2 ≤ L) :
    ∀ᶠ N : ℕ in atTop, ∃ X : ConfigurationD 24 (N+1),
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/(L:ℝ))*((1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2))+
          (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1/2 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
          4*(2*(leechMacroConstA24*((2*w)^(s/2+2)/(s/2+2))+
            1/(L:ℝ)*((2*w)^(s/2+1)/(s/2+1)))+2*(leechNegBlockConst24 s Bst/(L:ℝ)^2))+
            2*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) := by
  have hp2 : 0 < s/2+1 := by linarith
  have hp3 : 0 < s/2+2 := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hLR
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hA := leechMacroConstA24_nonneg
  obtain ⟨d, hd, hev⟩ := exists_leech_neg_block24 hs hs0 hBst hstrat hL
  have hidx := rationalSizeFloorIndex24_tendsto d hd
  have h1 := hidx.eventually hev
  have h2 := hidx.eventually (eventually_ge_atTop 1)
  -- the missing fraction tends to zero
  have hprod : Tendsto (fun N : ℕ => (rationalSizeFloor24 d N:ℝ)/(N:ℝ)*((N:ℝ)/((N:ℝ)+1)))
      atTop (𝓝 (1*1)) :=
    (rationalSizeFloor24_ratio_tendsto d hd).mul (tendsto_natCast_div_add_atTop (1:ℝ))
  rw [one_mul] at hprod
  have hL14 : (0:ℝ) < (L:ℝ)^14 := pow_pos hL0 14
  have hL14' : 1/(L:ℝ)^14 ≤ 1/2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    calc (2:ℝ) ≤ L := hLR
      _ = (L:ℝ)^1 := (pow_one _).symm
      _ ≤ (L:ℝ)^14 := pow_le_pow_right₀ hL1 (by norm_num)
  have hgap : 1-1/(L:ℝ)^14 < 1 := by
    have h : 0 < 1/(L:ℝ)^14 := one_div_pos.mpr hL14
    linarith
  have e1 := (tendsto_order.mp hprod).1 _ hgap
  filter_upwards [h1, h2, e1, eventually_gt_atTop 0] with N hN1 hN2 hN3 hN0
  obtain ⟨Y, hYW, hYM⟩ := hN1
  have hmpos : 0 < rationalSizeFloorIndex24 d N := hN2
  have hMpos : 0 < (d*rationalSizeFloorIndex24 d N)^24 := pow_pos (Nat.mul_pos hd hmpos) 24
  have hMle : (d*rationalSizeFloorIndex24 d N)^24 ≤ N := rationalSizeFloor24_le d N hd
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (d*rationalSizeFloorIndex24 d N)^24+r = N+1 :=
    ⟨N+1-(d*rationalSizeFloorIndex24 d N)^24, Nat.add_sub_of_le (hMle.trans (Nat.le_succ N))⟩
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, add_zero] at hr
      rw [hr] at hMle
      exact absurd hMle (Nat.not_succ_le_self N)
    · exact h0
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hN1R : (0:ℝ) < (N:ℝ)+1 := by linarith
  have hMR : (0:ℝ) < (((d*rationalSizeFloorIndex24 d N)^24:ℕ):ℝ) := by exact_mod_cast hMpos
  have hsumR : (((d*rationalSizeFloorIndex24 d N)^24:ℕ):ℝ)+(r:ℝ) = (N:ℝ)+1 := by
    exact_mod_cast hr
  -- `M > (1-1/L¹⁴)(N+1)`
  have hfrac : (1-1/(L:ℝ)^14)*((N:ℝ)+1) < (((d*rationalSizeFloorIndex24 d N)^24:ℕ):ℝ) := by
    have h : (rationalSizeFloor24 d N:ℝ)/(N:ℝ)*((N:ℝ)/((N:ℝ)+1)) =
        (((d*rationalSizeFloorIndex24 d N)^24:ℕ):ℝ)/((N:ℝ)+1) := by
      unfold rationalSizeFloor24
      rw [div_mul_div_comm, mul_comm (N:ℝ) ((N:ℝ)+1), mul_div_mul_right _ _ hNR.ne']
    rw [h, lt_div_iff₀ hN1R] at hN3
    exact hN3
  have hcast : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
  have hrN : (r:ℝ) ≤ 1/(L:ℝ)^14*((N+1:ℕ):ℝ) := by
    rw [hcast]
    linarith
  have hN2' : ((N+1:ℕ):ℝ) ≤ 2*(((d*rationalSizeFloorIndex24 d N)^24:ℕ):ℝ) := by
    rw [hcast]
    have h : (1/2)*((N:ℝ)+1) ≤ (1-1/(L:ℝ)^14)*((N:ℝ)+1) :=
      mul_le_mul_of_nonneg_right (by linarith) hN1R.le
    linarith
  obtain ⟨X, hXW, hXM⟩ := exists_added_configuration24 hs hs0 hL hBst hsph hMpos hrpos hr hrN
    hN2' Y
    (fun α => (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
      (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2))
    (fun w => 2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
      2*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) hYW hYM
  have hl1 : 1 ≤ sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1) :=
    sphereScaleRatio24_one_le hMpos (by omega)
  have hl2 : sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1) ≤ 2 :=
    sphereScaleRatio24_le_two hMpos hN2'
  refine ⟨X, ?_, ?_⟩
  · intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hθ : leechGaussianThetaReal24
        (sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*α*(1-1/(L:ℝ))^2) ≤
        leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2) := by
      have hlα : α ≤ sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*α := by
        calc α = 1*α := (one_mul α).symm
          _ ≤ sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*α :=
            mul_le_mul_of_nonneg_right hl1 hαpos.le
      exact leechGaussianThetaReal24_anti (mul_pos hαpos (pow_pos hη0 2))
        (mul_le_mul_of_nonneg_right hlα (pow_pos hη0 2).le)
    have h : sphereGaussianFullScaled24 α X ≤
        (1+1/(L:ℝ))*((1+1/(L:ℝ))*(leechGaussianThetaReal24
          (sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*α*(1-1/(L:ℝ))^2)+
            2/(L:ℝ))+(1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2))+
          (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := hXW α hα
    have hmono : (1+1/(L:ℝ))*((1+1/(L:ℝ))*(leechGaussianThetaReal24
        (sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*α*(1-1/(L:ℝ))^2)+
          2/(L:ℝ))+(1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) ≤
        (1+1/(L:ℝ))*((1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) := by
      have h0 : 0 ≤ 1+1/(L:ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left
        (by linarith [mul_le_mul_of_nonneg_left hθ h0]) h0
    linarith
  · intro w hw hw2
    have h : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
        4*(2*(leechMacroConstA24*
          ((sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*w)^(s/2+2)/(s/2+2))+
          1/(L:ℝ)*
          ((sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*w)^(s/2+1)/(s/2+1)))+
          2*(leechNegBlockConst24 s Bst/(L:ℝ)^2))+2*(leechNegBlockConst24 s Bst/(L:ℝ)^2) :=
      hXM w hw hw2
    have hlw0 : 0 ≤ sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*w :=
      mul_nonneg (by linarith) hw.le
    have hlw : sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*w ≤ 2*w :=
      mul_le_mul_of_nonneg_right hl2 hw.le
    have h3 : (sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*w)^(s/2+2)/
        (s/2+2) ≤ (2*w)^(s/2+2)/(s/2+2) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hlw0 hlw hp3.le) hp3.le
    have h2 : (sphereScaleRatio24 ((d*rationalSizeFloorIndex24 d N)^24) (N+1)*w)^(s/2+1)/
        (s/2+1) ≤ (2*w)^(s/2+1)/(s/2+1) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hlw0 hlw hp2.le) hp2.le
    have hA3 := mul_le_mul_of_nonneg_left h3 hA
    have hL2 := mul_le_mul_of_nonneg_left h2 hη.le
    linarith

/-- Configurations of every large size whose normalized negative-exponent energy is at least
`C_s - η`, given the two stratifications. -/
theorem sphere24_riesz_neg_lower_allN_of_stratifiable {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : LeechResidualStratifiable24 Bst)
    (hsph : SphereCellStratifiable24 Bst) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ConfigurationD 24 N,
      sphereRieszCoefficientNeg24 s-η ≤ normalizedEnergyNeg24 s X := by
  have hp2 : 0 < s/2+1 := by linarith
  have hp3 : 0 < s/2+2 := by linarith
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop, ∃ X : ConfigurationD 24 (N+1),
      (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/((j+2:ℕ):ℝ))*((1+1/((j+2:ℕ):ℝ))*
          (leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
          (1+((j+2:ℕ):ℝ))*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2))+
          (1+((j+2:ℕ):ℝ))*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1/2 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
          4*(2*(leechMacroConstA24*((2*w)^(s/2+2)/(s/2+2))+
            1/((j+2:ℕ):ℝ)*((2*w)^(s/2+1)/(s/2+1)))+
            2*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2))+
            2*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) :=
    fun j => exists_leech_neg_allN_block24 hs hs0 hBst hstrat hsph (L := j+2) (by omega)
  obtain ⟨J, hJt, hJ⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hJ
  have hQ := fun k : ℕ => hN₁ (N₁+k) (Nat.le_add_right N₁ k)
  choose Z hZW hZM using hQ
  have hNt : Tendsto (fun k : ℕ => N₁+k+1) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_add_left k N₁).trans (Nat.le_succ _)) tendsto_id
  have hNpos : ∀ k : ℕ, 0 < N₁+k+1 := fun k => Nat.succ_pos _
  have hidx : Tendsto (fun k : ℕ => N₁+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₁) tendsto_id
  have hLt : Tendsto (fun k : ℕ => J (N₁+k)+2) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (J (N₁+k)) 2) (hJt.comp hidx)
  have hLR : Tendsto (fun k : ℕ => ((J (N₁+k)+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hLt
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hu : Tendsto (fun k : ℕ => 1/((J (N₁+k)+2:ℕ):ℝ)) atTop (𝓝 0) := hone.div_atTop hLR
  have hCc : Tendsto (fun _ : ℕ => leechNegBlockConst24 s Bst) atTop
      (𝓝 (leechNegBlockConst24 s Bst)) := tendsto_const_nhds
  have hsq : Tendsto (fun k : ℕ => leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)^2) atTop
      (𝓝 0) := hCc.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hLR)
  have hlin : Tendsto (fun k : ℕ => leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)) atTop
      (𝓝 0) := hCc.div_atTop hLR
  have htail : Tendsto (fun k : ℕ => (1+((J (N₁+k)+2:ℕ):ℝ))*
      (leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)^2)) atTop (𝓝 0) := by
    have h := hsq.add hlin
    rw [add_zero] at h
    refine h.congr fun k => ?_
    show leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)^2+
        leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ) =
      (1+((J (N₁+k)+2:ℕ):ℝ))*(leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)^2)
    have hLne : ((J (N₁+k)+2:ℕ):ℝ) ≠ 0 := by positivity
    have h1 : ((J (N₁+k)+2:ℕ):ℝ)*(leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)^2) =
        leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ) := by
      rw [← mul_div_assoc, sq, mul_div_mul_left _ _ hLne]
    rw [add_mul, one_mul, h1]
  -- the pointwise window
  have hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (Z k) ≤ leechGaussianThetaReal24 α+ε := by
    intro α hα ε hε
    have hΦ := leechBlockWindowBound_tendsto (B := leechNegBlockConst24 s Bst) hα hLt
    have hall := ((hone.add hu).mul hΦ).add htail
    have hlim : (1+0)*leechGaussianThetaReal24 α+0 = leechGaussianThetaReal24 α := by ring
    rw [hlim] at hall
    have e1 := (tendsto_order.mp hall).2 (leechGaussianThetaReal24 α+ε) (by linarith)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with k hk1 hk2
    exact (hZW k α hk2.le).trans hk1.le
  -- the macroscopic end
  have hmacro : ∀ η : ℝ, 0 < η → ∃ w : ℝ, 0 < w ∧ ∀ᶠ k in atTop,
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α (Z k)+1)) ≤ η := by
    intro η hη
    have hA := leechMacroConstA24_nonneg
    have hden : 0 < 32*(leechMacroConstA24+1) := by linarith
    have hw0 : 0 < η*(s/2+2)/(32*(leechMacroConstA24+1)) := div_pos (mul_pos hη hp3) hden
    refine ⟨min (1/2) (η*(s/2+2)/(32*(leechMacroConstA24+1))),
      lt_min (by norm_num) hw0, ?_⟩
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = min (1/2) (η*(s/2+2)/(32*(leechMacroConstA24+1))) :=
      ⟨_, rfl⟩
    rw [← hwdef]
    have hw : 0 < w := by rw [hwdef]; exact lt_min (by norm_num) hw0
    have hw2 : w ≤ 1/2 := by rw [hwdef]; exact min_le_left _ _
    have hw3 : w ≤ η*(s/2+2)/(32*(leechMacroConstA24+1)) := by
      rw [hwdef]; exact min_le_right _ _
    have h2w0 : 0 < 2*w := by linarith
    have h2w1 : 2*w ≤ 1 := by linarith
    have hpow3 : (2*w)^(s/2+2) ≤ 2*w := by
      have h := Real.rpow_le_rpow_of_exponent_ge h2w0 h2w1 (by linarith : (1:ℝ) ≤ s/2+2)
      rwa [Real.rpow_one] at h
    have hpow2 : (2*w)^(s/2+1) ≤ 1 := Real.rpow_le_one h2w0.le h2w1 hp2.le
    have hfirst : 4*(2*(leechMacroConstA24*((2*w)^(s/2+2)/(s/2+2)))) ≤ η/2 := by
      have h1 : (2*w)^(s/2+2)/(s/2+2) ≤ 2*(η/(32*(leechMacroConstA24+1))) := by
        rw [div_le_iff₀ hp3]
        calc (2*w)^(s/2+2) ≤ 2*w := hpow3
          _ ≤ 2*(η*(s/2+2)/(32*(leechMacroConstA24+1))) := by linarith
          _ = 2*(η/(32*(leechMacroConstA24+1)))*(s/2+2) := by ring
      have h2 : leechMacroConstA24*((2*w)^(s/2+2)/(s/2+2)) ≤
          leechMacroConstA24*(2*(η/(32*(leechMacroConstA24+1)))) :=
        mul_le_mul_of_nonneg_left h1 hA
      have h3 : leechMacroConstA24*(2*(η/(32*(leechMacroConstA24+1)))) ≤ η/16 := by
        rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 16)]
        linarith
      linarith
    have hφ : Tendsto (fun k : ℕ => 8*(1/((J (N₁+k)+2:ℕ):ℝ)*(1/(s/2+1)))+
        10*(leechNegBlockConst24 s Bst/((J (N₁+k)+2:ℕ):ℝ)^2)) atTop
        (𝓝 (8*(0*(1/(s/2+1)))+10*0)) :=
      ((hu.mul_const _).const_mul 8).add (hsq.const_mul 10)
    have hφ0 : (8*(0*(1/(s/2+1)))+10*0 : ℝ) = 0 := by ring
    rw [hφ0] at hφ
    have e := (tendsto_order.mp hφ).2 (η/2) (half_pos hη)
    filter_upwards [e] with k hk
    have hMk := hZM k w hw hw2
    have hsec : 1/((J (N₁+k)+2:ℕ):ℝ)*((2*w)^(s/2+1)/(s/2+1)) ≤
        1/((J (N₁+k)+2:ℕ):ℝ)*(1/(s/2+1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow2 hp2.le)
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    linarith
  intro η hη
  have hfin := sphere24_riesz_neg_lower_of_full_profile hs hs0 hNt hNpos Z hp hmacro η hη
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hfin
  refine ⟨N₁+k₀+1, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = N₁+k+1 := ⟨N-N₁-1, by omega⟩
  exact ⟨Z k, hk₀ k (by omega)⟩

end SphericalRiesz
end
end

section

/-! The sharp asymptotics for negative exponents `-2 < s < 0` on S²⁴ (stage NEG, statements).

For `-2 < s < 0` the energy of a configuration is `E_s(X) = Σ_{i≠j} |x_i-x_j|^|s|`, the
continuous constant `I_s` is the double integral of `|x-y|^|s|` over the sphere, and
`C_s = A₂₄^(-s/24) Re ζ_Λ(s)` is the continued Leech Epstein value.

* Lower half, without hypotheses: for every `η > 0` and every large `N` there is a configuration
  with `(E_s - I_s N²)/N^(1+s/24) ≥ C_s - η`.  The configurations are fourteenth-order Leech
  patch nodes, stratified residual points and stratified added points; both stratifications are
  proved in `Riesz.SphereStratification24`.
* Upper half, for all configurations, under all-scale Leech contact certificates (stage G24,
  not proved in this project): `(E_s - I_s N²)/N^(1+s/24) ≤ C_s + η`.

Together they give the conjectured second-order term of the maximal sum of `|x_i-x_j|^|s|`
on S²⁴, with G24 as the only hypothesis. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The negative-exponent continuous constant is the actual double integral of `|x-y|^|s|`. -/
theorem sphereRieszConstNeg24_eq_pair_integral {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    sphereRieszConstNeg24 s =
      ∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
        ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  set μ := (sphereProbabilityD 24).prod (sphereProbabilityD 24) with hμ
  set ν := volume.restrict (Ioi (0:ℝ)) with hν
  set f : SphereD 24 × SphereD 24 → ℝ → ℝ :=
    fun p t => t^(s/2-1)*(sphereGaussianKernel24 t p.1 p.2-1) with hf
  have hdom1 : IntegrableOn (fun t : ℝ => 4*(t^(s/2-1)*min t 1)) (Ioi 0) := by
    apply integrableOn_Ioi_of_rpow_min_bound (C := 4) (a := s/2) (by linarith) (by linarith)
    · intro t ht
      have ht0 : (0:ℝ) < t := ht
      exact (continuousAt_const.mul ((Real.continuousAt_rpow_const t (s/2-1)
        (Or.inl ht0.ne')).mul (continuous_id.min continuous_const).continuousAt)).continuousWithinAt
    · intro t ht
      have h0 : 0 ≤ 4*(t^(s/2-1)*min t 1) :=
        mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ht.le _)
          (le_min ht.le zero_le_one))
      rw [abs_of_nonneg h0]
  have hdom : Integrable (fun z : (SphereD 24 × SphereD 24) × ℝ =>
      (1:ℝ)*(4*(z.2^(s/2-1)*min z.2 1))) (μ.prod ν) :=
    Integrable.mul_prod (integrable_const (1:ℝ)) hdom1
  have hmeas : Measurable (Function.uncurry f) := by
    have h1 : Measurable (fun z : (SphereD 24 × SphereD 24) × ℝ => z.2^(s/2-1)) :=
      measurable_snd.pow_const _
    have h2 : Continuous (fun z : (SphereD 24 × SphereD 24) × ℝ =>
        Real.exp (-(z.2*(dist z.1.1 z.1.2)^2))-1) := by fun_prop
    exact h1.mul h2.measurable
  have hpos : ∀ᵐ z ∂(μ.prod ν), z.2 ∈ Ioi (0:ℝ) :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd)
      (ae_restrict_mem measurableSet_Ioi)
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hpos] with z hz
    have ht0 : (0:ℝ) < z.2 := hz
    have hd := sphere24_dist_le_two z.1.1 z.1.2
    have hd0 : 0 ≤ dist z.1.1 z.1.2 := dist_nonneg
    obtain ⟨hb1, hb2⟩ := one_sub_exp_neg_bounds
      (mul_nonneg ht0.le (sq_nonneg (dist z.1.1 z.1.2)))
    have hw : 0 ≤ z.2^(s/2-1) := Real.rpow_nonneg ht0.le _
    have hd2 : (dist z.1.1 z.1.2)^2 ≤ 4 := by nlinarith
    have hm : min (z.2*(dist z.1.1 z.1.2)^2) 1 ≤ 4*min z.2 1 := by
      rcases le_total z.2 1 with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hd2 ht0.le])
      · rw [min_eq_right h]
        linarith [min_le_right (z.2*(dist z.1.1 z.1.2)^2) 1]
    change ‖z.2^(s/2-1)*(Real.exp (-(z.2*(dist z.1.1 z.1.2)^2))-1)‖ ≤
      1*(4*(z.2^(s/2-1)*min z.2 1))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub,
      one_mul]
    calc z.2^(s/2-1)*(1-Real.exp (-(z.2*(dist z.1.1 z.1.2)^2)))
        ≤ z.2^(s/2-1)*(4*min z.2 1) := mul_le_mul_of_nonneg_left (hb2.trans hm) hw
      _ = 4*(z.2^(s/2-1)*min z.2 1) := by ring
  have hswap := integral_integral_swap hint
  have hleft : (∫ p, (∫ t, f p t ∂ν) ∂μ) =
      Real.Gamma (s/2)*∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    exact (sphereGaussianPair24_mellin_neg hs hs0 p.1 p.2).2
  have hright : (∫ t, (∫ p, f p t ∂μ) ∂ν) =
      ∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianBackground24 t-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    simp only [hf]
    rw [integral_const_mul, integral_sub (sphereGaussianKernel24_pair_integrable ht0)
      (integrable_const (1:ℝ))]
    simp [sphereGaussianBackground24]
  rw [hleft, hright] at hswap
  unfold sphereRieszConstNeg24
  rw [← hswap]
  field_simp

/-- The residual regions of Leech patch families are stratifiable at the density scale. -/
theorem leechResidualStratifiable24_of_neg {B : ℝ}
    (h : ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      NegStratifiable24 (⋃ i, smallLeechSpherePatch24 (P i))ᶜ B) :
    LeechResidualStratifiable24 B := by
  intro K P ε hε
  exact h P ε hε

/-- The whole-sphere stratification in the form used for the added points. -/
theorem sphereCellStratifiable24_of_stratifiable {B : ℝ} (h : SphereStratifiable24 B) :
    SphereCellStratifiable24 B := by
  intro r hr
  exact h r hr

/-- Configurations of every large size whose normalized negative-exponent energy is at least
`C_s - η`.  No hypothesis is used. -/
theorem sphere24_riesz_neg_lower_allN {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ConfigurationD 24 N,
      sphereRieszCoefficientNeg24 s-η ≤ normalizedEnergyNeg24 s X := by
  obtain ⟨B, hB, hneg, hsph⟩ := sphere24_stratification_hypotheses
  exact sphere24_riesz_neg_lower_allN_of_stratifiable hs hs0 hB
    (leechResidualStratifiable24_of_neg hneg) (sphereCellStratifiable24_of_stratifiable hsph)

/-- Conjecture form of the lower half, with the actual double integral and the Leech Epstein
value.  No hypothesis is used. -/
theorem sphere24_riesz_neg_lower_conjecture_form {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s Y-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere24_riesz_neg_lower_allN hs hs0 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyNeg24, sphereRieszConstNeg24_eq_pair_integral hs hs0,
    sphereRieszCoefficientNeg24_eq_epstein hs0] at hY

/-- Conjecture form of the universal upper half under all-scale Leech contact certificates
(stage G24). -/
theorem sphere24_riesz_neg_upper_conjecture_form
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      (energyRpowD s X-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) ≤
        ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere24_riesz_neg_upper_of_contact hG24 hs hs0 η hη
  refine ⟨N₀, fun N hN X => ?_⟩
  have hX := h N hN X
  rwa [normalizedEnergyNeg24, sphereRieszConstNeg24_eq_pair_integral hs hs0,
    sphereRieszCoefficientNeg24_eq_epstein hs0] at hX

/-- The sharp asymptotics for every `-2 < s < 0` on S²⁴ in conjecture form (all configurations
above, some configuration below, every large `N`), with stage G24 as the only hypothesis. -/
theorem sphere24_riesz_neg_sharp_asymptotic
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      (energyRpowD s X-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) ≤
        ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re+η) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s Y-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24)) :=
  ⟨sphere24_riesz_neg_upper_conjecture_form hG24 hs hs0,
    sphere24_riesz_neg_lower_conjecture_form hs hs0⟩

end SphericalRiesz
end
end
