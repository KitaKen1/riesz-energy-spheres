import Riesz.HexProfileLower2
import Riesz.SphereBallD
import Riesz.CubeLebesgue
import Riesz.GaussianMellin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Riesz.FiniteBackground
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Riesz.SphereRieszMellinRpow8
import Riesz.HexLattice2
import Riesz.SphereRieszLowerRpow8
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! The Mellin form of the Riesz energy on S² and the universal lower bound for `0 < s < 2`
(stage S2-2 of the S² chain; dimension-2 counterparts of `SphereRieszLower24` and of the sphere
part of `LeechEpstein24`).

* `SphereRieszLower2`: the Gaussian background of S² (`B(t) = ½ ∫₀² e^(-2tv) dv ≤ 1/(4t)`), the
  density-scaled centred profile, the Mellin form
  `(E_s - I_s N²)/N^(1+s/2) = c_s ∫ α^(s/2-1) F_N(α) dα`, the regularized theta profile
  `α^(s/2-1)(Θ(α) - α⁻¹ - 1)` of the triangular lattice, and the universal lower bound by Fatou
  under the sharp Gaussian profile of the sphere; `I_s` is the actual double integral.
* `HexEpsteinSphere2`: the coefficient is `A₂^(-s/2) Re ζ_Λ(s)` with the continued Epstein zeta
  function of the triangular lattice of covolume one (variable `u = s/2`).

The lower bounds are stated under `∀ β > 0, ∃ f, HexGaussianContactCertificate2 β f`; that
hypothesis is discharged in `Riesz.HexGaussianBridge2`. -/

section

/-! # The Riesz energy of `S²` for `0 < s < 2`: Mellin form and universal lower bound (stage S2-2)

Dimension-2 port of `SphereRieszLower24`: the unit sphere `S² ⊂ ℝ³` with its uniform probability
measure `σ`, and the triangular lattice of covolume one in place of the Leech lattice.

* Background.  The Gaussian background `B(t) = ∫∫ exp(-t |x - y|²) dσ dσ` is written as an
  integral over the unit ball of `ℝ³`, then in polar coordinates around the north pole,
  `B(t) = (1/2) ∫_0^π sin θ exp(-t (2 - 2 cos θ)) dθ`, and in the height `v = 1 - cos θ`,
  `B(t) = (1/2) ∫_0^2 exp(-2 t v) dv`.  Hence `B(t) ≤ 1/(4t) = (π/A)/t`, `A = 4π` the area of `S²`.
* Majorant.  At the density scale `sphereGaussianScale2 N α = π α N/A` the background satisfies
  `N B ≤ α⁻¹`; the centred Gaussian profile of every configuration is at least `-min(1, α⁻¹)`,
  and `α^(s/2-1) min(1, α⁻¹)` is integrable on `(0, ∞)` for `0 < s < 2`.
* Mellin form.  For `0 < s < 2` the constant `I_s = sphereRieszConst2 s` is the Mellin transform
  of the background, and the normalized energy `(E_s - I_s N²)/N^(1+s/2)` of a configuration is
  `π^(s/2) A^(-s/2)/Γ(s/2)` times the Mellin integral of its centred Gaussian profile at the
  density scale.
* Lower bound.  With the regularized theta profile `α^(s/2-1) (Θ(α) - α⁻¹ - 1)` of the triangular
  lattice and Fatou's lemma, the sharp Gaussian profile of `S²` gives
  `(E_s - I_s N²)/N^(1+s/2) ≥ C_s - η` for all configurations of `N ≥ N₀(η)` points, with
  `C_s = sphereRieszCoefficient2 s`, under Gaussian certificates of the lattice at all scales.
* The measures of `S²` have no atoms, and `I_s` is the double integral of `|x - y|^(-s)`.

The stages of the dimension-24 file are kept in order, in one namespace; the `open` commands
accumulate as they do there. -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

/-! ## The Gaussian background as an integral over the unit ball of `ℝ³` -/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

theorem northPole2_dist_sq (q : SphereD 2) :
    dist northPole2 q ^ 2 = 2 - 2 * (q : AmbientD 2) 0 := by
  change ‖(northPole2 : AmbientD 2) - (q : AmbientD 2)‖ ^ 2 = _
  rw [norm_sub_sq_real]
  have hp : ‖(northPole2 : AmbientD 2)‖ = 1 := mem_sphere_zero_iff_norm.mp northPole2.property
  have hq : ‖(q : AmbientD 2)‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  have hi : ⟪(northPole2 : AmbientD 2), (q : AmbientD 2)⟫ = (q : AmbientD 2) 0 := by
    simp [northPole2, EuclideanSpace.inner_single_left]
  rw [hp, hq, hi]
  ring

theorem northPole2_gaussian_coordinate (t : ℝ) (q : (SphereD 2)) :
    sphereGaussianKernel2 t northPole2 q =
      Real.exp (-(t*(2-2*(q:(AmbientD 2)) 0))) := by
  unfold sphereGaussianKernel2
  rw [northPole2_dist_sq]

/-- The Gaussian kernel between the north pole and the direction `v/|v|` of a vector `v` of `ℝ³`. -/
def ambientPoleGaussian2 (t : ℝ) (v : (AmbientD 2)) : ℝ :=
  Real.exp (-(t*(2-2*v 0/‖v‖)))

theorem ambientPoleGaussian2_measurable (t : ℝ) : Measurable (ambientPoleGaussian2 t) := by
  unfold ambientPoleGaussian2
  fun_prop

theorem northPole2_direction_gaussian (t : ℝ) (z : (NonzeroD 2)) :
    sphereGaussianKernel2 t northPole2 ((sphereDirectionD 2) z) = ambientPoleGaussian2 t z := by
  rw [northPole2_gaussian_coordinate, (sphereDirectionD_coe 2)]
  unfold ambientPoleGaussian2
  simp only [PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv]
  congr 2
  ring

theorem sphereGaussianPotential2_ball_integral (t : ℝ) (p : (SphereD 2)) :
    sphereGaussianPotential2 t p =
      ∫ z, sphereGaussianKernel2 t p ((sphereDirectionD 2) z) ∂(sphereBallProbabilityD 2) := by
  unfold sphereGaussianPotential2
  rw [← (sphereBallProbabilityD_direction_preserving 2).map_eq]
  exact integral_map (sphereDirectionD_measurable 2).aemeasurable (by unfold sphereGaussianKernel2; fun_prop)

theorem gaussian_unitBallNonzero2_preimage :
    (Subtype.val : (NonzeroD 2) → (AmbientD 2)) ⁻¹' ball 0 1 = (unitBallNonzeroD 2) := by
  ext z
  simp [unitBallNonzeroD]

theorem ambientPoleGaussian2_unitBall_integrable {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (ambientPoleGaussian2 t) (ball (0:(AmbientD 2)) 1) := by
  have hi := (sphereBallProbabilityD_direction_preserving 2).integrable_comp
    (by unfold sphereGaussianKernel2; fun_prop : AEStronglyMeasurable
      (sphereGaussianKernel2 t northPole2) (sphereProbabilityD 2))
  have h := hi.mpr (sphereGaussianKernel2_integrable ht northPole2)
  change Integrable (fun z : (NonzeroD 2) => sphereGaussianKernel2 t northPole2 ((sphereDirectionD 2) z))
    (sphereBallProbabilityD 2) at h
  simp_rw [northPole2_direction_gaussian] at h
  unfold sphereBallProbabilityD sphereBallMeasureD at h
  have h' := (integrable_inv_smul_measure (NeZero.ne ((sphereAreaD 2) univ))
    (by finiteness : (sphereAreaD 2) univ ≠ ⊤)).mp h
  rw [show ((2 : ℕ) : ENNReal) + 1 = 3 by norm_num] at h'
  have h'' := (integrable_smul_measure (by norm_num : (3:ENNReal) ≠ 0)
    (by norm_num : (3:ENNReal) ≠ ⊤)).mp h'
  have he : MeasurableEmbedding (Subtype.val : (NonzeroD 2) → (AmbientD 2)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  rw [← gaussian_unitBallNonzero2_preimage, ← he.comap_restrict] at h''
  have hin : IntegrableOn (ambientPoleGaussian2 t) (NonzeroD 2) (volume.restrict (ball 0 1)) := by
    apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:(AmbientD 2))).compl).mpr
    simpa only [Function.comp_def] using h''
  change Integrable (ambientPoleGaussian2 t) ((volume.restrict (ball 0 1)).restrict {0}ᶜ) at hin
  rw [restrict_compl_singleton] at hin
  exact hin

theorem sphereGaussianBackground2_ball {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground2 t =
      ((sphereAreaD 2).real univ)⁻¹*3*∫ v in ball (0:(AmbientD 2)) 1, ambientPoleGaussian2 t v := by
  rw [sphereGaussianBackground2_eq_potential ht northPole2,
    sphereGaussianPotential2_ball_integral]
  simp_rw [northPole2_direction_gaussian]
  unfold sphereBallProbabilityD sphereBallMeasureD
  rw [integral_smul_measure, integral_smul_measure]
  rw [show ((2 : ℕ) : ENNReal) + 1 = 3 by norm_num]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  have he : MeasurableEmbedding (Subtype.val : (NonzeroD 2) → (AmbientD 2)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  have hint : (∫ z : (NonzeroD 2), ambientPoleGaussian2 t z
      ∂((volume:Measure (AmbientD 2)).comap Subtype.val).restrict (unitBallNonzeroD 2)) =
      ∫ v in ball (0:(AmbientD 2)) 1, ambientPoleGaussian2 t v := by
    rw [← gaussian_unitBallNonzero2_preimage, ← he.comap_restrict,
      integral_subtype_comap (measurableSet_singleton (0:(AmbientD 2))).compl (ambientPoleGaussian2 t)]
    change (∫ v, ambientPoleGaussian2 t v ∂(volume.restrict (ball 0 1)).restrict {0}ᶜ) = _
    rw [restrict_compl_singleton]
  rw [hint]
  change ((sphereAreaD 2).real univ)⁻¹*(3*_) = _
  ring

/-- `ambientPoleGaussian2` cut off outside the unit ball of `ℝ³`. -/
def ambientPoleGaussianBall2 (t : ℝ) : (AmbientD 2) → ℝ :=
  (ball 0 1).indicator (ambientPoleGaussian2 t)

theorem ambientPoleGaussianBall2_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (ambientPoleGaussianBall2 t) :=
  (integrable_indicator_iff measurableSet_ball).mpr (ambientPoleGaussian2_unitBall_integrable ht)

theorem ambientPoleGaussianBall2_integral (t : ℝ) :
    (∫ v, ambientPoleGaussianBall2 t v) = ∫ v in ball (0:(AmbientD 2)) 1, ambientPoleGaussian2 t v :=
  integral_indicator measurableSet_ball

/-! ## Polar coordinates around the north pole

The ball of `ℝ³` is split as `ℝ × ℝ²` (height, transverse plane); the transverse plane is
integrated radially and the half plane of height and transverse radius in polar coordinates.
Result: `B(t) = (1/2) ∫_0^π sin θ exp(-t (2 - 2 cos θ)) dθ`. -/

/-- The plane transverse to the polar axis, as a Euclidean space. -/
abbrev PoleTransverse2 := EuclideanSpace ℝ (Fin 2)

/-- `ℝ × ℝ² ≃ ℝ³`: the height along the polar axis first, then the transverse coordinates. -/
def ambientCons3 : (ℝ × (Fin 2 → ℝ)) ≃ᵐ AmbientD 2 :=
  (Boundary.cubeConsEquiv 2).trans (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

theorem ambientCons3_apply (p : ℝ × (Fin 2 → ℝ)) :
    ambientCons3 p = WithLp.toLp 2 (Fin.cons p.1 p.2) := by
  simp [ambientCons3, Boundary.cubeConsEquiv_apply]

theorem ambientCons3_measurePreserving : MeasurePreserving ambientCons3 volume volume :=
  (PiLp.volume_preserving_toLp (Fin 3)).comp (Boundary.cubeConsEquiv_measurePreserving 2)

theorem ambientCons3_norm_sq (p : ℝ × (Fin 2 → ℝ)) :
    ‖ambientCons3 p‖ ^ 2 = p.1 ^ 2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse2)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [ambientCons3_apply, Fin.sum_univ_succ]

theorem ambientCons3_norm (p : ℝ × (Fin 2 → ℝ)) :
    ‖ambientCons3 p‖ = Real.sqrt (p.1^2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse2)‖^2) := by
  rw [← ambientCons3_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The unit disc of the transverse plane has area `π` (`π^(d/2)/(d/2)!` with `d = 2`). -/
theorem poleTransverse2_unit_ball_volume :
    (volume : Measure PoleTransverse2).real (ball 0 1) = Real.pi := by
  have hv : volume (ball (0 : PoleTransverse2) 1) = ENNReal.ofReal Real.pi := by
    rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp [PoleTransverse2])]
    norm_num [PoleTransverse2]
  rw [Measure.real, hv, ENNReal.toReal_ofReal Real.pi_pos.le]

theorem poleRadialPower2_setIntegral :
    (∫ r in Ioo (0 : ℝ) 1, r ^ 2) = 1 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num

/-- The integrand on the unit ball in the height `a` and the transverse radius `r`. -/
def poleRadialGaussian2 (t a r : ℝ) : ℝ :=
  if a^2+r^2 < 1 then Real.exp (-(t*(2-2*a/Real.sqrt (a^2+r^2)))) else 0

/-- The integrand on the half plane of height and transverse radius `r > 0`, with the weight
`r^(d-1) = r` of the radial integration in the transverse plane. -/
def poleHalfPlaneGaussian2 (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then p.2*poleRadialGaussian2 t p.1 p.2 else 0

/-- The integrand in the polar angle: `sin θ exp(-t (2 - 2 cos θ))` (`sin^(d-1) θ` with `d = 2`). -/
def poleAngularGaussian2 (t θ : ℝ) : ℝ :=
  Real.sin θ * Real.exp (-(t*(2-2*Real.cos θ)))

/-- The integrand in polar coordinates (radius, angle) of the half plane, on `(0, 1) × (0, π)`. -/
def poleRectangleGaussian2 (t : ℝ) : ℝ × ℝ → ℝ :=
  (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi).indicator
    (fun p => p.1^2*poleAngularGaussian2 t p.2)

theorem poleAngularGaussian2_continuous (t : ℝ) : Continuous (poleAngularGaussian2 t) := by
  unfold poleAngularGaussian2
  fun_prop

theorem poleRadialGaussian2_nonneg (t a r : ℝ) : 0 ≤ poleRadialGaussian2 t a r := by
  unfold poleRadialGaussian2
  split_ifs <;> positivity

theorem poleRadialGaussian2_le_one {t : ℝ} (ht : 0 ≤ t) (a r : ℝ) (hr : 0 < r) :
    poleRadialGaussian2 t a r ≤ 1 := by
  have hs : 0 < Real.sqrt (a^2+r^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])
  have ha : a ≤ Real.sqrt (a^2+r^2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
  have hq : a/Real.sqrt (a^2+r^2) ≤ 1 := (div_le_iff₀ hs).mpr (by simpa using ha)
  unfold poleRadialGaussian2
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    apply mul_nonneg ht
    simp only [mul_div_assoc]
    linarith
  · norm_num

theorem poleHalfPlaneGaussian2_nonneg (t : ℝ) (p : ℝ × ℝ) :
    0 ≤ poleHalfPlaneGaussian2 t p := by
  unfold poleHalfPlaneGaussian2
  split_ifs with hr
  · exact mul_nonneg hr.le (poleRadialGaussian2_nonneg _ _ _)
  · norm_num

theorem poleHalfPlaneGaussian2_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (poleHalfPlaneGaussian2 t) := by
  let s : Set (ℝ × ℝ) := Icc (-1:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hs : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : (volume:Measure (ℝ × ℝ)) s ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi : Integrable (s.indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hfinite)
  have hm : Measurable (poleHalfPlaneGaussian2 t) := by
    unfold poleHalfPlaneGaussian2
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    · apply measurable_snd.mul
      unfold poleRadialGaussian2
      exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
        (by fun_prop) measurable_const
    · exact measurable_const
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (poleHalfPlaneGaussian2_nonneg t p)]
  by_cases hr : 0 < p.2
  · by_cases hb : p.1^2+p.2^2 < 1
    · have hr1 : p.2 ≤ 1 := by nlinarith [sq_nonneg p.1]
      have hm : p ∈ s := ⟨⟨by nlinarith [sq_nonneg p.2],
        by nlinarith [sq_nonneg p.2]⟩,⟨hr.le,hr1⟩⟩
      rw [indicator_of_mem hm]
      change poleHalfPlaneGaussian2 t p ≤ 1
      rw [poleHalfPlaneGaussian2, ite_eq_left hr]
      simpa only [one_mul] using mul_le_mul hr1
        (poleRadialGaussian2_le_one ht p.1 p.2 hr)
        (poleRadialGaussian2_nonneg t p.1 p.2) zero_le_one
    · simp only [poleHalfPlaneGaussian2, ite_eq_left hr, poleRadialGaussian2, ite_eq_right hb,
        mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) p
  · simp only [poleHalfPlaneGaussian2, ite_eq_right hr]
    exact indicator_nonneg (fun _ _ => zero_le_one) p

theorem ambientPoleGaussianBall2_split (t : ℝ) (p : ℝ × (Fin 2 → ℝ)) :
    ambientPoleGaussianBall2 t (ambientCons3 p) =
      poleRadialGaussian2 t p.1 ‖(WithLp.toLp 2 p.2:PoleTransverse2)‖ := by
  have hi : ‖ambientCons3 p‖ < 1 ↔
      p.1^2+‖(WithLp.toLp 2 p.2:PoleTransverse2)‖^2 < 1 := by
    rw [← ambientCons3_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (ambientCons3 p)]
  have hz : ambientCons3 p 0 = p.1 := by simp [ambientCons3_apply]
  unfold ambientPoleGaussianBall2 ambientPoleGaussian2 poleRadialGaussian2
  simp only [indicator, mem_ball, dist_zero_right, hi]
  rw [hz, ambientCons3_norm]

theorem poleRadialGaussian2_polar (t r θ : ℝ) (hr : 0 < r) :
    poleRadialGaussian2 t (r*Real.cos θ) (r*Real.sin θ) =
      if r < 1 then Real.exp (-(t*(2-2*Real.cos θ))) else 0 := by
  have hs : (r*Real.cos θ)^2+(r*Real.sin θ)^2 = r^2 := by
    calc
      _ = r^2*(Real.cos θ^2+Real.sin θ^2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  have hi : r^2 < 1 ↔ r < 1 := by constructor <;> intro h <;> nlinarith
  unfold poleRadialGaussian2
  simp only [hs, Real.sqrt_sq hr.le, hi]
  have hc : 2*(r*Real.cos θ)/r = 2*Real.cos θ := by field_simp
  rw [hc]

theorem poleHalfPlaneGaussian2_polar (t : ℝ) (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1*poleHalfPlaneGaussian2 t (polarCoord.symm p) = poleRectangleGaussian2 t p := by
  change p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi at hp
  have hr : 0 < p.1 := hp.1
  have htlo : -Real.pi < p.2 := hp.2.1
  have hthi : p.2 < Real.pi := hp.2.2
  change p.1*(if 0 < p.1*Real.sin p.2 then
      (p.1*Real.sin p.2)*poleRadialGaussian2 t (p.1*Real.cos p.2) (p.1*Real.sin p.2)
      else 0) = _
  rw [poleRadialGaussian2_polar t p.1 p.2 hr]
  by_cases hθ : 0 < p.2
  · have hpos := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ hthi)
    rw [ite_eq_left hpos]
    by_cases h1 : p.1 < 1
    · have hm : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := ⟨⟨hr,h1⟩,⟨hθ,hthi⟩⟩
      rw [ite_eq_left h1, poleRectangleGaussian2, indicator_of_mem hm]
      unfold poleAngularGaussian2
      ring
    · have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := fun h => h1 h.1.2
      simp [h1, poleRectangleGaussian2, hm]
  · have hs : Real.sin p.2 ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hθ) htlo.le
    have hnon : ¬0 < p.1*Real.sin p.2 :=
      not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le hs)
    have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := fun h => hθ h.2.1
    simp [hnon, poleRectangleGaussian2, hm]

theorem poleRectangleGaussian2_zero_off_target (t : ℝ) (p : ℝ × ℝ)
    (hp : p ∉ polarCoord.target) : poleRectangleGaussian2 t p = 0 := by
  apply indicator_of_notMem
  intro hm
  apply hp
  change p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  exact ⟨hm.1.1,⟨by linarith [hm.2.1,Real.pi_pos],hm.2.2⟩⟩

theorem poleRectangleGaussian2_integral (t : ℝ) :
    (∫ p, poleRectangleGaussian2 t p) =
      (1/3:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian2 t θ := by
  rw [poleRectangleGaussian2, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    show (volume:Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul (fun r : ℝ => r^2) (poleAngularGaussian2 t),
    poleRadialPower2_setIntegral]

theorem poleHalfPlaneGaussian2_integral (t : ℝ) :
    (∫ p, poleHalfPlaneGaussian2 t p) =
      (1/3:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian2 t θ := by
  rw [← integral_comp_polarCoord_symm]
  have h : (∫ p in polarCoord.target, p.1 • poleHalfPlaneGaussian2 t (polarCoord.symm p)) =
      ∫ p in polarCoord.target, poleRectangleGaussian2 t p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    exact poleHalfPlaneGaussian2_polar t p hp
  rw [h, setIntegral_eq_integral_of_forall_compl_eq_zero (poleRectangleGaussian2_zero_off_target t),
    poleRectangleGaussian2_integral]

theorem poleHalfPlaneGaussian2_radial_integral (t a : ℝ) :
    (∫ r in Ioi (0:ℝ), r*poleRadialGaussian2 t a r) =
      ∫ r : ℝ, poleHalfPlaneGaussian2 t (a,r) := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1

theorem poleRadialGaussian2_transverse_integral (t a : ℝ) :
    (∫ u : Fin 2 → ℝ, poleRadialGaussian2 t a ‖(WithLp.toLp 2 u:PoleTransverse2)‖) =
      (2*Real.pi)*∫ r : ℝ, poleHalfPlaneGaussian2 t (a,r) := by
  calc
    _ = ∫ u : PoleTransverse2, poleRadialGaussian2 t a ‖u‖ :=
      (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding _
    _ = _ := by
      rw [integral_fun_norm_addHaar (volume:Measure PoleTransverse2)]
      simp only [PoleTransverse2,finrank_euclideanSpace_fin,Nat.reduceSub,pow_one,
        smul_eq_mul,poleTransverse2_unit_ball_volume]
      rw [poleHalfPlaneGaussian2_radial_integral]
      ring

theorem ambientPoleGaussianBall2_integral_angular {t : ℝ} (ht : 0 ≤ t) :
    (∫ v : (AmbientD 2), ambientPoleGaussianBall2 t v) =
      (2*Real.pi/3)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian2 t θ := by
  have hi : Integrable (ambientPoleGaussianBall2 t ∘ ambientCons3) :=
    ambientCons3_measurePreserving.integrable_comp_of_integrable
      (ambientPoleGaussianBall2_integrable ht)
  calc
    _ = ∫ p : ℝ × (Fin 2 → ℝ), ambientPoleGaussianBall2 t (ambientCons3 p) :=
      (ambientCons3_measurePreserving.integral_comp' (ambientPoleGaussianBall2 t)).symm
    _ = ∫ a : ℝ, ∫ u : Fin 2 → ℝ, ambientPoleGaussianBall2 t (ambientCons3 (a,u)) :=
      integral_prod _ hi
    _ = ∫ a : ℝ, (2*Real.pi)*∫ r : ℝ, poleHalfPlaneGaussian2 t (a,r) := by
      simp_rw [ambientPoleGaussianBall2_split, poleRadialGaussian2_transverse_integral]
    _ = _ := by
      rw [integral_const_mul, ← integral_prod _ (poleHalfPlaneGaussian2_integrable ht),
        ← Measure.volume_eq_prod, poleHalfPlaneGaussian2_integral]
      ring

theorem sphereGaussianBackground2_angular {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground2 t =
      (1/2:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian2 t θ := by
  rw [sphereGaussianBackground2_ball ht, ← ambientPoleGaussianBall2_integral,
    ambientPoleGaussianBall2_integral_angular ht, sphereArea2_univ_real]
  have h4 : (4*Real.pi)⁻¹*(4*Real.pi) = 1 :=
    inv_mul_cancel₀ (mul_pos (by norm_num) Real.pi_pos).ne'
  linear_combination
    ((1/2:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian2 t θ)*h4

/-! ## The background in the height variable and its decay

With `v = 1 - cos θ`, `B(t) = (1/2) ∫_0^2 exp(-2 t v) dv`.  In dimension `d` the integrand carries
the factor `v^(d/2-1) (2-v)^(d/2-1)`, which is `1` for `d = 2`.  Hence `B(t) ≤ 1/(4t)`. -/

/-- The integrand of the background in the height `v = 1 - cos θ` above the pole.  In dimension
`d` it is `exp(-2tv) v^(d/2-1) (2-v)^(d/2-1)`; for `d = 2` the polynomial factor is `1`. -/
def polePolynomialGaussian2 (t v : ℝ) : ℝ :=
  Real.exp (-(2*t*v))

theorem polePolynomialGaussian2_eq (t v : ℝ) :
    polePolynomialGaussian2 t v = Real.exp (-(2*t*v)) := rfl

theorem polePolynomialGaussian2_continuous (t : ℝ) : Continuous (polePolynomialGaussian2 t) := by
  unfold polePolynomialGaussian2
  fun_prop

theorem poleHeight2_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun u : ℝ => 1-Real.cos u) (Real.sin θ) θ := by
  convert (Real.hasDerivAt_cos θ).neg.const_add 1 using 1
  simp

theorem poleAngularGaussian2_polynomial (t θ : ℝ) :
    poleAngularGaussian2 t θ = polePolynomialGaussian2 t (1-Real.cos θ)*Real.sin θ := by
  unfold poleAngularGaussian2 polePolynomialGaussian2
  have he : -(t*(2-2*Real.cos θ)) = -(2*t*(1-Real.cos θ)) := by ring
  rw [he]
  ring

theorem poleAngularGaussian2_interval_polynomial (t : ℝ) :
    (∫ θ in (0:ℝ)..Real.pi, poleAngularGaussian2 t θ) =
      ∫ v in (0:ℝ)..2, polePolynomialGaussian2 t v := by
  simp_rw [poleAngularGaussian2_polynomial]
  have h := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := Real.pi)
    (f := fun θ : ℝ => 1-Real.cos θ) (f' := Real.sin) (g := polePolynomialGaussian2 t)
    (fun θ _ => poleHeight2_hasDerivAt θ) Real.continuous_sin.continuousOn
    (polePolynomialGaussian2_continuous t)
  simpa only [Function.comp_def, Real.cos_zero, Real.cos_pi, sub_self,
    sub_neg_eq_add, one_add_one_eq_two] using h

theorem poleAngularGaussian2_set_polynomial (t : ℝ) :
    (∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian2 t θ) =
      ∫ v in (0:ℝ)..2, polePolynomialGaussian2 t v := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact poleAngularGaussian2_interval_polynomial t

theorem sphereGaussianBackground2_polynomial {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground2 t =
      (1/2:ℝ)*∫ v in (0:ℝ)..2, polePolynomialGaussian2 t v := by
  rw [sphereGaussianBackground2_angular ht, poleAngularGaussian2_set_polynomial]

theorem sphereGaussianBackground2_polynomial_set {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground2 t =
      (1/2:ℝ)*∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian2 t v := by
  rw [sphereGaussianBackground2_polynomial ht,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2), integral_Ioc_eq_integral_Ioo]

theorem polePolynomialGaussian2_nonneg (t v : ℝ) : 0 ≤ polePolynomialGaussian2 t v :=
  (Real.exp_pos _).le

/-- `∫_0^∞ exp(-2tv) dv = 1/(2t)`: the Gamma moment of order `d/2 - 1 = 0`. -/
theorem zerothGaussian2_integral {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ in Ioi 0, Real.exp (-(2*t*v))) = 1/(2*t) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1) (r := 2*t) (by norm_num) (by positivity)
  simpa only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] using h

theorem zerothGaussian2_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => Real.exp (-(2*t*v))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [zerothGaussian2_integral ht]
  exact (by positivity : (0:ℝ) < 1/(2*t)).ne'

/-- The Gaussian background of `S²` is at most `1/(4t)`. -/
theorem sphereGaussianBackground2_decay {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground2 t ≤ (1/4:ℝ)/t := by
  have hf := zerothGaussian2_integrable ht
  have htail : (∫ v in Ioo (0:ℝ) 2, Real.exp (-(2*t*v))) ≤
      ∫ v in Ioi (0:ℝ), Real.exp (-(2*t*v)) := by
    apply setIntegral_mono_set hf
    · filter_upwards [] with v
      exact (Real.exp_pos _).le
    · exact .of_forall fun v hv => hv.1
  rw [sphereGaussianBackground2_polynomial_set ht.le]
  unfold polePolynomialGaussian2
  calc
    _ ≤ (1/2:ℝ)*(∫ v in Ioi (0:ℝ), Real.exp (-(2*t*v))) :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = _ := by rw [zerothGaussian2_integral ht]; ring

theorem sphereGaussianBackground2_min_bound {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground2 t ≤ min 1 ((1/4:ℝ)/t) :=
  le_min (sphereGaussianBackground2_le_one ht.le) (sphereGaussianBackground2_decay ht)

/-- The decay with the area normalization: `π/A = 1/4` for the area `A = 4π` of `S²`. -/
theorem sphereGaussianBackground2_area_decay {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground2 t ≤ (Real.pi/(sphereAreaD 2).real univ)/t := by
  have h4 : (4*Real.pi) ≠ 0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  have hC : Real.pi/(sphereAreaD 2).real univ = (1/4:ℝ) := by
    rw [sphereArea2_univ_real, div_eq_iff h4]
    ring
  rw [hC]
  exact sphereGaussianBackground2_decay ht

/-! ## The common lower bound of the centred Gaussian energy -/

open ProbabilityTheory

theorem sphereGaussianPair2_diagonal_lower {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) :
    (N:ℝ) ≤ ∑ i, ∑ j, sphereGaussianKernel2 t (X i) (X j) := by
  have h := gaussian_diagonal_lower t (fun i : Fin N => (X i:(AmbientD 2)))
  simpa only [kernelPair, one_mul, mul_one, Fintype.card_fin,
    sphereGaussianKernel2_eq_ambient] using h

theorem sphereGaussianPair2_background_lower {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (X : (ConfigurationD 2) N) :
    (N:ℝ)^2*sphereGaussianBackground2 t ≤ ∑ i, ∑ j, sphereGaussianKernel2 t (X i) (X j) := by
  have h := sphereGaussianDefect2_nonneg ht (N:ℝ) X
  rw [sphereGaussianDefect2_charge_N ht] at h
  exact sub_nonneg.mp h

theorem sphereGaussianCentered2_common_lower_of_bound {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 ≤ t) (X : (ConfigurationD 2) N) (C : ℝ)
    (hbackground : (N:ℝ)*sphereGaussianBackground2 t ≤ C) :
    -min 1 C ≤
      (∑ i, ∑ j, sphereGaussianKernel2 t (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground2 t - 1 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hpair := sphereGaussianPair2_background_lower ht X
  have hdiag := sphereGaussianPair2_diagonal_lower t X
  apply background_subtracted_common_lower
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hNR).mpr
    nlinarith [hpair]
  · exact (le_div_iff₀ hNR).mpr (by simpa using hdiag)
  · exact hbackground

theorem sphereGaussianCentered2_common_lower {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t)
    (X : (ConfigurationD 2) N) :
    -min 1 ((N:ℝ)*sphereGaussianBackground2 t) ≤
      (∑ i, ∑ j, sphereGaussianKernel2 t (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground2 t - 1 :=
  sphereGaussianCentered2_common_lower_of_bound hN ht X _ le_rfl

/-! ## The integrable majorant at the density scale, for `0 < s < 2` -/

theorem sphereGaussianScale2_pos {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    0 < sphereGaussianScale2 N α := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  unfold sphereGaussianScale2
  positivity

/-- At the density scale the background of `N` points is at most `α⁻¹` (the cap `(α^(d/2))⁻¹`
of the general dimension), for every `N`. -/
theorem sphereGaussianBackground2_scaled_cap {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) :
    (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) ≤ α⁻¹ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have h := mul_le_mul_of_nonneg_left
    (sphereGaussianBackground2_area_decay (sphereGaussianScale2_pos hN hα)) hNR.le
  calc
    _ ≤ (N:ℝ)*(Real.pi/(sphereAreaD 2).real univ)/(sphereGaussianScale2 N α) := by
      simpa only [mul_div_assoc] using h
    _ = _ := by
      have hx : Real.pi*α*((N:ℝ)/(sphereAreaD 2).real univ) ≠ 0 :=
        (mul_pos (mul_pos Real.pi_pos hα) (div_pos hNR hA)).ne'
      have hα1 : α⁻¹*α = 1 := inv_mul_cancel₀ hα.ne'
      rw [sphereGaussianScale2_eq, div_eq_iff hx]
      linear_combination (-((N:ℝ)*(Real.pi/(sphereAreaD 2).real univ)))*hα1

theorem sphereGaussianCentered2_scaled_common_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 2) N) :
    -min 1 (α⁻¹) ≤
      (∑ i, ∑ j, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) - 1 :=
  sphereGaussianCentered2_common_lower_of_bound hN (sphereGaussianScale2_pos hN hα).le X _
    (sphereGaussianBackground2_scaled_cap hN hα)

/-- A one-sided background replacement; no background asymptotic is a premise. -/
theorem sphereGaussianCentered2_flat_baseline_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 2) N) :
    (∑ i, ∑ j, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ) -
        α⁻¹ - 1 ≤
      (∑ i, ∑ j, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) - 1 := by
  linarith [sphereGaussianBackground2_scaled_cap hN hα]

/-- The Fatou majorant `α^(s/2-1) min(1, α⁻¹)`. -/
def sphereGaussianMajorant2 (s α : ℝ) : ℝ := α^(s/2-1)*min 1 (α⁻¹)

theorem sphereGaussianMajorant2_small (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    sphereGaussianMajorant2 s α = α^(s/2-1) := by
  rw [sphereGaussianMajorant2, min_eq_left ((one_le_inv₀ hα).mpr hα1), mul_one]

theorem sphereGaussianMajorant2_large (s : ℝ) {α : ℝ} (hα1 : 1 ≤ α) :
    sphereGaussianMajorant2 s α = α^(s/2-2) := by
  have hα : 0 < α := lt_of_lt_of_le zero_lt_one hα1
  have hpow : α^(s/2-2) = α^(s/2-1)*α⁻¹ := by
    have he : s/2-2 = (s/2-1)-(1:ℝ) := by ring
    rw [he,Real.rpow_sub hα,Real.rpow_one,div_eq_mul_inv]
  rw [sphereGaussianMajorant2,min_eq_right ((inv_le_one₀ hα).mpr hα1),hpow]

theorem sphereGaussianMajorant2_nonneg (s : ℝ) {α : ℝ} (hα : 0 < α) :
    0 ≤ sphereGaussianMajorant2 s α := by
  unfold sphereGaussianMajorant2
  exact mul_nonneg (Real.rpow_nonneg hα.le _) (le_min zero_le_one (inv_nonneg.mpr hα.le))

theorem sphereGaussianMajorant2_integrable {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    IntegrableOn (sphereGaussianMajorant2 s) (Ioi 0) := by
  have hsmall : IntegrableOn (fun α : ℝ => α^(s/2-1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  have hlarge : IntegrableOn (fun α : ℝ => α^(s/2-2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hi := ((hsmall.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi (0:ℝ))).add
    ((hlarge.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi (0:ℝ)))
  apply hi.congr
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1:ℝ)) :
      ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ∈ ({1}:Set ℝ)ᶜ)
    intro α hα
    simpa using hα
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with α hα hne1
  have hα0 : 0 < α := hα
  simp only [Pi.add_apply]
  rcases lt_or_gt_of_ne hne1 with hsmall | hlarge
  · rw [sphereGaussianMajorant2_small s hα0 hsmall.le,
      indicator_of_mem (show α ∈ Ioo 0 1 from ⟨hα0,hsmall⟩),
      indicator_of_notMem (show α ∉ Ioi 1 by simpa using hsmall.le)]
    simp
  · rw [sphereGaussianMajorant2_large s hlarge.le,
      indicator_of_notMem (notMem_Ioo_of_ge hlarge.le),
      indicator_of_mem (show α ∈ Ioi 1 from hlarge)]
    simp

theorem sphereGaussianCentered2_weighted_common_lower {N : ℕ} (hN : 0 < N)
    (s : ℝ) {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 2) N) :
    -sphereGaussianMajorant2 s α ≤ α^(s/2-1)*
      ((∑ i, ∑ j, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) - 1) := by
  have h := mul_le_mul_of_nonneg_left (sphereGaussianCentered2_scaled_common_lower hN hα X)
    (Real.rpow_nonneg hα.le (s/2-1))
  simpa only [sphereGaussianMajorant2,mul_neg] using h

/-! ## The Mellin form of the normalized Riesz energy, for `0 < s < 2`

Finite ordered energy, continuous background, Mellin integrability and the exact normalization at
the density scale, on the unit sphere `S²`. -/

/-- The Gaussian energy of a configuration over ordered pairs of distinct points. -/
def sphereGaussianOffDiagonal2 {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, sphereGaussianKernel2 t (X i) (X j)

theorem sphereGaussianOffDiagonal2_continuous {N : ℕ} (X : (ConfigurationD 2) N) :
    Continuous (fun t : ℝ => sphereGaussianOffDiagonal2 t X) := by
  unfold sphereGaussianOffDiagonal2 sphereGaussianKernel2
  fun_prop

theorem sphereGaussianOffDiagonal2_nonneg {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) :
    0 ≤ sphereGaussianOffDiagonal2 t X := by
  unfold sphereGaussianOffDiagonal2
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sphereGaussianKernel2_nonneg t (X i) (X j)

theorem sphereGaussianSum2_diagonal {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) :
    (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel2 t (X i) (X j)) =
      sphereGaussianOffDiagonal2 t X+(N:ℝ) := by
  calc
    _ = ∑ i : Fin N, ((∑ j ∈ Finset.univ.erase i,
        sphereGaussianKernel2 t (X i) (X j))+1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := Finset.sum_erase_add (s := Finset.univ) (a := i)
        (fun j : Fin N => sphereGaussianKernel2 t (X i) (X j)) (Finset.mem_univ i)
      simpa only [sphereGaussianKernel2_self] using h.symm
    _ = _ := by simp [sphereGaussianOffDiagonal2]

theorem sphereGaussianOffDiagonal2_eq_full_sub {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianOffDiagonal2 t X =
      (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel2 t (X i) (X j))-(N:ℝ) := by
  linarith [sphereGaussianSum2_diagonal t X]

/-- The off-diagonal Gaussian energy minus `N²` times the background. -/
def sphereGaussianRieszDefect2 {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) : ℝ :=
  sphereGaussianOffDiagonal2 t X-(N:ℝ)^2*sphereGaussianBackground2 t

theorem sphereGaussianRieszDefect2_eq_full {N : ℕ} (t : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianRieszDefect2 t X =
      (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel2 t (X i) (X j))-(N:ℝ)-
        (N:ℝ)^2*sphereGaussianBackground2 t := by
  rw [sphereGaussianRieszDefect2,sphereGaussianOffDiagonal2_eq_full_sub]

/-- The factor `π N/A` of the density scale: `sphereGaussianScale2 N α` is this factor times `α`. -/
def sphereGaussianDensityFactor2 (N : ℕ) : ℝ := sphereGaussianScale2 N 1

theorem sphereGaussianDensityFactor2_pos {N : ℕ} (hN : 0 < N) :
    0 < sphereGaussianDensityFactor2 N :=
  sphereGaussianScale2_pos hN zero_lt_one

theorem sphereGaussianScale2_eq_factor (N : ℕ) (α : ℝ) :
    sphereGaussianScale2 N α = sphereGaussianDensityFactor2 N*α := by
  unfold sphereGaussianDensityFactor2 sphereGaussianScale2
  ring

/-- The centred Gaussian profile of a configuration at the density scale: the normalized energy
(diagonal included) minus `N` times the background minus `1`. -/
def sphereGaussianCenteredScaled2 {N : ℕ} (α : ℝ) (X : (ConfigurationD 2) N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ)-
    (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α)-1

theorem sphereGaussianCenteredScaled2_defect {N : ℕ} (hN : 0 < N)
    (α : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianRieszDefect2 (sphereGaussianScale2 N α) X =
      (N:ℝ)*sphereGaussianCenteredScaled2 α X := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sphereGaussianRieszDefect2_eq_full]
  unfold sphereGaussianCenteredScaled2
  field_simp [hNR]
  ring

theorem sphereGaussianPair2_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 2) N) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianKernel2 t (X i) (X j)) (Ioi 0) := by
  have h := gaussianPair_mellin_rpow_integrable hs (offDiagonal_dist_posD X hij)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [sphereGaussianKernel2, mul_comm t]

theorem sphereGaussianPair2_mellin_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 2) N) {i j : Fin N} (hij : i ≠ j) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianKernel2 t (X i) (X j)) =
      Real.Gamma (s/2)*(dist (X i) (X j))^(-s) := by
  rw [← gaussianPair_mellin_rpow hs (offDiagonal_dist_posD X hij)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [sphereGaussianKernel2, mul_comm t]

theorem sphereGaussianOffDiagonal2_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 2) N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianOffDiagonal2 t X) (Ioi 0) := by
  unfold sphereGaussianOffDiagonal2
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact sphereGaussianPair2_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianOffDiagonal2_mellin_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 2) N) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianOffDiagonal2 t X) =
      Real.Gamma (s/2)*energyRpowD s X := by
  have hi (i : Fin N) : IntegrableOn
      (fun t : ℝ => ∑ j ∈ Finset.univ.erase i, t^(s/2-1)*sphereGaussianKernel2 t (X i) (X j))
      (Ioi 0) :=
    integrable_finsetSum _ (fun j hj =>
      sphereGaussianPair2_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm)
  unfold sphereGaussianOffDiagonal2 energyRpowD
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj =>
    sphereGaussianPair2_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm)]
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereGaussianPair2_mellin_rpow hs X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianBackground2_continuousOn : ContinuousOn sphereGaussianBackground2 (Ici 0) := by
  have hc : Continuous (fun t : ℝ =>
      (1/2:ℝ)*∫ v in Icc (0:ℝ) 2, polePolynomialGaussian2 t v) := by
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    unfold polePolynomialGaussian2
    fun_prop
  apply hc.continuousOn.congr
  intro t ht
  dsimp only
  rw [sphereGaussianBackground2_polynomial_set ht, integral_Icc_eq_integral_Ioo]

/-- The weighted background is dominated by the majorant.  The constant `max 1 (π/A)` of the
general dimension is `1` here, because `π/A = 1/4`. -/
theorem sphereGaussianBackground2_weighted_le_majorant {s t : ℝ} (ht : 0 < t) :
    |t^(s/2-1)*sphereGaussianBackground2 t| ≤ sphereGaussianMajorant2 s t := by
  have hB0 := sphereGaussianBackground2_nonneg t
  have hB := sphereGaussianBackground2_min_bound ht
  have hp : 0 ≤ t^(s/2-1) := Real.rpow_nonneg ht.le _
  have hti : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have h4 : (1/4:ℝ)/t ≤ t⁻¹ := by
    rw [div_eq_mul_inv]
    linarith
  have hmin : min 1 ((1/4:ℝ)/t) ≤ min 1 (t⁻¹) :=
    le_min (min_le_left _ _) ((min_le_right _ _).trans h4)
  rw [abs_of_nonneg (mul_nonneg hp hB0), sphereGaussianMajorant2]
  exact mul_le_mul_of_nonneg_left (hB.trans hmin) hp

theorem sphereGaussianBackground2_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianBackground2 t) (Ioi 0) := by
  have hmaj := sphereGaussianMajorant2_integrable hs hs2
  refine Integrable.mono' hmaj ?_ ?_
  · have hm : ContinuousOn (fun t : ℝ => t^(s/2-1)*sphereGaussianBackground2 t) (Ioi 0) := by
      apply ContinuousOn.mul
      · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
      · exact sphereGaussianBackground2_continuousOn.mono Ioi_subset_Ici_self
    exact hm.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact sphereGaussianBackground2_weighted_le_majorant ht

/-- The continuous Riesz `s`-energy constant `I_s` of the uniform measure of `S²`, defined by the
Gaussian Mellin integral of the sphere Gaussian background. -/
def sphereRieszConst2 (s : ℝ) : ℝ :=
  (Real.Gamma (s/2))⁻¹ * ∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianBackground2 t

theorem sphereGaussianRieszDefect2_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ} (X : (ConfigurationD 2) N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianRieszDefect2 t X) (Ioi 0) := by
  have hi := (sphereGaussianOffDiagonal2_weighted_integrable_rpow hs X).sub
    ((sphereGaussianBackground2_weighted_integrable_rpow hs hs2).const_mul ((N:ℝ)^2))
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  change t^(s/2-1)*sphereGaussianOffDiagonal2 t X-(N:ℝ)^2*(t^(s/2-1)*sphereGaussianBackground2 t) =
    t^(s/2-1)*(sphereGaussianOffDiagonal2 t X-(N:ℝ)^2*sphereGaussianBackground2 t)
  ring

theorem sphereGaussianRieszDefect2_mellin_rpow {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ} (X : (ConfigurationD 2) N) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianRieszDefect2 t X) =
      Real.Gamma (s/2)*(energyRpowD s X-sphereRieszConst2 s*(N:ℝ)^2) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have he : (fun t : ℝ => t^(s/2-1)*sphereGaussianRieszDefect2 t X) =
      (fun t : ℝ => t^(s/2-1)*sphereGaussianOffDiagonal2 t X-
        (N:ℝ)^2*(t^(s/2-1)*sphereGaussianBackground2 t)) := by
    ext t
    unfold sphereGaussianRieszDefect2
    ring
  rw [he, integral_sub (sphereGaussianOffDiagonal2_weighted_integrable_rpow hs X)
      ((sphereGaussianBackground2_weighted_integrable_rpow hs hs2).const_mul ((N:ℝ)^2)),
    integral_const_mul, sphereGaussianOffDiagonal2_mellin_rpow hs]
  unfold sphereRieszConst2
  field_simp

theorem sphereGaussianRieszDefect2_scaled_mellin_rpow {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ} (X : (ConfigurationD 2) N) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianRieszDefect2 (c*α) X) (Ioi 0) ∧
    c^(s/2)*(∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianRieszDefect2 (c*α) X) =
      Real.Gamma (s/2)*(energyRpowD s X-sphereRieszConst2 s*(N:ℝ)^2) := by
  set g : ℝ → ℝ := fun t => t^(s/2-1)*sphereGaussianRieszDefect2 t X with hg
  have hcomp : ∀ α : ℝ, 0 < α → g (c*α) =
      c^(s/2-1)*(α^(s/2-1)*sphereGaussianRieszDefect2 (c*α) X) := by
    intro α hα
    simp only [hg]
    rw [Real.mul_rpow hc.le hα.le]
    ring
  have hgi : IntegrableOn g (Ioi 0) := sphereGaussianRieszDefect2_weighted_integrable_rpow hs hs2 X
  have hgc : IntegrableOn (fun α : ℝ => g (c*α)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr
    simpa only [mul_zero] using hgi
  have hcp : 0 < c^(s/2-1) := Real.rpow_pos_of_pos hc _
  constructor
  · have hh : IntegrableOn (fun α : ℝ => (c^(s/2-1))⁻¹*g (c*α)) (Ioi 0) := hgc.const_mul _
    apply hh.congr_fun _ measurableSet_Ioi
    intro α hα
    dsimp only
    rw [hcomp α hα]
    field_simp
  · have h := integral_comp_mul_left_Ioi' g 0 hc
    simp only [mul_zero, smul_eq_mul] at h
    have he : (∫ α : ℝ in Ioi 0, g (c*α)) =
        c^(s/2-1)*∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianRieszDefect2 (c*α) X := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro α hα
      exact hcomp α hα
    rw [he, ← mul_assoc, ← Real.rpow_one_add' hc.le (by linarith), show 1+(s/2-1) = s/2 by ring,
      sphereGaussianRieszDefect2_mellin_rpow hs hs2] at h
    exact h

/-- The normalized ordered Riesz `s`-energy `(E_s - I_s N²)/N^(1+s/2)`. -/
def normalizedEnergyRpow2 (s : ℝ) {N : ℕ} (X : (ConfigurationD 2) N) : ℝ :=
  (energyRpowD s X-sphereRieszConst2 s*(N:ℝ)^2)/(N:ℝ)^(1+s/2)

theorem sphereGaussianCenteredScaled2_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 2) N) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianCenteredScaled2 α X) (Ioi 0) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : IntegrableOn (fun α : ℝ => (N:ℝ)⁻¹*(α^(s/2-1)*
      sphereGaussianRieszDefect2 (sphereGaussianDensityFactor2 N*α) X)) (Ioi 0) :=
    ((sphereGaussianRieszDefect2_scaled_mellin_rpow hs hs2 X
      (sphereGaussianDensityFactor2_pos hN)).1).const_mul (N:ℝ)⁻¹
  apply hi.congr_fun _ measurableSet_Ioi
  intro α _
  change (N:ℝ)⁻¹*(α^(s/2-1)*sphereGaussianRieszDefect2 (sphereGaussianDensityFactor2 N*α) X) =
    α^(s/2-1)*sphereGaussianCenteredScaled2 α X
  rw [← sphereGaussianScale2_eq_factor, sphereGaussianCenteredScaled2_defect hN]
  field_simp

theorem sphereGaussianDensityFactor2_rpow {s : ℝ} {N : ℕ} (hN : 0 < N) :
    (sphereGaussianDensityFactor2 N)^(s/2) =
      Real.pi^(s/2)*((N:ℝ)/(sphereAreaD 2).real univ)^(s/2) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hρ : 0 ≤ (N:ℝ)/(sphereAreaD 2).real univ := (div_pos hNR hA).le
  simp only [sphereGaussianDensityFactor2, sphereGaussianScale2, mul_one]
  rw [Real.mul_rpow Real.pi_pos.le (Real.rpow_nonneg hρ _), ← Real.rpow_mul hρ]
  congr 2
  ring

/-- Density-scale Mellin form of the normalized `s`-energy. -/
theorem normalizedEnergyRpow2_gaussian_mellin {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 2) N) :
    normalizedEnergyRpow2 s X =
      (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled2 α X) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have h := (sphereGaussianRieszDefect2_scaled_mellin_rpow hs hs2 X
    (sphereGaussianDensityFactor2_pos hN)).2
  have he : (fun α : ℝ => α^(s/2-1)*sphereGaussianRieszDefect2 (sphereGaussianDensityFactor2 N*α) X) =
      (fun α : ℝ => (N:ℝ)*(α^(s/2-1)*sphereGaussianCenteredScaled2 α X)) := by
    ext α
    rw [← sphereGaussianScale2_eq_factor, sphereGaussianCenteredScaled2_defect hN]
    ring
  rw [he, integral_const_mul, sphereGaussianDensityFactor2_rpow hN] at h
  set I := ∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled2 α X
  have hdiv : ((N:ℝ)/(sphereAreaD 2).real univ)^(s/2) =
      (N:ℝ)^(s/2)*((sphereAreaD 2).real univ)^(-(s/2)) := by
    rw [Real.div_rpow hNR.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hpow : (N:ℝ)^(1+s/2) = (N:ℝ)*(N:ℝ)^(s/2) := by
    rw [Real.rpow_add' hNR.le (by positivity), Real.rpow_one]
  have hNs : 0 < (N:ℝ)^(s/2) := Real.rpow_pos_of_pos hNR _
  rw [hdiv] at h
  have h2 : energyRpowD s X-sphereRieszConst2 s*(N:ℝ)^2 =
      Real.pi^(s/2)*((N:ℝ)^(s/2)*((sphereAreaD 2).real univ)^(-(s/2)))*((N:ℝ)*I)/Real.Gamma (s/2) := by
    rw [eq_div_iff hΓ.ne']
    linear_combination (-1:ℝ)*h
  have hN0 : (N:ℝ) ≠ 0 := hNR.ne'
  have hNs0 : (N:ℝ)^(s/2) ≠ 0 := hNs.ne'
  unfold normalizedEnergyRpow2
  rw [hpow, h2, div_eq_iff (mul_ne_zero hN0 hNs0)]
  ring

/-! ## The universal lower bound, for `0 < s < 2`

Uniform over configurations, conditional only on Gaussian certificates of the triangular lattice
at all scales.  The coefficient is the Mellin integral of the regularized theta profile. -/

open Filter
open scoped Topology

/-- The weighted Gaussian profile `α^(s/2-1)(Θ(α) - α⁻¹ - 1)` of the triangular lattice. -/
def hexGaussianRieszProfileRpow2 (s α : ℝ) : ℝ :=
  α^(s/2-1)*(hexGaussianThetaReal2 α-α⁻¹-1)

theorem hexGaussianRieszProfileRpow2_eq_re (s : ℝ) {α : ℝ} (hα : 0 < α) :
    hexGaussianRieszProfileRpow2 s α =
      ((α:ℂ)^(((s/2:ℝ):ℂ)-1) • hexThetaRegularized α).re := by
  have hc : (α:ℂ)^(((s/2:ℝ):ℂ)-1) = ((α^(s/2-1):ℝ):ℂ) := by
    rw [Complex.ofReal_cpow hα.le]
    push_cast
    ring_nf
  rw [hc, smul_eq_mul, Complex.re_ofReal_mul]
  have hre : (hexThetaRegularized α).re = hexGaussianThetaReal2 α-α⁻¹-1 := by
    rw [hexThetaRegularized_eq_real hα, Complex.ofReal_re]
  rw [hre]
  rfl

theorem hexGaussianRieszProfileRpow2_integrable {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    IntegrableOn (hexGaussianRieszProfileRpow2 s) (Ioi 0) := by
  have h := hexThetaRegularized_mellinConvergent (s := ((s/2:ℝ):ℂ))
    (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)
  have hre := h.re
  apply hre.congr_fun _ measurableSet_Ioi
  intro α hα
  exact (hexGaussianRieszProfileRpow2_eq_re s hα).symm

/-- The conjectured second-order coefficient for exponent `s`, as a Gaussian profile integral. -/
def sphereRieszCoefficient2 (s : ℝ) : ℝ :=
  (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
    ∫ α : ℝ in Ioi 0, hexGaussianRieszProfileRpow2 s α

theorem sphereGaussianCenteredScaled2_weighted_lower_rpow {N : ℕ} (hN : 0 < N)
    (s : ℝ) {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 2) N) :
    -sphereGaussianMajorant2 s α ≤ α^(s/2-1)*sphereGaussianCenteredScaled2 α X := by
  simpa only [sphereGaussianCenteredScaled2] using
    sphereGaussianCentered2_weighted_common_lower hN s hα X

theorem sphereGaussianCenteredScaled2_weighted_profile_eventually_rpow (s : ℝ)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianRieszProfileRpow2 s α-ε ≤ α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  filter_upwards [hp (ε/α^(s/2-1)) (div_pos hε hw)] with k hk
  have hb : sphereGaussianFullScaled2 α (X k) - α⁻¹ - 1 ≤
      sphereGaussianCenteredScaled2 α (X k) := by
    simpa only [sphereGaussianFullScaled2, sphereGaussianCenteredScaled2] using
      sphereGaussianCentered2_flat_baseline_lower (hN k) hα (X k)
  have he : α^(s/2-1)*(ε/α^(s/2-1)) = ε := mul_div_cancel₀ _ hw.ne'
  unfold hexGaussianRieszProfileRpow2
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_integral_lower_of_profile_rpow2 {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k))
    {C : ℝ}
    (hC : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k)) ≤ C) :
    (∫ α : ℝ in Ioi 0, hexGaussianRieszProfileRpow2 s α) ≤ C :=
  integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := hexGaussianRieszProfileRpow2 s) (M := sphereGaussianMajorant2 s)
    (f := fun k α => α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k))
    (hexGaussianRieszProfileRpow2_integrable hs hs2)
    (fun k => sphereGaussianCenteredScaled2_weighted_integrable_rpow hs hs2 (hN k) (X k))
    (sphereGaussianMajorant2_integrable hs hs2)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianMajorant2_nonneg s hα)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled2_weighted_lower_rpow (hN k) s hα (X k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled2_weighted_profile_eventually_rpow s hN X hα (hp α hα))
    hC

theorem sphereGaussianSequence_energy_bound_of_profile_rpow2 {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k))
    {C : ℝ} (hC : ∀ k, normalizedEnergyRpow2 s (X k) ≤ C) :
    sphereRieszCoefficient2 s ≤ C := by
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have hc : 0 < Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2) := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < ((sphereAreaD 2).real univ)^(-(s/2)) := Real.rpow_pos_of_pos hA _
    positivity
  have hi : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k)) ≤
      C/(Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2)) := by
    intro k
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm, ← normalizedEnergyRpow2_gaussian_mellin hs hs2 (hN k) (X k)]
    exact hC k
  have h := sphereGaussianSequence_integral_lower_of_profile_rpow2 hs hs2 hN X hp hi
  unfold sphereRieszCoefficient2
  have hh := mul_le_mul_of_nonneg_left h hc.le
  rwa [mul_div_cancel₀ C hc.ne'] at hh

/-- Uniform sharp lower bound for every exponent `0 < s < 2`, from the pointwise sharp sphere
Gaussian profile. -/
theorem sphere2_riesz_sharp_lower_of_gaussian_profile_rpow (hp : SphereGaussianSharpProfileLower2)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : (ConfigurationD 2) N, sphereRieszCoefficient2 s-η ≤ normalizedEnergyRpow2 s X := by
  classical
  intro η hη
  by_contra h
  push Not at h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : (ConfigurationD 2) N, normalizedEnergyRpow2 s X < sphereRieszCoefficient2 s-η :=
    fun k => h (k+1)
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  have hc := sphereGaussianSequence_energy_bound_of_profile_rpow2 hs hs2 hN0 X
    (hp N ht hN0 X) (fun k => (hX k).le)
  linarith

/-- The sharp lower bound for every exponent `0 < s < 2` under the all-scale Schwartz input. -/
theorem sphere2_riesz_sharp_lower_of_schwartz_input (hG2 : HexSharpGaussianSchwartzInput2)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : (ConfigurationD 2) N, sphereRieszCoefficient2 s-η ≤ normalizedEnergyRpow2 s X :=
  sphere2_riesz_sharp_lower_of_gaussian_profile_rpow
    (sphereGaussianSharpProfileLower2_of_schwartz_input hG2) hs hs2

/-- Uniform sharp lower bound under Gaussian certificates of the triangular lattice at all
scales. -/
theorem sphere2_riesz_sharp_lower_of_contact
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ConfigurationD 2 N,
        sphereRieszCoefficient2 s-η ≤ normalizedEnergyRpow2 s X :=
  sphere2_riesz_sharp_lower_of_schwartz_input
    (hexSharpGaussianSchwartzInput2_of_contact hG2) hs hs2

/-! ## The measures of `S²` have no atoms -/

open scoped Pointwise

/-- The two coordinates of a vector of `ℝ³` transverse to the polar axis. -/
def transverse2 (v : AmbientD 2) : Fin 2 → ℝ := fun i => v i.succ

theorem transverse2_smul (a : ℝ) (v : AmbientD 2) :
    transverse2 (a • v) = a • transverse2 v := by
  ext i
  simp [transverse2]

theorem transverse2_northPole : transverse2 (northPole2 : AmbientD 2) = 0 := by
  ext i
  simp [transverse2, northPole2]

theorem transverse2_ambientCons3 (p : ℝ × (Fin 2 → ℝ)) :
    transverse2 (ambientCons3 p) = p.2 := by
  ext i
  simp [ambientCons3_apply, transverse2]

theorem transverse2_ae_ne_zero : ∀ᵐ v ∂(volume : Measure (AmbientD 2)), transverse2 v ≠ 0 := by
  have ht : ∀ᵐ u ∂(volume : Measure (Fin 2 → ℝ)), u ≠ 0 := by simp [ae_iff]
  have hp : ∀ᵐ p ∂(volume : Measure (ℝ × (Fin 2 → ℝ))), p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd ((measurableSet_singleton 0).compl))).mpr
    exact Filter.Eventually.of_forall (fun _ => ht)
  rw [← ambientCons3_measurePreserving.map_eq]
  apply ambientCons3.measurableEmbedding.ae_map_iff.mpr
  simpa only [transverse2_ambientCons3] using hp

theorem sphereArea2_northPole_singleton : (sphereAreaD 2) {northPole2} = 0 := by
  have haxis : (volume : Measure (AmbientD 2)) {v | transverse2 v = 0} = 0 := by
    simpa only [not_not] using (ae_iff.mp transverse2_ae_ne_zero)
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' ({northPole2} : Set (SphereD 2))) ⊆
      {v | transverse2 v = 0} := by
    rintro z ⟨r,hr,w,⟨y,hy,rfl⟩,rfl⟩
    rw [mem_singleton_iff] at hy
    subst y
    change transverse2 (r • (northPole2 : (AmbientD 2))) = 0
    rw [transverse2_smul,transverse2_northPole,smul_zero]
  unfold sphereAreaD
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _),
    measure_mono_null hcone haxis,mul_zero]

theorem sphereArea2_singleton (p : (SphereD 2)) : (sphereAreaD 2) {p} = 0 := by
  obtain ⟨g,hg⟩ := sphereRotation2_transitive northPole2 p
  have hpre : (sphereRotationD g) ⁻¹' ({p} : Set (SphereD 2)) = {northPole2} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,← hg,
      (sphereRotationD g).injective.eq_iff]
  have hm := (sphereAreaD_rotation_preserving g).measure_preimage_emb
    (sphereRotationD g).measurableEmbedding ({p} : Set (SphereD 2))
  rw [hpre,sphereArea2_northPole_singleton] at hm
  exact hm.symm

instance sphereArea2_nullSingleton : NullSingletonClass (sphereAreaD 2) :=
  ⟨sphereArea2_singleton⟩

instance sphereProbability2_nullSingleton : NullSingletonClass (sphereProbabilityD 2) := by
  refine ⟨fun p => ?_⟩
  simp [sphereProbabilityD,Measure.smul_apply]

theorem sphereProbability2_finite_null (B : Set (SphereD 2)) (hB : B.Finite) :
    (sphereProbabilityD 2) B = 0 := hB.measure_zero (sphereProbabilityD 2)

/-! ## The Riesz constant is the continuous energy of `S²`

The Mellin-defined constant is the double integral of `|x - y|^(-s)` against the uniform
probability measure of `S²`; Tonelli's theorem removes the null diagonal. -/

open scoped ENNReal

theorem sphereProbability2_prod_diagonal_null :
    ((sphereProbabilityD 2).prod (sphereProbabilityD 2)) {p : (SphereD 2) × (SphereD 2) | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : (SphereD 2) × (SphereD 2) | p.1 = p.2} :=
    (isClosed_diagonal (X := (SphereD 2))).measurableSet
  rw [Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hs : (Prod.mk x ⁻¹' {p : (SphereD 2) × (SphereD 2) | p.1 = p.2}) = {x} := by
    ext y
    simp [eq_comm]
  simp only [Pi.zero_apply]
  rw [hs]
  exact measure_singleton x

theorem sphereRieszPair2_ofReal_mellin {s : ℝ} (hs : 0 < s) {x y : (SphereD 2)} (hxy : x ≠ y) :
    ENNReal.ofReal ((dist x y)^(-s)) = ENNReal.ofReal (Real.Gamma (s/2))⁻¹ *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t^(s/2-1)*Real.exp (-(t*(dist x y)^2))) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have hint : IntegrableOn (fun t : ℝ => t^(s/2-1)*Real.exp (-(t*(dist x y)^2))) (Ioi 0) := by
    have h := gaussianPair_mellin_rpow_integrable hs hd
    apply h.congr_fun _ measurableSet_Ioi
    intro t _
    simp only [mul_comm t]
  have hval : (∫ t : ℝ in Ioi 0, t^(s/2-1)*Real.exp (-(t*(dist x y)^2))) =
      Real.Gamma (s/2)*(dist x y)^(-s) := by
    rw [← gaussianPair_mellin_rpow hs hd]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [mul_comm t]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le), hval,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hΓ.le), ← mul_assoc, inv_mul_cancel₀ hΓ.ne', one_mul]

theorem sphereRieszPair2_lintegral {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∫⁻ p : (SphereD 2) × (SphereD 2), ENNReal.ofReal ((dist p.1 p.2)^(-s))
        ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) =
      ENNReal.ofReal (sphereRieszConst2 s) := by
  set μ := (sphereProbabilityD 2).prod (sphereProbabilityD 2) with hμ
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set F : ℝ → (SphereD 2) × (SphereD 2) → ℝ≥0∞ :=
    fun t p => ENNReal.ofReal (t^(s/2-1)*Real.exp (-(t*(dist p.1 p.2)^2))) with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact measurable_fst.pow_const _
    · apply Real.measurable_exp.comp
      apply Measurable.neg
      apply measurable_fst.mul
      exact (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable.comp
        measurable_snd |>.pow_const 2
  have hae : (fun p : (SphereD 2) × (SphereD 2) => ENNReal.ofReal ((dist p.1 p.2)^(-s))) =ᵐ[μ]
      (fun p => ENNReal.ofReal (Real.Gamma (s/2))⁻¹ * ∫⁻ t in Ioi 0, F t p) := by
    have hnull : μ {p : (SphereD 2) × (SphereD 2) | p.1 = p.2} = 0 := sphereProbability2_prod_diagonal_null
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    exact sphereRieszPair2_ofReal_mellin hs hp
  have hmeas : Measurable (fun p : (SphereD 2) × (SphereD 2) => ∫⁻ t in Ioi 0, F t p) :=
    Measurable.lintegral_prod_left' (μ := volume.restrict (Ioi (0:ℝ))) hFm
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hmeas,
    lintegral_lintegral_swap (f := fun (p : (SphereD 2) × (SphereD 2)) (t : ℝ) => F t p)
      ((hFm.comp measurable_swap).aemeasurable)]
  have hin : ∀ t ∈ Ioi (0:ℝ), ∫⁻ p, F t p ∂μ =
      ENNReal.ofReal (t^(s/2-1)*sphereGaussianBackground2 t) := by
    intro t ht
    have ht0 : 0 ≤ t := (show (0:ℝ) < t from ht).le
    have hi : Integrable (fun p : (SphereD 2) × (SphereD 2) =>
        t^(s/2-1)*Real.exp (-(t*(dist p.1 p.2)^2))) μ :=
      (sphereGaussianKernel2_pair_integrable ht0).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Real.rpow_nonneg ht0 _) (Real.exp_pos _).le)), integral_const_mul]
    rfl
  rw [setLIntegral_congr_fun measurableSet_Ioi hin,
    ← ofReal_integral_eq_lintegral_ofReal
      (sphereGaussianBackground2_weighted_integrable_rpow hs hs2)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
          (sphereGaussianBackground2_nonneg t)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hΓ.le)]
  rfl

theorem sphereRieszPair2_integrable {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    Integrable (fun p : (SphereD 2) × (SphereD 2) => (dist p.1 p.2)^(-s))
      ((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  have hm : Measurable (fun p : (SphereD 2) × (SphereD 2) => (dist p.1 p.2)^(-s)) :=
    (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p =>
      Real.rpow_nonneg dist_nonneg _)),
    sphereRieszPair2_lintegral hs hs2]
  exact ENNReal.ofReal_lt_top

/-- `I_s` is the continuous Riesz `s`-energy of the uniform probability measure of `S²`. -/
theorem sphereRieszConst2_eq_pair_integral {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    sphereRieszConst2 s = ∫ p : (SphereD 2) × (SphereD 2), (dist p.1 p.2)^(-s)
      ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  have hnn : 0 ≤ sphereRieszConst2 s := by
    unfold sphereRieszConst2
    apply mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by positivity)).le)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (sphereGaussianBackground2_nonneg t)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun p =>
      Real.rpow_nonneg dist_nonneg _))
      (sphereRieszPair2_integrable hs hs2).aestronglyMeasurable,
    sphereRieszPair2_lintegral hs hs2, ENNReal.toReal_ofReal hnn]

/-- The all-N lower bound in the original ordered-pair normalization. -/
theorem sphere2_riesz_sharp_lower_conjecture_form
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      sphereRieszCoefficient2 s-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) := by
  intro η hη
  obtain ⟨N₀,h⟩ := sphere2_riesz_sharp_lower_of_contact hG2 hs hs2 η hη
  refine ⟨N₀,fun N hN X => ?_⟩
  have := h N hN X
  rwa [normalizedEnergyRpow2, sphereRieszConst2_eq_pair_integral hs hs2] at this

end SphericalRiesz
end
end

section

/-! # The coefficient of the `S²` Riesz asymptotics as an Epstein zeta value (stage S2-2)

The three sphere-dependent declarations at the end of `LeechEpstein24`, in dimension 2.  The
lattice part (the completed function `hexThetaCompleted`, the continued Epstein zeta function
`hexEpsteinZeta` of the triangular lattice of covolume one in the variable `u = s/2`, and the
Mellin integral of the regularized theta function in the strip `0 < u < 1`) is in
`Riesz.HexLattice2`.

* The integral of the regularized theta profile `α^(s/2-1) (Θ(α) - α⁻¹ - 1)` is the real part of
  the completed value at `s/2`, for `0 < s < 2`.
* The coefficient of the universal lower bound is `C_s = A^(-s/2) ζ_Λ(s)`, with `A = 4π` the area
  of `S²` and `ζ_Λ(s) = hexEpsteinZeta (s/2)` the continued Epstein zeta function, for `0 < s < 2`
  (where the series `Σ |x|^(-s)` diverges).
* The lower bound of the Riesz energy of `S²` with this coefficient, in the ordered-pair
  normalization, under Gaussian certificates of the triangular lattice at all scales.

The lattice part uses the two `backward.isDefEq` options of `LeechEpstein24`; the three statements
here do not need them. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
namespace SphericalRiesz

/-- The profile integral is the real part of the completed value in the strip. -/
theorem hexGaussianRieszProfileRpow2_integral_eq {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    (∫ α : ℝ in Ioi 0, hexGaussianRieszProfileRpow2 s α) =
      (hexThetaCompleted ((s/2:ℝ):ℂ)).re :=
  (hexThetaCompleted_re_eq_integral (u := s/2) (by linarith) (by linarith)).symm

/-- The sharp coefficient of the `S²` Riesz energy is the continued Epstein zeta value of the
triangular lattice, `C_s = A^(-s/2) ζ_Λ(s)` with `A` the area of `S²`, for every `0 < s < 2`. -/
theorem sphereRieszCoefficient2_eq_epstein {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    sphereRieszCoefficient2 s =
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re := by
  have hG : Complex.Gamma ((s/2:ℝ):ℂ) = ((Real.Gamma (s/2) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (s/2)
  have hP : (Real.pi : ℂ)^((s/2:ℝ):ℂ) = ((Real.pi^(s/2) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow Real.pi_pos.le (s/2)).symm
  have hre : (((Real.pi^(s/2) : ℝ) : ℂ)*hexThetaCompleted ((s/2:ℝ):ℂ)/
      ((Real.Gamma (s/2) : ℝ) : ℂ)).re =
      Real.pi^(s/2)/Real.Gamma (s/2)*(hexThetaCompleted ((s/2:ℝ):ℂ)).re := by
    rw [mul_div_right_comm, ← Complex.ofReal_div, Complex.re_ofReal_mul]
  unfold sphereRieszCoefficient2 hexEpsteinZeta
  rw [hexGaussianRieszProfileRpow2_integral_eq hs hs2, hG, hP, hre]
  ring

/-- The sharp lower bound of the `S²` Riesz energy with the Epstein coefficient, in the original
ordered-pair normalization, under Gaussian certificates of the triangular lattice at all
scales. -/
theorem sphere2_riesz_sharp_lower_epstein
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)))*(N:ℝ)^2)/(N:ℝ)^(1+s/2) := by
  rw [← sphereRieszCoefficient2_eq_epstein hs hs2]
  exact sphere2_riesz_sharp_lower_conjecture_form hG2 hs hs2

end SphericalRiesz
end
end
