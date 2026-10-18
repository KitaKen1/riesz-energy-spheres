import Riesz.SphereGaussianBackground24
import Riesz.SphereBallD
import Riesz.CubeLebesgue
import Riesz.GaussianMellin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Riesz.FiniteBackground
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Riesz.SphereRieszMellinRpow8
import Riesz.LeechRegularized24
import Riesz.SphereRieszLowerRpow8
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! The actual S²⁴ Gaussian background decay, Riesz Mellin identity and conditional
all-N lower theorem. The chain is grouped here to share one library import during verification.
Each proof stage is delimited below; the all-scale contact premise remains explicit. -/


/-! ## SphereGaussianBall24 -/


/-! The actual S²⁴ Gaussian background as an ambient unit-ball integral. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace
namespace SphericalRiesz

theorem northPole24_dist_sq (q : SphereD 24) :
    dist northPole24 q ^ 2 = 2 - 2 * (q : AmbientD 24) 0 := by
  change ‖(northPole24 : AmbientD 24) - (q : AmbientD 24)‖ ^ 2 = _
  rw [norm_sub_sq_real]
  have hp : ‖(northPole24 : AmbientD 24)‖ = 1 := mem_sphere_zero_iff_norm.mp northPole24.property
  have hq : ‖(q : AmbientD 24)‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  have hi : ⟪(northPole24 : AmbientD 24), (q : AmbientD 24)⟫ = (q : AmbientD 24) 0 := by
    simp [northPole24, EuclideanSpace.inner_single_left]
  rw [hp, hq, hi]
  ring

theorem northPole24_gaussian_coordinate (t : ℝ) (q : (SphereD 24)) :
    sphereGaussianKernel24 t northPole24 q =
      Real.exp (-(t*(2-2*(q:(AmbientD 24)) 0))) := by
  unfold sphereGaussianKernel24
  rw [northPole24_dist_sq]

def ambientPoleGaussian24 (t : ℝ) (v : (AmbientD 24)) : ℝ :=
  Real.exp (-(t*(2-2*v 0/‖v‖)))

theorem ambientPoleGaussian24_measurable (t : ℝ) : Measurable (ambientPoleGaussian24 t) := by
  unfold ambientPoleGaussian24
  fun_prop

theorem northPole24_direction_gaussian (t : ℝ) (z : (NonzeroD 24)) :
    sphereGaussianKernel24 t northPole24 ((sphereDirectionD 24) z) = ambientPoleGaussian24 t z := by
  rw [northPole24_gaussian_coordinate, (sphereDirectionD_coe 24)]
  unfold ambientPoleGaussian24
  simp only [PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv]
  congr 2
  ring

theorem sphereGaussianPotential24_ball_integral (t : ℝ) (p : (SphereD 24)) :
    sphereGaussianPotential24 t p =
      ∫ z, sphereGaussianKernel24 t p ((sphereDirectionD 24) z) ∂(sphereBallProbabilityD 24) := by
  unfold sphereGaussianPotential24
  rw [← (sphereBallProbabilityD_direction_preserving 24).map_eq]
  exact integral_map (sphereDirectionD_measurable 24).aemeasurable (by unfold sphereGaussianKernel24; fun_prop)

theorem gaussian_unitBallNonzero24_preimage :
    (Subtype.val : (NonzeroD 24) → (AmbientD 24)) ⁻¹' ball 0 1 = (unitBallNonzeroD 24) := by
  ext z
  simp [unitBallNonzeroD]

theorem ambientPoleGaussian24_unitBall_integrable {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (ambientPoleGaussian24 t) (ball (0:(AmbientD 24)) 1) := by
  have hi := (sphereBallProbabilityD_direction_preserving 24).integrable_comp
    (by unfold sphereGaussianKernel24; fun_prop : AEStronglyMeasurable
      (sphereGaussianKernel24 t northPole24) (sphereProbabilityD 24))
  have h := hi.mpr (sphereGaussianKernel24_integrable ht northPole24)
  change Integrable (fun z : (NonzeroD 24) => sphereGaussianKernel24 t northPole24 ((sphereDirectionD 24) z))
    (sphereBallProbabilityD 24) at h
  simp_rw [northPole24_direction_gaussian] at h
  unfold sphereBallProbabilityD sphereBallMeasureD at h
  have h' := (integrable_inv_smul_measure (NeZero.ne ((sphereAreaD 24) univ))
    (by finiteness : (sphereAreaD 24) univ ≠ ⊤)).mp h
  rw [show ((24 : ℕ) : ENNReal) + 1 = 25 by norm_num] at h'
  have h'' := (integrable_smul_measure (by norm_num : (25:ENNReal) ≠ 0)
    (by norm_num : (25:ENNReal) ≠ ⊤)).mp h'
  have he : MeasurableEmbedding (Subtype.val : (NonzeroD 24) → (AmbientD 24)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  rw [← gaussian_unitBallNonzero24_preimage, ← he.comap_restrict] at h''
  have hin : IntegrableOn (ambientPoleGaussian24 t) (NonzeroD 24) (volume.restrict (ball 0 1)) := by
    apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:(AmbientD 24))).compl).mpr
    simpa only [Function.comp_def] using h''
  change Integrable (ambientPoleGaussian24 t) ((volume.restrict (ball 0 1)).restrict {0}ᶜ) at hin
  rw [restrict_compl_singleton] at hin
  exact hin

theorem sphereGaussianBackground24_ball {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground24 t =
      ((sphereAreaD 24).real univ)⁻¹*25*∫ v in ball (0:(AmbientD 24)) 1, ambientPoleGaussian24 t v := by
  rw [sphereGaussianBackground24_eq_potential ht northPole24,
    sphereGaussianPotential24_ball_integral]
  simp_rw [northPole24_direction_gaussian]
  unfold sphereBallProbabilityD sphereBallMeasureD
  rw [integral_smul_measure, integral_smul_measure]
  rw [show ((24 : ℕ) : ENNReal) + 1 = 25 by norm_num]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  have he : MeasurableEmbedding (Subtype.val : (NonzeroD 24) → (AmbientD 24)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  have hint : (∫ z : (NonzeroD 24), ambientPoleGaussian24 t z
      ∂((volume:Measure (AmbientD 24)).comap Subtype.val).restrict (unitBallNonzeroD 24)) =
      ∫ v in ball (0:(AmbientD 24)) 1, ambientPoleGaussian24 t v := by
    rw [← gaussian_unitBallNonzero24_preimage, ← he.comap_restrict,
      integral_subtype_comap (measurableSet_singleton (0:(AmbientD 24))).compl (ambientPoleGaussian24 t)]
    change (∫ v, ambientPoleGaussian24 t v ∂(volume.restrict (ball 0 1)).restrict {0}ᶜ) = _
    rw [restrict_compl_singleton]
  rw [hint]
  change ((sphereAreaD 24).real univ)⁻¹*(25*_) = _
  ring

def ambientPoleGaussianBall24 (t : ℝ) : (AmbientD 24) → ℝ :=
  (ball 0 1).indicator (ambientPoleGaussian24 t)

theorem ambientPoleGaussianBall24_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (ambientPoleGaussianBall24 t) :=
  (integrable_indicator_iff measurableSet_ball).mpr (ambientPoleGaussian24_unitBall_integrable ht)

theorem ambientPoleGaussianBall24_integral (t : ℝ) :
    (∫ v, ambientPoleGaussianBall24 t v) = ∫ v in ball (0:(AmbientD 24)) 1, ambientPoleGaussian24 t v :=
  integral_indicator measurableSet_ball

#print axioms northPole24_dist_sq
#print axioms northPole24_gaussian_coordinate
#print axioms ambientPoleGaussian24_measurable
#print axioms northPole24_direction_gaussian
#print axioms sphereGaussianPotential24_ball_integral
#print axioms gaussian_unitBallNonzero24_preimage
#print axioms ambientPoleGaussian24_unitBall_integrable
#print axioms sphereGaussianBackground24_ball
#print axioms ambientPoleGaussianBall24_integrable
#print axioms ambientPoleGaussianBall24_integral

end SphericalRiesz


/-! ## SphereGaussianPolar24 -/


/-! Actual coordinate, radial and polar integration for the S²⁴ Gaussian background. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

abbrev PoleTransverse24 := EuclideanSpace ℝ (Fin 24)

def ambientCons25 : (ℝ × (Fin 24 → ℝ)) ≃ᵐ AmbientD 24 :=
  (Boundary.cubeConsEquiv 24).trans (MeasurableEquiv.toLp 2 (Fin 25 → ℝ))

theorem ambientCons25_apply (p : ℝ × (Fin 24 → ℝ)) :
    ambientCons25 p = WithLp.toLp 2 (Fin.cons p.1 p.2) := by
  simp [ambientCons25, Boundary.cubeConsEquiv_apply]

theorem ambientCons25_measurePreserving : MeasurePreserving ambientCons25 volume volume :=
  (PiLp.volume_preserving_toLp (Fin 25)).comp (Boundary.cubeConsEquiv_measurePreserving 24)

theorem ambientCons25_norm_sq (p : ℝ × (Fin 24 → ℝ)) :
    ‖ambientCons25 p‖ ^ 2 = p.1 ^ 2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse24)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [ambientCons25_apply, Fin.sum_univ_succ]

theorem ambientCons25_norm (p : ℝ × (Fin 24 → ℝ)) :
    ‖ambientCons25 p‖ = Real.sqrt (p.1^2 + ‖(WithLp.toLp 2 p.2 : PoleTransverse24)‖^2) := by
  rw [← ambientCons25_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem poleTransverse24_unit_ball_volume :
    (volume : Measure PoleTransverse24).real (ball 0 1) = Real.pi^12 / 479001600 := by
  have hv : volume (ball (0 : PoleTransverse24) 1) = ENNReal.ofReal (Real.pi^12 / 479001600) := by
    rw [InnerProductSpace.volume_ball_of_dim_even (k := 12) (by simp [PoleTransverse24])]
    norm_num [PoleTransverse24]
  rw [Measure.real, hv, ENNReal.toReal_ofReal]
  positivity

theorem poleRadialPower24_setIntegral :
    (∫ r in Ioo (0 : ℝ) 1, r ^ 24) = 1 / 25 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num

def poleRadialGaussian24 (t a r : ℝ) : ℝ :=
  if a^2+r^2 < 1 then Real.exp (-(t*(2-2*a/Real.sqrt (a^2+r^2)))) else 0

def poleHalfPlaneGaussian24 (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then p.2^23*poleRadialGaussian24 t p.1 p.2 else 0

def poleAngularGaussian24 (t θ : ℝ) : ℝ :=
  Real.sin θ^23 * Real.exp (-(t*(2-2*Real.cos θ)))

def poleRectangleGaussian24 (t : ℝ) : ℝ × ℝ → ℝ :=
  (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi).indicator
    (fun p => p.1^24*poleAngularGaussian24 t p.2)

theorem poleAngularGaussian24_continuous (t : ℝ) : Continuous (poleAngularGaussian24 t) := by
  unfold poleAngularGaussian24
  fun_prop

theorem poleRadialGaussian24_nonneg (t a r : ℝ) : 0 ≤ poleRadialGaussian24 t a r := by
  unfold poleRadialGaussian24
  split_ifs <;> positivity

theorem poleRadialGaussian24_le_one {t : ℝ} (ht : 0 ≤ t) (a r : ℝ) (hr : 0 < r) :
    poleRadialGaussian24 t a r ≤ 1 := by
  have hs : 0 < Real.sqrt (a^2+r^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])
  have ha : a ≤ Real.sqrt (a^2+r^2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
  have hq : a/Real.sqrt (a^2+r^2) ≤ 1 := (div_le_iff₀ hs).mpr (by simpa using ha)
  unfold poleRadialGaussian24
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    apply mul_nonneg ht
    simp only [mul_div_assoc]
    linarith
  · norm_num

theorem poleHalfPlaneGaussian24_nonneg (t : ℝ) (p : ℝ × ℝ) :
    0 ≤ poleHalfPlaneGaussian24 t p := by
  unfold poleHalfPlaneGaussian24
  split_ifs with hr
  · exact mul_nonneg (pow_nonneg hr.le _) (poleRadialGaussian24_nonneg _ _ _)
  · norm_num

theorem poleHalfPlaneGaussian24_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (poleHalfPlaneGaussian24 t) := by
  let s : Set (ℝ × ℝ) := Icc (-1:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hs : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : (volume:Measure (ℝ × ℝ)) s ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi : Integrable (s.indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hfinite)
  have hm : Measurable (poleHalfPlaneGaussian24 t) := by
    unfold poleHalfPlaneGaussian24
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    · apply (measurable_snd.pow_const 23).mul
      unfold poleRadialGaussian24
      exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
        (by fun_prop) measurable_const
    · exact measurable_const
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (poleHalfPlaneGaussian24_nonneg t p)]
  by_cases hr : 0 < p.2
  · by_cases hb : p.1^2+p.2^2 < 1
    · have hr1 : p.2 ≤ 1 := by nlinarith [sq_nonneg p.1]
      have hm : p ∈ s := ⟨⟨by nlinarith [sq_nonneg p.2],
        by nlinarith [sq_nonneg p.2]⟩,⟨hr.le,hr1⟩⟩
      rw [indicator_of_mem hm]
      change poleHalfPlaneGaussian24 t p ≤ 1
      rw [poleHalfPlaneGaussian24, if_pos hr]
      simpa only [one_mul] using mul_le_mul
        (show p.2^23 ≤ (1:ℝ) from pow_le_one₀ hr.le hr1)
        (poleRadialGaussian24_le_one ht p.1 p.2 hr)
        (poleRadialGaussian24_nonneg t p.1 p.2) zero_le_one
    · simp only [poleHalfPlaneGaussian24, if_pos hr, poleRadialGaussian24, if_neg hb, mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) p
  · simp only [poleHalfPlaneGaussian24, if_neg hr]
    exact indicator_nonneg (fun _ _ => zero_le_one) p

theorem ambientPoleGaussianBall24_split (t : ℝ) (p : ℝ × (Fin 24 → ℝ)) :
    ambientPoleGaussianBall24 t (ambientCons25 p) =
      poleRadialGaussian24 t p.1 ‖(WithLp.toLp 2 p.2:PoleTransverse24)‖ := by
  have hi : ‖ambientCons25 p‖ < 1 ↔
      p.1^2+‖(WithLp.toLp 2 p.2:PoleTransverse24)‖^2 < 1 := by
    rw [← ambientCons25_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (ambientCons25 p)]
  have hz : ambientCons25 p 0 = p.1 := by simp [ambientCons25_apply]
  unfold ambientPoleGaussianBall24 ambientPoleGaussian24 poleRadialGaussian24
  simp only [indicator, mem_ball, dist_zero_right, hi]
  rw [hz, ambientCons25_norm]

theorem poleRadialGaussian24_polar (t r θ : ℝ) (hr : 0 < r) :
    poleRadialGaussian24 t (r*Real.cos θ) (r*Real.sin θ) =
      if r < 1 then Real.exp (-(t*(2-2*Real.cos θ))) else 0 := by
  have hs : (r*Real.cos θ)^2+(r*Real.sin θ)^2 = r^2 := by
    calc
      _ = r^2*(Real.cos θ^2+Real.sin θ^2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  have hi : r^2 < 1 ↔ r < 1 := by constructor <;> intro h <;> nlinarith
  unfold poleRadialGaussian24
  simp only [hs, Real.sqrt_sq hr.le, hi]
  have hc : 2*(r*Real.cos θ)/r = 2*Real.cos θ := by field_simp
  rw [hc]

theorem poleHalfPlaneGaussian24_polar (t : ℝ) (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1*poleHalfPlaneGaussian24 t (polarCoord.symm p) = poleRectangleGaussian24 t p := by
  change p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi at hp
  have hr : 0 < p.1 := hp.1
  have htlo : -Real.pi < p.2 := hp.2.1
  have hthi : p.2 < Real.pi := hp.2.2
  change p.1*(if 0 < p.1*Real.sin p.2 then
      (p.1*Real.sin p.2)^23*poleRadialGaussian24 t (p.1*Real.cos p.2) (p.1*Real.sin p.2)
      else 0) = _
  rw [poleRadialGaussian24_polar t p.1 p.2 hr]
  by_cases hθ : 0 < p.2
  · have hpos := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ hthi)
    rw [if_pos hpos]
    by_cases h1 : p.1 < 1
    · have hm : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := ⟨⟨hr,h1⟩,⟨hθ,hthi⟩⟩
      rw [if_pos h1, poleRectangleGaussian24, indicator_of_mem hm]
      unfold poleAngularGaussian24
      ring
    · have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := fun h => h1 h.1.2
      simp [h1, poleRectangleGaussian24, hm]
  · have hs : Real.sin p.2 ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hθ) htlo.le
    have hnon : ¬0 < p.1*Real.sin p.2 :=
      not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le hs)
    have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := fun h => hθ h.2.1
    simp [hnon, poleRectangleGaussian24, hm]

theorem poleRectangleGaussian24_zero_off_target (t : ℝ) (p : ℝ × ℝ)
    (hp : p ∉ polarCoord.target) : poleRectangleGaussian24 t p = 0 := by
  apply indicator_of_notMem
  intro hm
  apply hp
  change p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  exact ⟨hm.1.1,⟨by linarith [hm.2.1,Real.pi_pos],hm.2.2⟩⟩

theorem poleRectangleGaussian24_integral (t : ℝ) :
    (∫ p, poleRectangleGaussian24 t p) =
      (1/25:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian24 t θ := by
  rw [poleRectangleGaussian24, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    show (volume:Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul (fun r : ℝ => r^24) (poleAngularGaussian24 t),
    poleRadialPower24_setIntegral]

theorem poleHalfPlaneGaussian24_integral (t : ℝ) :
    (∫ p, poleHalfPlaneGaussian24 t p) =
      (1/25:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian24 t θ := by
  rw [← integral_comp_polarCoord_symm]
  have h : (∫ p in polarCoord.target, p.1 • poleHalfPlaneGaussian24 t (polarCoord.symm p)) =
      ∫ p in polarCoord.target, poleRectangleGaussian24 t p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    exact poleHalfPlaneGaussian24_polar t p hp
  rw [h, setIntegral_eq_integral_of_forall_compl_eq_zero (poleRectangleGaussian24_zero_off_target t),
    poleRectangleGaussian24_integral]

theorem poleHalfPlaneGaussian24_radial_integral (t a : ℝ) :
    (∫ r in Ioi (0:ℝ), r^23*poleRadialGaussian24 t a r) =
      ∫ r : ℝ, poleHalfPlaneGaussian24 t (a,r) := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1

theorem poleRadialGaussian24_transverse_integral (t a : ℝ) :
    (∫ u : Fin 24 → ℝ, poleRadialGaussian24 t a ‖(WithLp.toLp 2 u:PoleTransverse24)‖) =
      (Real.pi^12/19958400)*∫ r : ℝ, poleHalfPlaneGaussian24 t (a,r) := by
  calc
    _ = ∫ u : PoleTransverse24, poleRadialGaussian24 t a ‖u‖ :=
      (PiLp.volume_preserving_toLp (Fin 24)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 24 → ℝ)).measurableEmbedding _
    _ = _ := by
      rw [integral_fun_norm_addHaar (volume:Measure PoleTransverse24)]
      simp only [PoleTransverse24,finrank_euclideanSpace_fin,Nat.reduceSub,
        smul_eq_mul,poleTransverse24_unit_ball_volume]
      rw [poleHalfPlaneGaussian24_radial_integral]
      ring

theorem ambientPoleGaussianBall24_integral_angular {t : ℝ} (ht : 0 ≤ t) :
    (∫ v : (AmbientD 24), ambientPoleGaussianBall24 t v) =
      (Real.pi^12/498960000)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian24 t θ := by
  have hi : Integrable (ambientPoleGaussianBall24 t ∘ ambientCons25) :=
    ambientCons25_measurePreserving.integrable_comp_of_integrable
      (ambientPoleGaussianBall24_integrable ht)
  calc
    _ = ∫ p : ℝ × (Fin 24 → ℝ), ambientPoleGaussianBall24 t (ambientCons25 p) :=
      (ambientCons25_measurePreserving.integral_comp' (ambientPoleGaussianBall24 t)).symm
    _ = ∫ a : ℝ, ∫ u : Fin 24 → ℝ, ambientPoleGaussianBall24 t (ambientCons25 (a,u)) :=
      integral_prod _ hi
    _ = ∫ a : ℝ, (Real.pi^12/19958400)*∫ r : ℝ, poleHalfPlaneGaussian24 t (a,r) := by
      simp_rw [ambientPoleGaussianBall24_split, poleRadialGaussian24_transverse_integral]
    _ = _ := by
      rw [integral_const_mul, ← integral_prod _ (poleHalfPlaneGaussian24_integrable ht),
        ← Measure.volume_eq_prod, poleHalfPlaneGaussian24_integral]
      ring

theorem sphereGaussianBackground24_angular {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground24 t =
      (2028117/1048576:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian24 t θ := by
  rw [sphereGaussianBackground24_ball ht, ← ambientPoleGaussianBall24_integral,
    ambientPoleGaussianBall24_integral_angular ht, sphereArea24_univ_real]
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

#print axioms ambientCons25_apply
#print axioms ambientCons25_measurePreserving
#print axioms ambientCons25_norm_sq
#print axioms ambientCons25_norm
#print axioms poleTransverse24_unit_ball_volume
#print axioms poleRadialPower24_setIntegral
#print axioms poleAngularGaussian24_continuous
#print axioms poleRadialGaussian24_nonneg
#print axioms poleRadialGaussian24_le_one
#print axioms poleHalfPlaneGaussian24_nonneg
#print axioms poleHalfPlaneGaussian24_integrable
#print axioms ambientPoleGaussianBall24_split
#print axioms poleRadialGaussian24_polar
#print axioms poleHalfPlaneGaussian24_polar
#print axioms poleRectangleGaussian24_zero_off_target
#print axioms poleRectangleGaussian24_integral
#print axioms poleHalfPlaneGaussian24_integral
#print axioms poleHalfPlaneGaussian24_radial_integral
#print axioms poleRadialGaussian24_transverse_integral
#print axioms ambientPoleGaussianBall24_integral_angular
#print axioms sphereGaussianBackground24_angular

end SphericalRiesz


/-! ## SphereGaussianPolynomial24 -/


/-! The actual Gaussian background as a finite exponential-polynomial integral.
The eleventh Gamma moment gives the uniform decay with the exact area normalization. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def polePolynomialGaussian24 (t v : ℝ) : ℝ :=
  Real.exp (-(2*t*v))*v^11*(2-v)^11

theorem polePolynomialGaussian24_continuous (t : ℝ) : Continuous (polePolynomialGaussian24 t) := by
  unfold polePolynomialGaussian24
  fun_prop

theorem poleHeight24_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun u : ℝ => 1-Real.cos u) (Real.sin θ) θ := by
  convert (Real.hasDerivAt_cos θ).neg.const_add 1 using 1 <;> simp

theorem poleAngularGaussian24_polynomial (t θ : ℝ) :
    poleAngularGaussian24 t θ = polePolynomialGaussian24 t (1-Real.cos θ)*Real.sin θ := by
  have hs : Real.sin θ^2 = (1-Real.cos θ)*(1+Real.cos θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs23 : Real.sin θ^23 = Real.sin θ*(Real.sin θ^2)^11 := by ring
  unfold poleAngularGaussian24 polePolynomialGaussian24
  rw [hs23, hs]
  have he : -(t*(2-2*Real.cos θ)) = -(2*t*(1-Real.cos θ)) := by ring
  rw [he]
  ring

theorem poleAngularGaussian24_interval_polynomial (t : ℝ) :
    (∫ θ in (0:ℝ)..Real.pi, poleAngularGaussian24 t θ) =
      ∫ v in (0:ℝ)..2, polePolynomialGaussian24 t v := by
  simp_rw [poleAngularGaussian24_polynomial]
  have h := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := Real.pi)
    (f := fun θ : ℝ => 1-Real.cos θ) (f' := Real.sin) (g := polePolynomialGaussian24 t)
    (fun θ _ => poleHeight24_hasDerivAt θ) Real.continuous_sin.continuousOn
    (polePolynomialGaussian24_continuous t)
  simpa only [Function.comp_def, Real.cos_zero, Real.cos_pi, sub_self,
    sub_neg_eq_add, one_add_one_eq_two] using h

theorem poleAngularGaussian24_set_polynomial (t : ℝ) :
    (∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian24 t θ) =
      ∫ v in (0:ℝ)..2, polePolynomialGaussian24 t v := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact poleAngularGaussian24_interval_polynomial t

theorem sphereGaussianBackground24_polynomial {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground24 t =
      (2028117/1048576:ℝ)*∫ v in (0:ℝ)..2, polePolynomialGaussian24 t v := by
  rw [sphereGaussianBackground24_angular ht, poleAngularGaussian24_set_polynomial]

theorem sphereGaussianBackground24_polynomial_set {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground24 t =
      (2028117/1048576:ℝ)*∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian24 t v := by
  rw [sphereGaussianBackground24_polynomial ht,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2), integral_Ioc_eq_integral_Ioo]

theorem polePolynomialGaussian24_nonneg (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    0 ≤ polePolynomialGaussian24 t v := by
  unfold polePolynomialGaussian24
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv.1 _))
    (pow_nonneg (sub_nonneg.mpr hv.2) _)

theorem polePolynomialGaussian24_le_eleventh (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    polePolynomialGaussian24 t v ≤ 2048*(v^11*Real.exp (-(2*t*v))) := by
  have hp : (2-v)^11 ≤ (2048:ℝ) := by
    have h := pow_le_pow_left₀ (sub_nonneg.mpr hv.2) (show 2-v ≤ (2:ℝ) by linarith [hv.1]) 11
    norm_num at h
    exact h
  unfold polePolynomialGaussian24
  calc
    _ ≤ Real.exp (-(2*t*v))*v^11*2048 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv.1 11))
    _ = _ := by ring

theorem eleventhGaussian24_integral {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ in Ioi 0, v^11*Real.exp (-(2*t*v))) = 155925/(16*t^12) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 12) (r := 2*t) (by norm_num) (by positivity)
  have h' : (∫ v : ℝ in Ioi 0, v^11*Real.exp (-(2*t*v))) = (1/(2*t))^12*39916800 := by
    simpa only [show (12:ℝ)-1 = 11 by norm_num, Real.rpow_ofNat,
      show Real.Gamma 12 = 39916800 by norm_num] using h
  rw [h']
  field_simp
  ring

theorem eleventhGaussian24_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => v^11*Real.exp (-(2*t*v))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [eleventhGaussian24_integral ht]
  exact (by positivity : (0:ℝ) < 155925/(16*t^12)).ne'

theorem sphereGaussianBackground24_decay {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground24 t ≤ (316234143225/8192:ℝ)/t^12 := by
  have hf := eleventhGaussian24_integrable ht
  have hg : IntegrableOn (polePolynomialGaussian24 t) (Ioo (0:ℝ) 2) :=
    (polePolynomialGaussian24_continuous t).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcap : (∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian24 t v) ≤
      ∫ v in Ioo (0:ℝ) 2, 2048*(v^11*Real.exp (-(2*t*v))) :=
    setIntegral_mono_on hg ((hf.mono_set Ioo_subset_Ioi_self).const_mul 2048)
      measurableSet_Ioo (fun v hv => polePolynomialGaussian24_le_eleventh t ⟨hv.1.le,hv.2.le⟩)
  have htail : (∫ v in Ioo (0:ℝ) 2, v^11*Real.exp (-(2*t*v))) ≤
      ∫ v in Ioi (0:ℝ), v^11*Real.exp (-(2*t*v)) := by
    apply setIntegral_mono_set hf
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le
    · exact .of_forall fun v hv => hv.1
  rw [sphereGaussianBackground24_polynomial_set ht.le]
  calc
    _ ≤ (2028117/1048576:ℝ)*∫ v in Ioo (0:ℝ) 2, 2048*(v^11*Real.exp (-(2*t*v))) :=
      mul_le_mul_of_nonneg_left hcap (by norm_num)
    _ = (2028117/1048576:ℝ)*2048*(∫ v in Ioo (0:ℝ) 2, v^11*Real.exp (-(2*t*v))) := by
      rw [integral_const_mul]; ring
    _ ≤ (2028117/1048576:ℝ)*2048*(∫ v in Ioi (0:ℝ), v^11*Real.exp (-(2*t*v))) :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = _ := by rw [eleventhGaussian24_integral ht]; field_simp; ring

theorem sphereGaussianBackground24_min_bound {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground24 t ≤ min 1 ((316234143225/8192:ℝ)/t^12) :=
  le_min (sphereGaussianBackground24_le_one ht.le) (sphereGaussianBackground24_decay ht)

theorem sphereGaussianBackground24_area_decay {t : ℝ} (ht : 0 < t) :
    sphereGaussianBackground24 t ≤ (Real.pi^12/(sphereAreaD 24).real univ)/t^12 := by
  have hC : Real.pi^12/(sphereAreaD 24).real univ = (316234143225/8192:ℝ) := by
    rw [sphereArea24_univ_real]
    have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp <;> norm_num
  rw [hC]
  exact sphereGaussianBackground24_decay ht

#print axioms polePolynomialGaussian24_continuous
#print axioms poleHeight24_hasDerivAt
#print axioms poleAngularGaussian24_polynomial
#print axioms poleAngularGaussian24_interval_polynomial
#print axioms poleAngularGaussian24_set_polynomial
#print axioms sphereGaussianBackground24_polynomial
#print axioms sphereGaussianBackground24_polynomial_set
#print axioms polePolynomialGaussian24_nonneg
#print axioms polePolynomialGaussian24_le_eleventh
#print axioms eleventhGaussian24_integral
#print axioms eleventhGaussian24_integrable
#print axioms sphereGaussianBackground24_decay
#print axioms sphereGaussianBackground24_min_bound
#print axioms sphereGaussianBackground24_area_decay

end SphericalRiesz


/-! ## SphereGaussianCommonLower24 -/


/-! Actual common lower bound for the Gaussian Mellin/Fatou integrand.
Its future integrable majorant still requires the sphere background decay. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SphericalRiesz

theorem sphereGaussianPair24_diagonal_lower {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) :
    (N:ℝ) ≤ ∑ i, ∑ j, sphereGaussianKernel24 t (X i) (X j) := by
  have h := gaussian_diagonal_lower t (fun i : Fin N => (X i:(AmbientD 24)))
  simpa only [kernelPair, one_mul, mul_one, Fintype.card_fin,
    sphereGaussianKernel24_eq_ambient] using h

theorem sphereGaussianPair24_background_lower {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (X : (ConfigurationD 24) N) :
    (N:ℝ)^2*sphereGaussianBackground24 t ≤ ∑ i, ∑ j, sphereGaussianKernel24 t (X i) (X j) := by
  have h := sphereGaussianDefect24_nonneg ht (N:ℝ) X
  rw [sphereGaussianDefect24_charge_N ht] at h
  exact sub_nonneg.mp h

theorem sphereGaussianCentered24_common_lower_of_bound {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 ≤ t) (X : (ConfigurationD 24) N) (C : ℝ)
    (hbackground : (N:ℝ)*sphereGaussianBackground24 t ≤ C) :
    -min 1 C ≤
      (∑ i, ∑ j, sphereGaussianKernel24 t (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground24 t - 1 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hpair := sphereGaussianPair24_background_lower ht X
  have hdiag := sphereGaussianPair24_diagonal_lower t X
  apply background_subtracted_common_lower
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hNR).mpr
    nlinarith [hpair]
  · exact (le_div_iff₀ hNR).mpr (by simpa using hdiag)
  · exact hbackground

theorem sphereGaussianCentered24_common_lower {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t)
    (X : (ConfigurationD 24) N) :
    -min 1 ((N:ℝ)*sphereGaussianBackground24 t) ≤
      (∑ i, ∑ j, sphereGaussianKernel24 t (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground24 t - 1 :=
  sphereGaussianCentered24_common_lower_of_bound hN ht X _ le_rfl

#print axioms sphereGaussianPair24_diagonal_lower
#print axioms sphereGaussianPair24_background_lower
#print axioms sphereGaussianCentered24_common_lower_of_bound
#print axioms sphereGaussianCentered24_common_lower

end SphericalRiesz


/-! ## SphereGaussianMajorant24 -/


/-! A genuine N-independent integrable common lower for every 0<s<24.
The scale and the background are the actual unit-sphere ones. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem sphereGaussianScale24_pos {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    0 < sphereGaussianScale24 N α := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  unfold sphereGaussianScale24
  positivity

theorem sphereGaussianScale24_pow_twelve {N : ℕ} (hN : 0 < N) (α : ℝ) :
    (sphereGaussianScale24 N α)^12 = Real.pi^12*α^12*((N:ℝ)/(sphereAreaD 24).real univ) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hρ : 0 ≤ (N:ℝ)/(sphereAreaD 24).real univ := (div_pos hNR hA).le
  have hp : (((N:ℝ)/(sphereAreaD 24).real univ)^(1/12:ℝ))^12 =
      (N:ℝ)/(sphereAreaD 24).real univ := by
    rw [← Real.rpow_mul_natCast hρ]
    norm_num
  simp only [sphereGaussianScale24, mul_pow, hp]

theorem sphereGaussianBackground24_scaled_cap {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) :
    (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N α) ≤ (α^12)⁻¹ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have h := mul_le_mul_of_nonneg_left
    (sphereGaussianBackground24_area_decay (sphereGaussianScale24_pos hN hα)) hNR.le
  calc
    _ ≤ (N:ℝ)*(Real.pi^12/(sphereAreaD 24).real univ)/(sphereGaussianScale24 N α)^12 := by
      simpa only [mul_div_assoc] using h
    _ = _ := by
      rw [sphereGaussianScale24_pow_twelve hN]
      field_simp [Real.pi_pos.ne',hA.ne',hNR.ne',hα.ne']

theorem sphereGaussianCentered24_scaled_common_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 24) N) :
    -min 1 ((α^12)⁻¹) ≤
      (∑ i, ∑ j, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N α) - 1 :=
  sphereGaussianCentered24_common_lower_of_bound hN (sphereGaussianScale24_pos hN hα).le X _
    (sphereGaussianBackground24_scaled_cap hN hα)

/-- A one-sided background replacement; no background asymptotic is a premise. -/
theorem sphereGaussianCentered24_flat_baseline_lower {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 24) N) :
    (∑ i, ∑ j, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ) -
        (α^12)⁻¹ - 1 ≤
      (∑ i, ∑ j, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N α) - 1 := by
  linarith [sphereGaussianBackground24_scaled_cap hN hα]

def sphereGaussianMajorant24 (s α : ℝ) : ℝ := α^(s/2-1)*min 1 ((α^12)⁻¹)

theorem sphereGaussianMajorant24_small (s : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    sphereGaussianMajorant24 s α = α^(s/2-1) := by
  have hp : (0:ℝ) < α^12 := pow_pos hα _
  have hle : α^12 ≤ 1 := pow_le_one₀ hα.le hα1
  rw [sphereGaussianMajorant24, min_eq_left ((one_le_inv₀ hp).mpr hle), mul_one]

theorem sphereGaussianMajorant24_large (s : ℝ) {α : ℝ} (hα1 : 1 ≤ α) :
    sphereGaussianMajorant24 s α = α^(s/2-13) := by
  have hα : 0 < α := lt_of_lt_of_le zero_lt_one hα1
  have hp : (0:ℝ) < α^12 := pow_pos hα _
  have hle : 1 ≤ α^12 := one_le_pow₀ hα1
  have hpow : α^(s/2-13) = α^(s/2-1)*(α^12)⁻¹ := by
    have he : s/2-13 = (s/2-1)-(12:ℝ) := by ring
    rw [he,Real.rpow_sub hα,Real.rpow_ofNat,div_eq_mul_inv]
  rw [sphereGaussianMajorant24,min_eq_right ((inv_le_one₀ hp).mpr hle),hpow]

theorem sphereGaussianMajorant24_nonneg (s : ℝ) {α : ℝ} (hα : 0 < α) :
    0 ≤ sphereGaussianMajorant24 s α := by
  unfold sphereGaussianMajorant24
  exact mul_nonneg (Real.rpow_nonneg hα.le _) (le_min zero_le_one (by positivity))

theorem sphereGaussianMajorant24_integrable {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    IntegrableOn (sphereGaussianMajorant24 s) (Ioi 0) := by
  have hsmall : IntegrableOn (fun α : ℝ => α^(s/2-1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  have hlarge : IntegrableOn (fun α : ℝ => α^(s/2-13)) (Ioi 1) :=
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
  · rw [sphereGaussianMajorant24_small s hα0 hsmall.le,
      indicator_of_mem (show α ∈ Ioo 0 1 from ⟨hα0,hsmall⟩),
      indicator_of_notMem (show α ∉ Ioi 1 by simpa using hsmall.le)]
    simp
  · rw [sphereGaussianMajorant24_large s hlarge.le,
      indicator_of_notMem (notMem_Ioo_of_ge hlarge.le),
      indicator_of_mem (show α ∈ Ioi 1 from hlarge)]
    simp

theorem sphereGaussianCentered24_weighted_common_lower {N : ℕ} (hN : 0 < N)
    (s : ℝ) {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 24) N) :
    -sphereGaussianMajorant24 s α ≤ α^(s/2-1)*
      ((∑ i, ∑ j, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ) -
        (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N α) - 1) := by
  have h := mul_le_mul_of_nonneg_left (sphereGaussianCentered24_scaled_common_lower hN hα X)
    (Real.rpow_nonneg hα.le (s/2-1))
  simpa only [sphereGaussianMajorant24,mul_neg] using h

#print axioms sphereGaussianScale24_pos
#print axioms sphereGaussianScale24_pow_twelve
#print axioms sphereGaussianBackground24_scaled_cap
#print axioms sphereGaussianCentered24_scaled_common_lower
#print axioms sphereGaussianCentered24_flat_baseline_lower
#print axioms sphereGaussianMajorant24_small
#print axioms sphereGaussianMajorant24_large
#print axioms sphereGaussianMajorant24_nonneg
#print axioms sphereGaussianMajorant24_integrable
#print axioms sphereGaussianCentered24_weighted_common_lower

end SphericalRiesz


/-! ## SphereRieszMellinRpow24 -/


/-! All positive Riesz exponents on the actual unit S²⁴: finite ordered energy,
continuous background, Mellin integrability and exact density-scale normalization.
No singular anchor exponent or supplied background witness is used. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def sphereGaussianOffDiagonal24 {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, sphereGaussianKernel24 t (X i) (X j)

theorem sphereGaussianOffDiagonal24_continuous {N : ℕ} (X : (ConfigurationD 24) N) :
    Continuous (fun t : ℝ => sphereGaussianOffDiagonal24 t X) := by
  unfold sphereGaussianOffDiagonal24 sphereGaussianKernel24
  fun_prop

theorem sphereGaussianOffDiagonal24_nonneg {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) :
    0 ≤ sphereGaussianOffDiagonal24 t X := by
  unfold sphereGaussianOffDiagonal24
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sphereGaussianKernel24_nonneg t (X i) (X j)

theorem sphereGaussianSum24_diagonal {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) :
    (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel24 t (X i) (X j)) =
      sphereGaussianOffDiagonal24 t X+(N:ℝ) := by
  calc
    _ = ∑ i : Fin N, ((∑ j ∈ Finset.univ.erase i,
        sphereGaussianKernel24 t (X i) (X j))+1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := Finset.sum_erase_add (s := Finset.univ) (a := i)
        (fun j : Fin N => sphereGaussianKernel24 t (X i) (X j)) (Finset.mem_univ i)
      simpa only [sphereGaussianKernel24_self] using h.symm
    _ = _ := by simp [sphereGaussianOffDiagonal24, Finset.sum_add_distrib]

theorem sphereGaussianOffDiagonal24_eq_full_sub {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianOffDiagonal24 t X =
      (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel24 t (X i) (X j))-(N:ℝ) := by
  linarith [sphereGaussianSum24_diagonal t X]

def sphereGaussianRieszDefect24 {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) : ℝ :=
  sphereGaussianOffDiagonal24 t X-(N:ℝ)^2*sphereGaussianBackground24 t

theorem sphereGaussianRieszDefect24_eq_full {N : ℕ} (t : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianRieszDefect24 t X =
      (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel24 t (X i) (X j))-(N:ℝ)-
        (N:ℝ)^2*sphereGaussianBackground24 t := by
  rw [sphereGaussianRieszDefect24,sphereGaussianOffDiagonal24_eq_full_sub]

def sphereGaussianDensityFactor24 (N : ℕ) : ℝ := sphereGaussianScale24 N 1

theorem sphereGaussianDensityFactor24_pos {N : ℕ} (hN : 0 < N) :
    0 < sphereGaussianDensityFactor24 N :=
  sphereGaussianScale24_pos hN zero_lt_one

theorem sphereGaussianScale24_eq_factor (N : ℕ) (α : ℝ) :
    sphereGaussianScale24 N α = sphereGaussianDensityFactor24 N*α := by
  unfold sphereGaussianDensityFactor24 sphereGaussianScale24
  ring

def sphereGaussianCenteredScaled24 {N : ℕ} (α : ℝ) (X : (ConfigurationD 24) N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ)-
    (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N α)-1

theorem sphereGaussianCenteredScaled24_defect {N : ℕ} (hN : 0 < N)
    (α : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianRieszDefect24 (sphereGaussianScale24 N α) X =
      (N:ℝ)*sphereGaussianCenteredScaled24 α X := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sphereGaussianRieszDefect24_eq_full]
  unfold sphereGaussianCenteredScaled24
  field_simp [hNR] <;> ring

theorem sphereGaussianPair24_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 24) N) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianKernel24 t (X i) (X j)) (Ioi 0) := by
  have h := gaussianPair_mellin_rpow_integrable hs (offDiagonal_dist_posD X hij)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [sphereGaussianKernel24, mul_comm t]

theorem sphereGaussianPair24_mellin_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 24) N) {i j : Fin N} (hij : i ≠ j) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianKernel24 t (X i) (X j)) =
      Real.Gamma (s/2)*(dist (X i) (X j))^(-s) := by
  rw [← gaussianPair_mellin_rpow hs (offDiagonal_dist_posD X hij)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [sphereGaussianKernel24, mul_comm t]

theorem sphereGaussianOffDiagonal24_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 24) N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianOffDiagonal24 t X) (Ioi 0) := by
  unfold sphereGaussianOffDiagonal24
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact sphereGaussianPair24_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianOffDiagonal24_mellin_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : (ConfigurationD 24) N) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianOffDiagonal24 t X) =
      Real.Gamma (s/2)*energyRpowD s X := by
  have hi (i : Fin N) : IntegrableOn
      (fun t : ℝ => ∑ j ∈ Finset.univ.erase i, t^(s/2-1)*sphereGaussianKernel24 t (X i) (X j))
      (Ioi 0) :=
    integrable_finsetSum _ (fun j hj =>
      sphereGaussianPair24_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm)
  unfold sphereGaussianOffDiagonal24 energyRpowD
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj =>
    sphereGaussianPair24_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm)]
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereGaussianPair24_mellin_rpow hs X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianBackground24_continuousOn : ContinuousOn sphereGaussianBackground24 (Ici 0) := by
  have hc : Continuous (fun t : ℝ => (2028117/1048576:ℝ)*∫ v in Icc (0:ℝ) 2, polePolynomialGaussian24 t v) := by
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    unfold polePolynomialGaussian24
    fun_prop
  apply hc.continuousOn.congr
  intro t ht
  dsimp only
  rw [sphereGaussianBackground24_polynomial_set ht, integral_Icc_eq_integral_Ioo]

theorem sphereGaussianBackground24_weighted_le_majorant {s t : ℝ} (ht : 0 < t) :
    |t^(s/2-1)*sphereGaussianBackground24 t| ≤ (316234143225/8192:ℝ)*sphereGaussianMajorant24 s t := by
  have hB0 := sphereGaussianBackground24_nonneg t
  have hB := sphereGaussianBackground24_min_bound ht
  have hp : 0 ≤ t^(s/2-1) := Real.rpow_nonneg ht.le _
  rw [abs_of_nonneg (mul_nonneg hp hB0), sphereGaussianMajorant24]
  have hmin : min 1 ((316234143225/8192:ℝ)/t^12) ≤ (316234143225/8192:ℝ)*min 1 ((t^12)⁻¹) := by
    rcases le_total 1 ((t^12)⁻¹) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by norm_num)
    · rw [min_eq_right h, div_eq_mul_inv]
      exact min_le_right _ _
  calc t^(s/2-1)*sphereGaussianBackground24 t ≤ t^(s/2-1)*((316234143225/8192:ℝ)*min 1 ((t^12)⁻¹)) :=
        mul_le_mul_of_nonneg_left (hB.trans hmin) hp
    _ = _ := by ring

theorem sphereGaussianBackground24_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianBackground24 t) (Ioi 0) := by
  have hmaj := (sphereGaussianMajorant24_integrable hs hs24).const_mul (316234143225/8192:ℝ)
  refine hmaj.mono' ?_ ?_
  · have hm : ContinuousOn (fun t : ℝ => t^(s/2-1)*sphereGaussianBackground24 t) (Ioi 0) := by
      apply ContinuousOn.mul
      · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
      · exact sphereGaussianBackground24_continuousOn.mono Ioi_subset_Ici_self
    exact hm.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact sphereGaussianBackground24_weighted_le_majorant ht

/-- The continuous Riesz `s`-energy constant of the actual uniform S²⁴, defined by the Gaussian
Mellin integral of the actual sphere Gaussian background. -/
def sphereRieszConst24 (s : ℝ) : ℝ :=
  (Real.Gamma (s/2))⁻¹ * ∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianBackground24 t

theorem sphereGaussianRieszDefect24_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ} (X : (ConfigurationD 24) N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianRieszDefect24 t X) (Ioi 0) := by
  have hi := (sphereGaussianOffDiagonal24_weighted_integrable_rpow hs X).sub
    ((sphereGaussianBackground24_weighted_integrable_rpow hs hs24).const_mul ((N:ℝ)^2))
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  change t^(s/2-1)*sphereGaussianOffDiagonal24 t X-(N:ℝ)^2*(t^(s/2-1)*sphereGaussianBackground24 t) =
    t^(s/2-1)*(sphereGaussianOffDiagonal24 t X-(N:ℝ)^2*sphereGaussianBackground24 t)
  ring

theorem sphereGaussianRieszDefect24_mellin_rpow {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ} (X : (ConfigurationD 24) N) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianRieszDefect24 t X) =
      Real.Gamma (s/2)*(energyRpowD s X-sphereRieszConst24 s*(N:ℝ)^2) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have he : (fun t : ℝ => t^(s/2-1)*sphereGaussianRieszDefect24 t X) =
      (fun t : ℝ => t^(s/2-1)*sphereGaussianOffDiagonal24 t X-
        (N:ℝ)^2*(t^(s/2-1)*sphereGaussianBackground24 t)) := by
    ext t
    unfold sphereGaussianRieszDefect24
    ring
  rw [he, integral_sub (sphereGaussianOffDiagonal24_weighted_integrable_rpow hs X)
      ((sphereGaussianBackground24_weighted_integrable_rpow hs hs24).const_mul ((N:ℝ)^2)),
    integral_const_mul, sphereGaussianOffDiagonal24_mellin_rpow hs]
  unfold sphereRieszConst24
  field_simp

theorem sphereGaussianRieszDefect24_scaled_mellin_rpow {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ} (X : (ConfigurationD 24) N) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianRieszDefect24 (c*α) X) (Ioi 0) ∧
    c^(s/2)*(∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianRieszDefect24 (c*α) X) =
      Real.Gamma (s/2)*(energyRpowD s X-sphereRieszConst24 s*(N:ℝ)^2) := by
  set g : ℝ → ℝ := fun t => t^(s/2-1)*sphereGaussianRieszDefect24 t X with hg
  have hcomp : ∀ α : ℝ, 0 < α → g (c*α) =
      c^(s/2-1)*(α^(s/2-1)*sphereGaussianRieszDefect24 (c*α) X) := by
    intro α hα
    simp only [hg]
    rw [Real.mul_rpow hc.le hα.le]
    ring
  have hgi : IntegrableOn g (Ioi 0) := sphereGaussianRieszDefect24_weighted_integrable_rpow hs hs24 X
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
        c^(s/2-1)*∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianRieszDefect24 (c*α) X := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro α hα
      exact hcomp α hα
    rw [he, ← mul_assoc, ← Real.rpow_one_add' hc.le (by linarith), show 1+(s/2-1) = s/2 by ring,
      sphereGaussianRieszDefect24_mellin_rpow hs hs24] at h
    exact h

/-- The normalized ordered Riesz `s`-energy `(E_s - I_s N²)/N^(1+s/24)`. -/
def normalizedEnergyRpow24 (s : ℝ) {N : ℕ} (X : (ConfigurationD 24) N) : ℝ :=
  (energyRpowD s X-sphereRieszConst24 s*(N:ℝ)^2)/(N:ℝ)^(1+s/24)

theorem sphereGaussianCenteredScaled24_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 24) N) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianCenteredScaled24 α X) (Ioi 0) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : IntegrableOn (fun α : ℝ => (N:ℝ)⁻¹*(α^(s/2-1)*
      sphereGaussianRieszDefect24 (sphereGaussianDensityFactor24 N*α) X)) (Ioi 0) :=
    ((sphereGaussianRieszDefect24_scaled_mellin_rpow hs hs24 X
      (sphereGaussianDensityFactor24_pos hN)).1).const_mul (N:ℝ)⁻¹
  apply hi.congr_fun _ measurableSet_Ioi
  intro α _
  change (N:ℝ)⁻¹*(α^(s/2-1)*sphereGaussianRieszDefect24 (sphereGaussianDensityFactor24 N*α) X) =
    α^(s/2-1)*sphereGaussianCenteredScaled24 α X
  rw [← sphereGaussianScale24_eq_factor, sphereGaussianCenteredScaled24_defect hN]
  field_simp

theorem sphereGaussianDensityFactor24_rpow {s : ℝ} {N : ℕ} (hN : 0 < N) :
    (sphereGaussianDensityFactor24 N)^(s/2) =
      Real.pi^(s/2)*((N:ℝ)/(sphereAreaD 24).real univ)^(s/24) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hρ : 0 ≤ (N:ℝ)/(sphereAreaD 24).real univ := (div_pos hNR hA).le
  simp only [sphereGaussianDensityFactor24, sphereGaussianScale24, mul_one]
  rw [Real.mul_rpow Real.pi_pos.le (Real.rpow_nonneg hρ _), ← Real.rpow_mul hρ]
  congr 2
  ring

/-- Density-scale Mellin form of the normalized `s`-energy. -/
theorem normalizedEnergyRpow24_gaussian_mellin {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 24) N) :
    normalizedEnergyRpow24 s X =
      (Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled24 α X) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have h := (sphereGaussianRieszDefect24_scaled_mellin_rpow hs hs24 X
    (sphereGaussianDensityFactor24_pos hN)).2
  have he : (fun α : ℝ => α^(s/2-1)*sphereGaussianRieszDefect24 (sphereGaussianDensityFactor24 N*α) X) =
      (fun α : ℝ => (N:ℝ)*(α^(s/2-1)*sphereGaussianCenteredScaled24 α X)) := by
    ext α
    rw [← sphereGaussianScale24_eq_factor, sphereGaussianCenteredScaled24_defect hN]
    ring
  rw [he, integral_const_mul, sphereGaussianDensityFactor24_rpow hN] at h
  set I := ∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled24 α X
  have hdiv : ((N:ℝ)/(sphereAreaD 24).real univ)^(s/24) =
      (N:ℝ)^(s/24)*((sphereAreaD 24).real univ)^(-(s/24)) := by
    rw [Real.div_rpow hNR.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hpow : (N:ℝ)^(1+s/24) = (N:ℝ)*(N:ℝ)^(s/24) := by
    rw [Real.rpow_add' hNR.le (by positivity), Real.rpow_one]
  have hNs : 0 < (N:ℝ)^(s/24) := Real.rpow_pos_of_pos hNR _
  rw [hdiv] at h
  have h2 : energyRpowD s X-sphereRieszConst24 s*(N:ℝ)^2 =
      Real.pi^(s/2)*((N:ℝ)^(s/24)*((sphereAreaD 24).real univ)^(-(s/24)))*((N:ℝ)*I)/Real.Gamma (s/2) := by
    rw [eq_div_iff hΓ.ne']
    linear_combination (-1:ℝ)*h
  have hN0 : (N:ℝ) ≠ 0 := hNR.ne'
  have hNs0 : (N:ℝ)^(s/24) ≠ 0 := hNs.ne'
  have hΓ0 : Real.Gamma (s/2) ≠ 0 := hΓ.ne'
  unfold normalizedEnergyRpow24
  rw [hpow, h2]
  field_simp


#print axioms sphereGaussianOffDiagonal24_continuous
#print axioms sphereGaussianOffDiagonal24_nonneg
#print axioms sphereGaussianSum24_diagonal
#print axioms sphereGaussianOffDiagonal24_eq_full_sub
#print axioms sphereGaussianRieszDefect24_eq_full
#print axioms sphereGaussianDensityFactor24_pos
#print axioms sphereGaussianScale24_eq_factor
#print axioms sphereGaussianCenteredScaled24_defect
#print axioms sphereGaussianPair24_weighted_integrable_rpow
#print axioms sphereGaussianPair24_mellin_rpow
#print axioms sphereGaussianOffDiagonal24_weighted_integrable_rpow
#print axioms sphereGaussianOffDiagonal24_mellin_rpow
#print axioms sphereGaussianBackground24_continuousOn
#print axioms sphereGaussianBackground24_weighted_le_majorant
#print axioms sphereGaussianBackground24_weighted_integrable_rpow
#print axioms sphereGaussianRieszDefect24_weighted_integrable_rpow
#print axioms sphereGaussianRieszDefect24_mellin_rpow
#print axioms sphereGaussianRieszDefect24_scaled_mellin_rpow
#print axioms sphereGaussianCenteredScaled24_weighted_integrable_rpow
#print axioms sphereGaussianDensityFactor24_rpow
#print axioms normalizedEnergyRpow24_gaussian_mellin

end SphericalRiesz


/-! ## SphereRieszLowerRpow24 -/


/-! Uniform all-N sharp Riesz lower bounds on the actual S²⁴ for every 0<s<24,
conditional only on the all-scale Leech Gaussian contact certificates.
The coefficient is the actual regularized theta Mellin integral. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The weighted Leech Gaussian profile `α^(s/2-1)(Θ(α) - α⁻¹² - 1)`. -/
def leechGaussianRieszProfileRpow24 (s α : ℝ) : ℝ :=
  α^(s/2-1)*(leechGaussianThetaReal24 α-(α^12)⁻¹-1)

theorem leechGaussianRieszProfileRpow24_eq_re (s : ℝ) {α : ℝ} (hα : 0 < α) :
    leechGaussianRieszProfileRpow24 s α =
      ((α:ℂ)^(((s/2:ℝ):ℂ)-1) • leechThetaRegularized α).re := by
  have hc : (α:ℂ)^(((s/2:ℝ):ℂ)-1) = ((α^(s/2-1):ℝ):ℂ) := by
    rw [Complex.ofReal_cpow hα.le]
    push_cast
    ring_nf
  rw [hc, smul_eq_mul, Complex.re_ofReal_mul]
  have hre : (leechThetaRegularized α).re = leechGaussianThetaReal24 α-(α^12)⁻¹-1 := by
    rw [leechThetaRegularized, leechThetaTail, leechThetaImag_eq_real hα]
    simp only [Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow,
      ← Complex.ofReal_inv, Complex.ofReal_re]
    ring
  rw [hre]
  rfl

theorem leechGaussianRieszProfileRpow24_integrable {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    IntegrableOn (leechGaussianRieszProfileRpow24 s) (Ioi 0) := by
  have h := leechThetaRegularized_mellinConvergent (s := ((s/2:ℝ):ℂ))
    (by simp; linarith) (by simp; linarith)
  have hre := h.re
  apply hre.congr_fun _ measurableSet_Ioi
  intro α hα
  exact (leechGaussianRieszProfileRpow24_eq_re s hα).symm

/-- The conjectured second-order coefficient for exponent `s`, as a Gaussian profile integral. -/
def sphereRieszCoefficient24 (s : ℝ) : ℝ :=
  (Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2))*
    ∫ α : ℝ in Ioi 0, leechGaussianRieszProfileRpow24 s α

theorem sphereGaussianCenteredScaled24_weighted_lower_rpow {N : ℕ} (hN : 0 < N)
    (s : ℝ) {α : ℝ} (hα : 0 < α) (X : (ConfigurationD 24) N) :
    -sphereGaussianMajorant24 s α ≤ α^(s/2-1)*sphereGaussianCenteredScaled24 α X := by
  simpa only [sphereGaussianCenteredScaled24] using
    sphereGaussianCentered24_weighted_common_lower hN s hα X

theorem sphereGaussianCenteredScaled24_weighted_profile_eventually_rpow (s : ℝ)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianThetaReal24 α-ε ≤ sphereGaussianFullScaled24 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianRieszProfileRpow24 s α-ε ≤ α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  filter_upwards [hp (ε/α^(s/2-1)) (div_pos hε hw)] with k hk
  have hb : sphereGaussianFullScaled24 α (X k) - (α^12)⁻¹ - 1 ≤
      sphereGaussianCenteredScaled24 α (X k) := by
    simpa only [sphereGaussianFullScaled24, sphereGaussianCenteredScaled24] using
      sphereGaussianCentered24_flat_baseline_lower (hN k) hα (X k)
  have he : α^(s/2-1)*(ε/α^(s/2-1)) = ε := mul_div_cancel₀ _ hw.ne'
  unfold leechGaussianRieszProfileRpow24
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_integral_lower_of_profile_rpow24 {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianThetaReal24 α-ε ≤ sphereGaussianFullScaled24 α (X k))
    {C : ℝ}
    (hC : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k)) ≤ C) :
    (∫ α : ℝ in Ioi 0, leechGaussianRieszProfileRpow24 s α) ≤ C :=
  integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := leechGaussianRieszProfileRpow24 s) (M := sphereGaussianMajorant24 s)
    (f := fun k α => α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k))
    (leechGaussianRieszProfileRpow24_integrable hs hs24)
    (fun k => sphereGaussianCenteredScaled24_weighted_integrable_rpow hs hs24 (hN k) (X k))
    (sphereGaussianMajorant24_integrable hs hs24)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianMajorant24_nonneg s hα)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled24_weighted_lower_rpow (hN k) s hα (X k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled24_weighted_profile_eventually_rpow s hN X hα (hp α hα))
    hC

theorem sphereGaussianSequence_energy_bound_of_profile_rpow24 {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianThetaReal24 α-ε ≤ sphereGaussianFullScaled24 α (X k))
    {C : ℝ} (hC : ∀ k, normalizedEnergyRpow24 s (X k) ≤ C) :
    sphereRieszCoefficient24 s ≤ C := by
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have hc : 0 < Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2) := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < ((sphereAreaD 24).real univ)^(-(s/24)) := Real.rpow_pos_of_pos hA _
    positivity
  have hi : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k)) ≤
      C/(Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2)) := by
    intro k
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm, ← normalizedEnergyRpow24_gaussian_mellin hs hs24 (hN k) (X k)]
    exact hC k
  have h := sphereGaussianSequence_integral_lower_of_profile_rpow24 hs hs24 hN X hp hi
  unfold sphereRieszCoefficient24
  have hh := mul_le_mul_of_nonneg_left h hc.le
  rwa [mul_div_cancel₀ C hc.ne'] at hh

/-- Uniform sharp lower bound for every exponent `0 < s < 24`, from the pointwise sharp sphere
Gaussian profile. -/
theorem sphere24_riesz_sharp_lower_of_gaussian_profile_rpow (hp : SphereGaussianSharpProfileLower24)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : (ConfigurationD 24) N, sphereRieszCoefficient24 s-η ≤ normalizedEnergyRpow24 s X := by
  classical
  intro η hη
  by_contra h
  push_neg at h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : (ConfigurationD 24) N, normalizedEnergyRpow24 s X < sphereRieszCoefficient24 s-η :=
    fun k => h (k+1)
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  have hc := sphereGaussianSequence_energy_bound_of_profile_rpow24 hs hs24 hN0 X
    (hp N ht hN0 X) (fun k => (hX k).le)
  linarith

/-- The all-exponent sharp lower bound under the G24 input. -/
theorem sphere24_riesz_sharp_lower_of_schwartz_input (hG24 : LeechSharpGaussianSchwartzInput24)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : (ConfigurationD 24) N, sphereRieszCoefficient24 s-η ≤ normalizedEnergyRpow24 s X :=
  sphere24_riesz_sharp_lower_of_gaussian_profile_rpow
    (sphereGaussianSharpProfileLower24_of_schwartz_input hG24) hs hs24


/-- Uniform sharp lower bound under all-scale Leech contact certificates. -/
theorem sphere24_riesz_sharp_lower_of_contact
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ConfigurationD 24 N,
        sphereRieszCoefficient24 s-η ≤ normalizedEnergyRpow24 s X :=
  sphere24_riesz_sharp_lower_of_schwartz_input
    (leechSharpGaussianSchwartzInput24_of_contact hG24) hs hs24

#print axioms leechGaussianRieszProfileRpow24_eq_re
#print axioms leechGaussianRieszProfileRpow24_integrable
#print axioms sphereGaussianCenteredScaled24_weighted_lower_rpow
#print axioms sphereGaussianCenteredScaled24_weighted_profile_eventually_rpow
#print axioms sphereGaussianSequence_integral_lower_of_profile_rpow24
#print axioms sphereGaussianSequence_energy_bound_of_profile_rpow24
#print axioms sphere24_riesz_sharp_lower_of_gaussian_profile_rpow
#print axioms sphere24_riesz_sharp_lower_of_schwartz_input
#print axioms sphere24_riesz_sharp_lower_of_contact

end SphericalRiesz


/-! ## SphereAtomless24 -/


/-! The actual area and probability measures on S²⁴ have no atoms. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace SphericalRiesz

def transverse24 (v : AmbientD 24) : Fin 24 → ℝ := fun i => v i.succ

theorem transverse24_smul (a : ℝ) (v : AmbientD 24) :
    transverse24 (a • v) = a • transverse24 v := by
  ext i
  simp [transverse24]

theorem transverse24_northPole : transverse24 (northPole24 : AmbientD 24) = 0 := by
  ext i
  simp [transverse24, northPole24, EuclideanSpace.single_apply]

theorem transverse24_ambientCons25 (p : ℝ × (Fin 24 → ℝ)) :
    transverse24 (ambientCons25 p) = p.2 := by
  ext i
  simp [ambientCons25_apply, transverse24]

theorem transverse24_ae_ne_zero : ∀ᵐ v ∂(volume : Measure (AmbientD 24)), transverse24 v ≠ 0 := by
  have ht : ∀ᵐ u ∂(volume : Measure (Fin 24 → ℝ)), u ≠ 0 := by simp [ae_iff]
  have hp : ∀ᵐ p ∂(volume : Measure (ℝ × (Fin 24 → ℝ))), p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd ((measurableSet_singleton 0).compl))).mpr
    exact Filter.Eventually.of_forall (fun _ => ht)
  rw [← ambientCons25_measurePreserving.map_eq]
  apply ambientCons25.measurableEmbedding.ae_map_iff.mpr
  simpa only [transverse24_ambientCons25] using hp

theorem sphereArea24_northPole_singleton : (sphereAreaD 24) {northPole24} = 0 := by
  have haxis : (volume : Measure (AmbientD 24)) {v | transverse24 v = 0} = 0 := by
    simpa only [not_not] using (ae_iff.mp transverse24_ae_ne_zero)
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' ({northPole24} : Set (SphereD 24))) ⊆
      {v | transverse24 v = 0} := by
    rintro z ⟨r,hr,w,⟨y,hy,rfl⟩,rfl⟩
    rw [mem_singleton_iff] at hy
    subst y
    change transverse24 (r • (northPole24 : (AmbientD 24))) = 0
    rw [transverse24_smul,transverse24_northPole,smul_zero]
  unfold sphereAreaD
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _),
    measure_mono_null hcone haxis,mul_zero]

theorem sphereArea24_singleton (p : (SphereD 24)) : (sphereAreaD 24) {p} = 0 := by
  obtain ⟨g,hg⟩ := sphereRotation24_transitive northPole24 p
  have hpre : (sphereRotationD g) ⁻¹' ({p} : Set (SphereD 24)) = {northPole24} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,← hg,
      (sphereRotationD g).injective.eq_iff]
  have hm := (sphereAreaD_rotation_preserving g).measure_preimage_emb
    (sphereRotationD g).measurableEmbedding ({p} : Set (SphereD 24))
  rw [hpre,sphereArea24_northPole_singleton] at hm
  exact hm.symm

instance sphereArea24_nullSingleton : NullSingletonClass (sphereAreaD 24) :=
  ⟨sphereArea24_singleton⟩

instance sphereProbability24_nullSingleton : NullSingletonClass (sphereProbabilityD 24) := by
  refine ⟨fun p => ?_⟩
  simp [sphereProbabilityD,Measure.smul_apply]

theorem sphereProbability24_finite_null (B : Set (SphereD 24)) (hB : B.Finite) :
    (sphereProbabilityD 24) B = 0 := hB.measure_zero (sphereProbabilityD 24)

#print axioms transverse24_smul
#print axioms transverse24_northPole
#print axioms transverse24_ambientCons25
#print axioms transverse24_ae_ne_zero
#print axioms sphereArea24_northPole_singleton
#print axioms sphereArea24_singleton
#print axioms sphereProbability24_finite_null

end SphericalRiesz


/-! ## SphereRieszConstPair24 -/


/-! Identification of the Mellin-defined continuous Riesz constant with the
actual double sphere-probability integral on S²⁴. Tonelli removes the null diagonal. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SphericalRiesz

theorem sphereProbability24_prod_diagonal_null :
    ((sphereProbabilityD 24).prod (sphereProbabilityD 24)) {p : (SphereD 24) × (SphereD 24) | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : (SphereD 24) × (SphereD 24) | p.1 = p.2} :=
    (isClosed_diagonal (X := (SphereD 24))).measurableSet
  rw [Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hs : (Prod.mk x ⁻¹' {p : (SphereD 24) × (SphereD 24) | p.1 = p.2}) = {x} := by
    ext y
    simp [eq_comm]
  simp only [Pi.zero_apply]
  rw [hs]
  exact measure_singleton x

theorem sphereRieszPair24_ofReal_mellin {s : ℝ} (hs : 0 < s) {x y : (SphereD 24)} (hxy : x ≠ y) :
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

theorem sphereRieszPair24_lintegral {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∫⁻ p : (SphereD 24) × (SphereD 24), ENNReal.ofReal ((dist p.1 p.2)^(-s))
        ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)) =
      ENNReal.ofReal (sphereRieszConst24 s) := by
  set μ := (sphereProbabilityD 24).prod (sphereProbabilityD 24) with hμ
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set F : ℝ → (SphereD 24) × (SphereD 24) → ℝ≥0∞ :=
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
  have hae : (fun p : (SphereD 24) × (SphereD 24) => ENNReal.ofReal ((dist p.1 p.2)^(-s))) =ᵐ[μ]
      (fun p => ENNReal.ofReal (Real.Gamma (s/2))⁻¹ * ∫⁻ t in Ioi 0, F t p) := by
    have hnull : μ {p : (SphereD 24) × (SphereD 24) | p.1 = p.2} = 0 := sphereProbability24_prod_diagonal_null
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    exact sphereRieszPair24_ofReal_mellin hs hp
  have hmeas : Measurable (fun p : (SphereD 24) × (SphereD 24) => ∫⁻ t in Ioi 0, F t p) :=
    Measurable.lintegral_prod_left' (μ := volume.restrict (Ioi (0:ℝ))) hFm
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hmeas,
    lintegral_lintegral_swap (f := fun (p : (SphereD 24) × (SphereD 24)) (t : ℝ) => F t p)
      ((hFm.comp measurable_swap).aemeasurable)]
  have hin : ∀ t ∈ Ioi (0:ℝ), ∫⁻ p, F t p ∂μ =
      ENNReal.ofReal (t^(s/2-1)*sphereGaussianBackground24 t) := by
    intro t ht
    have ht0 : 0 ≤ t := (show (0:ℝ) < t from ht).le
    have hi : Integrable (fun p : (SphereD 24) × (SphereD 24) =>
        t^(s/2-1)*Real.exp (-(t*(dist p.1 p.2)^2))) μ :=
      (sphereGaussianKernel24_pair_integrable ht0).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Real.rpow_nonneg ht0 _) (Real.exp_pos _).le)), integral_const_mul]
    rfl
  rw [setLIntegral_congr_fun measurableSet_Ioi hin,
    ← ofReal_integral_eq_lintegral_ofReal
      (sphereGaussianBackground24_weighted_integrable_rpow hs hs24)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
          (sphereGaussianBackground24_nonneg t)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hΓ.le)]
  rfl

theorem sphereRieszPair24_integrable {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    Integrable (fun p : (SphereD 24) × (SphereD 24) => (dist p.1 p.2)^(-s))
      ((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  have hm : Measurable (fun p : (SphereD 24) × (SphereD 24) => (dist p.1 p.2)^(-s)) :=
    (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p =>
      Real.rpow_nonneg dist_nonneg _)),
    sphereRieszPair24_lintegral hs hs24]
  exact ENNReal.ofReal_lt_top

/-- `I_s` is the actual continuous Riesz `s`-energy of the uniform probability on S²⁴. -/
theorem sphereRieszConst24_eq_pair_integral {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    sphereRieszConst24 s = ∫ p : (SphereD 24) × (SphereD 24), (dist p.1 p.2)^(-s)
      ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  have hnn : 0 ≤ sphereRieszConst24 s := by
    unfold sphereRieszConst24
    apply mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by positivity)).le)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (sphereGaussianBackground24_nonneg t)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun p =>
      Real.rpow_nonneg dist_nonneg _))
      (sphereRieszPair24_integrable hs hs24).aestronglyMeasurable,
    sphereRieszPair24_lintegral hs hs24, ENNReal.toReal_ofReal hnn]

/-- The all-N lower bound in the original ordered-pair normalization. -/
theorem sphere24_riesz_sharp_lower_conjecture_form
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      sphereRieszCoefficient24 s-η ≤
        (energyRpowD s X-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) := by
  intro η hη
  obtain ⟨N₀,h⟩ := sphere24_riesz_sharp_lower_of_contact hG24 hs hs24 η hη
  refine ⟨N₀,fun N hN X => ?_⟩
  have := h N hN X
  rwa [normalizedEnergyRpow24, sphereRieszConst24_eq_pair_integral hs hs24] at this

#print axioms sphereProbability24_prod_diagonal_null
#print axioms sphereRieszPair24_ofReal_mellin
#print axioms sphereRieszPair24_lintegral
#print axioms sphereRieszPair24_integrable
#print axioms sphereRieszConst24_eq_pair_integral
#print axioms sphere24_riesz_sharp_lower_conjecture_form

end SphericalRiesz

