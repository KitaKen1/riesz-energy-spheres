import Riesz.SphereGaussianBall8
import Riesz.SphereValue8

/-! Actual radial and polar changes for the Gaussian background on unit S8.
The half-plane integrability proof uses a bounded compact rectangle. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

def poleRadialGaussian8 (t a r : ℝ) : ℝ :=
  if a^2+r^2 < 1 then Real.exp (-(t*(2-2*a/Real.sqrt (a^2+r^2)))) else 0

def poleHalfPlaneGaussian8 (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then p.2^7*poleRadialGaussian8 t p.1 p.2 else 0

def poleAngularGaussian8 (t θ : ℝ) : ℝ :=
  Real.sin θ^7 * Real.exp (-(t*(2-2*Real.cos θ)))

def poleRectangleGaussian8 (t : ℝ) : ℝ × ℝ → ℝ :=
  (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi).indicator
    (fun p => p.1^8*poleAngularGaussian8 t p.2)

theorem poleAngularGaussian8_continuous (t : ℝ) : Continuous (poleAngularGaussian8 t) := by
  unfold poleAngularGaussian8
  fun_prop

theorem poleRadialGaussian8_nonneg (t a r : ℝ) : 0 ≤ poleRadialGaussian8 t a r := by
  unfold poleRadialGaussian8
  split_ifs <;> positivity

theorem poleRadialGaussian8_le_one {t : ℝ} (ht : 0 ≤ t) (a r : ℝ) (hr : 0 < r) :
    poleRadialGaussian8 t a r ≤ 1 := by
  have hs : 0 < Real.sqrt (a^2+r^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])
  have ha : a ≤ Real.sqrt (a^2+r^2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
  have hq : a/Real.sqrt (a^2+r^2) ≤ 1 := (div_le_iff₀ hs).mpr (by simpa using ha)
  unfold poleRadialGaussian8
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    apply mul_nonneg ht
    simp only [mul_div_assoc]
    linarith
  · norm_num

theorem poleHalfPlaneGaussian8_nonneg (t : ℝ) (p : ℝ × ℝ) :
    0 ≤ poleHalfPlaneGaussian8 t p := by
  unfold poleHalfPlaneGaussian8
  split_ifs with hr
  · exact mul_nonneg (pow_nonneg hr.le _) (poleRadialGaussian8_nonneg _ _ _)
  · norm_num

theorem poleHalfPlaneGaussian8_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (poleHalfPlaneGaussian8 t) := by
  let s : Set (ℝ × ℝ) := Icc (-1:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hs : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : (volume:Measure (ℝ × ℝ)) s ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi : Integrable (s.indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hfinite)
  have hm : Measurable (poleHalfPlaneGaussian8 t) := by
    unfold poleHalfPlaneGaussian8
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    · apply (measurable_snd.pow_const 7).mul
      unfold poleRadialGaussian8
      exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
        (by fun_prop) measurable_const
    · exact measurable_const
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (poleHalfPlaneGaussian8_nonneg t p)]
  by_cases hr : 0 < p.2
  · by_cases hb : p.1^2+p.2^2 < 1
    · have hr1 : p.2 ≤ 1 := by nlinarith [sq_nonneg p.1]
      have hm : p ∈ s := ⟨⟨by nlinarith [sq_nonneg p.2],
        by nlinarith [sq_nonneg p.2]⟩,⟨hr.le,hr1⟩⟩
      rw [indicator_of_mem hm]
      change poleHalfPlaneGaussian8 t p ≤ 1
      rw [poleHalfPlaneGaussian8, if_pos hr]
      simpa only [one_mul] using mul_le_mul
        (show p.2^7 ≤ (1:ℝ) from pow_le_one₀ hr.le hr1)
        (poleRadialGaussian8_le_one ht p.1 p.2 hr)
        (poleRadialGaussian8_nonneg t p.1 p.2) zero_le_one
    · simp only [poleHalfPlaneGaussian8, if_pos hr, poleRadialGaussian8, if_neg hb, mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) p
  · simp only [poleHalfPlaneGaussian8, if_neg hr]
    exact indicator_nonneg (fun _ _ => zero_le_one) p

theorem ambientPoleGaussianBall8_split (t : ℝ) (p : ℝ × (Fin 8 → ℝ)) :
    ambientPoleGaussianBall8 t (ambientCons9 p) =
      poleRadialGaussian8 t p.1 ‖(WithLp.toLp 2 p.2:PoleTransverse8)‖ := by
  have hi : ‖ambientCons9 p‖ < 1 ↔
      p.1^2+‖(WithLp.toLp 2 p.2:PoleTransverse8)‖^2 < 1 := by
    rw [← ambientCons9_norm_sq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (ambientCons9 p)]
  have hz : ambientCons9 p 0 = p.1 := by simp [ambientCons9_apply]
  unfold ambientPoleGaussianBall8 ambientPoleGaussian8 poleRadialGaussian8
  simp only [indicator, mem_ball, dist_zero_right, hi]
  rw [hz, ambientCons9_norm]

theorem poleRadialGaussian8_polar (t r θ : ℝ) (hr : 0 < r) :
    poleRadialGaussian8 t (r*Real.cos θ) (r*Real.sin θ) =
      if r < 1 then Real.exp (-(t*(2-2*Real.cos θ))) else 0 := by
  have hs : (r*Real.cos θ)^2+(r*Real.sin θ)^2 = r^2 := by
    calc
      _ = r^2*(Real.cos θ^2+Real.sin θ^2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  have hi : r^2 < 1 ↔ r < 1 := by constructor <;> intro h <;> nlinarith
  unfold poleRadialGaussian8
  simp only [hs, Real.sqrt_sq hr.le, hi]
  have hc : 2*(r*Real.cos θ)/r = 2*Real.cos θ := by field_simp
  rw [hc]

theorem poleHalfPlaneGaussian8_polar (t : ℝ) (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1*poleHalfPlaneGaussian8 t (polarCoord.symm p) = poleRectangleGaussian8 t p := by
  change p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi at hp
  have hr : 0 < p.1 := hp.1
  have htlo : -Real.pi < p.2 := hp.2.1
  have hthi : p.2 < Real.pi := hp.2.2
  change p.1*(if 0 < p.1*Real.sin p.2 then
      (p.1*Real.sin p.2)^7*poleRadialGaussian8 t (p.1*Real.cos p.2) (p.1*Real.sin p.2)
      else 0) = _
  rw [poleRadialGaussian8_polar t p.1 p.2 hr]
  by_cases hθ : 0 < p.2
  · have hpos := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ hthi)
    rw [if_pos hpos]
    by_cases h1 : p.1 < 1
    · have hm : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := ⟨⟨hr,h1⟩,⟨hθ,hthi⟩⟩
      rw [if_pos h1, poleRectangleGaussian8, indicator_of_mem hm]
      unfold poleAngularGaussian8
      ring
    · have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := fun h => h1 h.1.2
      simp [h1, poleRectangleGaussian8, hm]
  · have hs : Real.sin p.2 ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hθ) htlo.le
    have hnon : ¬0 < p.1*Real.sin p.2 :=
      not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le hs)
    have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) Real.pi := fun h => hθ h.2.1
    simp [hnon, poleRectangleGaussian8, hm]

theorem poleRectangleGaussian8_zero_off_target (t : ℝ) (p : ℝ × ℝ)
    (hp : p ∉ polarCoord.target) : poleRectangleGaussian8 t p = 0 := by
  apply indicator_of_notMem
  intro hm
  apply hp
  change p ∈ Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  exact ⟨hm.1.1,⟨by linarith [hm.2.1,Real.pi_pos],hm.2.2⟩⟩

theorem poleRectangleGaussian8_integral (t : ℝ) :
    (∫ p, poleRectangleGaussian8 t p) =
      (1/9:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian8 t θ := by
  rw [poleRectangleGaussian8, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    show (volume:Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul (fun r : ℝ => r^8) (poleAngularGaussian8 t),
    poleRadialPower8_setIntegral]

theorem poleHalfPlaneGaussian8_integral (t : ℝ) :
    (∫ p, poleHalfPlaneGaussian8 t p) =
      (1/9:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian8 t θ := by
  rw [← integral_comp_polarCoord_symm]
  have h : (∫ p in polarCoord.target, p.1 • poleHalfPlaneGaussian8 t (polarCoord.symm p)) =
      ∫ p in polarCoord.target, poleRectangleGaussian8 t p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    exact poleHalfPlaneGaussian8_polar t p hp
  rw [h, setIntegral_eq_integral_of_forall_compl_eq_zero (poleRectangleGaussian8_zero_off_target t),
    poleRectangleGaussian8_integral]

theorem poleHalfPlaneGaussian8_radial_integral (t a : ℝ) :
    (∫ r in Ioi (0:ℝ), r^7*poleRadialGaussian8 t a r) =
      ∫ r : ℝ, poleHalfPlaneGaussian8 t (a,r) := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1

theorem poleRadialGaussian8_transverse_integral (t a : ℝ) :
    (∫ u : Fin 8 → ℝ, poleRadialGaussian8 t a ‖(WithLp.toLp 2 u:PoleTransverse8)‖) =
      (Real.pi^4/3)*∫ r : ℝ, poleHalfPlaneGaussian8 t (a,r) := by
  calc
    _ = ∫ u : PoleTransverse8, poleRadialGaussian8 t a ‖u‖ :=
      (PiLp.volume_preserving_toLp (Fin 8)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)).measurableEmbedding _
    _ = _ := by
      rw [integral_fun_norm_addHaar (volume:Measure PoleTransverse8)]
      simp only [PoleTransverse8,finrank_euclideanSpace_fin,Nat.reduceSub,
        smul_eq_mul,poleTransverse8_unit_ball_volume]
      rw [poleHalfPlaneGaussian8_radial_integral]
      ring

theorem ambientPoleGaussianBall8_integral_angular {t : ℝ} (ht : 0 ≤ t) :
    (∫ v : Ambient9, ambientPoleGaussianBall8 t v) =
      (Real.pi^4/27)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian8 t θ := by
  have hi : Integrable (ambientPoleGaussianBall8 t ∘ ambientCons9) :=
    ambientCons9_measurePreserving.integrable_comp_of_integrable
      (ambientPoleGaussianBall8_integrable ht)
  calc
    _ = ∫ p : ℝ × (Fin 8 → ℝ), ambientPoleGaussianBall8 t (ambientCons9 p) :=
      (ambientCons9_measurePreserving.integral_comp' (ambientPoleGaussianBall8 t)).symm
    _ = ∫ a : ℝ, ∫ u : Fin 8 → ℝ, ambientPoleGaussianBall8 t (ambientCons9 (a,u)) :=
      integral_prod _ hi
    _ = ∫ a : ℝ, (Real.pi^4/3)*∫ r : ℝ, poleHalfPlaneGaussian8 t (a,r) := by
      simp_rw [ambientPoleGaussianBall8_split, poleRadialGaussian8_transverse_integral]
    _ = _ := by
      rw [integral_const_mul, ← integral_prod _ (poleHalfPlaneGaussian8_integrable ht),
        ← Measure.volume_eq_prod, poleHalfPlaneGaussian8_integral]
      ring

theorem sphereGaussianBackground8_angular {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground8 t =
      (35/32:ℝ)*∫ θ in Ioo (0:ℝ) Real.pi, poleAngularGaussian8 t θ := by
  rw [sphereGaussianBackground8_ball ht, ← ambientPoleGaussianBall8_integral,
    ambientPoleGaussianBall8_integral_angular ht, sphereArea8_mass_real]
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

end SphericalRiesz
