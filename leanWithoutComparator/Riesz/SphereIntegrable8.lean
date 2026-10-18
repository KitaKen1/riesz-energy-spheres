import Riesz.SphereBall8
import Riesz.CubeLebesgue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
The actual inverse-fourth kernel on the uniform S8 is integrable. We use
the actual ambient-ball direction pushforward and an eight-coordinate
majorant; the exceptional ambient axis has Lebesgue measure zero.
No numerical value of the spherical potential is assumed here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

theorem sphereKernel4_nonneg (p q : Sphere8) : 0 ≤ sphereKernel4 p q := by
  unfold sphereKernel4
  positivity

def northPole8 : Sphere8 :=
  ⟨EuclideanSpace.single (0 : Fin 9) (1 : ℝ), by simp⟩

def transverse8 (v : Ambient9) : Fin 8 → ℝ := fun i => v i.succ

theorem transverse8_measurable : Measurable transverse8 := by
  unfold transverse8
  fun_prop

theorem transverse8_norm_le (v : Ambient9) : ‖transverse8 v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le v i.succ

theorem transverse8_northPole : transverse8 northPole8 = 0 := by
  ext i
  simp [transverse8, northPole8]

theorem transverse8_sub (v w : Ambient9) :
    transverse8 (v-w) = transverse8 v - transverse8 w := rfl

theorem transverse8_smul (a : ℝ) (v : Ambient9) :
    transverse8 (a • v) = a • transverse8 v := rfl

theorem sphereKernel4_transverse_bound (z : Nonzero9) (hz : z ∈ unitBallNonzero9)
    (ht : transverse8 z ≠ 0) :
    sphereKernel4 northPole8 (sphereDirection8 z) ≤ ‖transverse8 z‖⁻¹^4 := by
  have hzn : 0 < ‖(z : Ambient9)‖ := by
    apply norm_pos_iff.mpr
    simpa only [mem_compl_iff, mem_singleton_iff] using z.property
  have htn : 0 < ‖transverse8 z‖ := norm_pos_iff.mpr ht
  have hn : ‖(z : Ambient9)‖ < 1 := hz
  have htDir :
      ‖transverse8 (sphereDirection8 z : Ambient9)‖ =
        ‖(z : Ambient9)‖⁻¹*‖transverse8 z‖ := by
    rw [sphereDirection8_coe, transverse8_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hd : ‖transverse8 (sphereDirection8 z : Ambient9)‖ ≤
      dist northPole8 (sphereDirection8 z) := by
    change ‖transverse8 (sphereDirection8 z : Ambient9)‖ ≤
      dist (northPole8 : Ambient9) (sphereDirection8 z : Ambient9)
    have h := transverse8_norm_le ((sphereDirection8 z : Ambient9) - northPole8)
    rw [transverse8_sub, transverse8_northPole, sub_zero] at h
    simpa only [dist_eq_norm, norm_sub_rev] using h
  have hlow : ‖transverse8 z‖ ≤ dist northPole8 (sphereDirection8 z) := by
    calc
      _ ≤ ‖(z : Ambient9)‖⁻¹*‖transverse8 z‖ := by
        exact le_mul_of_one_le_left htn.le ((one_le_inv₀ hzn).mpr hn.le)
      _ ≤ _ := htDir ▸ hd
  unfold sphereKernel4
  exact pow_le_pow_left₀ (by positivity) (inv_le_inv₀ (lt_of_lt_of_le htn hlow) htn |>.mpr hlow) 4

def ambientCons9 : (ℝ × (Fin 8 → ℝ)) ≃ᵐ Ambient9 :=
  (Boundary.cubeConsEquiv 8).trans (MeasurableEquiv.toLp 2 (Fin 9 → ℝ))

theorem ambientCons9_apply (p : ℝ × (Fin 8 → ℝ)) :
    ambientCons9 p = WithLp.toLp 2 (Fin.cons p.1 p.2) := by
  simp [ambientCons9, Boundary.cubeConsEquiv_apply]

theorem ambientCons9_measurePreserving : MeasurePreserving ambientCons9 volume volume :=
  (PiLp.volume_preserving_toLp (Fin 9)).comp (Boundary.cubeConsEquiv_measurePreserving 8)

theorem transverse8_ambientCons9 (p : ℝ × (Fin 8 → ℝ)) :
    transverse8 (ambientCons9 p) = p.2 := by
  ext i
  simp [ambientCons9_apply, transverse8]

def transverseKernel4 (v : Ambient9) : ℝ := ‖transverse8 v‖⁻¹^4

theorem transverseKernel4_measurable : Measurable transverseKernel4 := by
  unfold transverseKernel4 transverse8
  fun_prop

theorem inverseFourth8_ball_integrable :
    IntegrableOn (fun u : Fin 8 → ℝ => ‖u‖⁻¹^4) (ball 0 2) := by
  have hd : Module.finrank ℝ (Fin 8 → ℝ) = 8 := by simp
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 4)
    (by rw [hd]; norm_num) (by rw [hd]; norm_num)
  · apply Filter.Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul,
      Real.rpow_neg (norm_nonneg u) (4 : ℝ)]
    simp only [Real.rpow_ofNat, inv_pow, le_refl]
  · exact (by fun_prop : Measurable (fun u : Fin 8 → ℝ => ‖u‖⁻¹^4)).aestronglyMeasurable

private def poleBox9 : Set (ℝ × (Fin 8 → ℝ)) := Icc (-1) 1 ×ˢ ball 0 2

private theorem unitBall_subset_poleBox_image :
    ball (0 : Ambient9) 1 ⊆ ambientCons9 '' poleBox9 := by
  intro v hv
  refine ⟨ambientCons9.symm v, ?_, ambientCons9.apply_symm_apply v⟩
  let p := ambientCons9.symm v
  have hn : ‖ambientCons9 p‖ < 1 := by
    simpa only [p, ambientCons9.apply_symm_apply, mem_ball, dist_zero_right] using hv
  have hh : |p.1| ≤ ‖ambientCons9 p‖ := by
    simpa [ambientCons9_apply] using PiLp.norm_apply_le (ambientCons9 p) (0 : Fin 9)
  have ht : ‖p.2‖ ≤ ‖ambientCons9 p‖ := by
    simpa only [transverse8_ambientCons9] using transverse8_norm_le (ambientCons9 p)
  change p.1 ∈ Icc (-1) 1 ∧ p.2 ∈ ball 0 2
  have ha : |p.1| < 1 := lt_of_le_of_lt hh hn
  exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
    by simpa only [mem_ball, dist_zero_right] using (show ‖p.2‖ < 2 by linarith)⟩

theorem transverseKernel4_unitBall_integrable :
    IntegrableOn transverseKernel4 (ball (0 : Ambient9) 1) := by
  have hi : IntegrableOn (fun p : ℝ × (Fin 8 → ℝ) => ‖p.2‖⁻¹^4) poleBox9 := by
    rw [poleBox9, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact inverseFourth8_ball_integrable.comp_snd (volume.restrict (Icc (-1 : ℝ) 1))
  have him : IntegrableOn transverseKernel4 (ambientCons9 '' poleBox9) := by
    apply (ambientCons9_measurePreserving.integrableOn_image ambientCons9.measurableEmbedding).mpr
    simpa only [Function.comp_def, transverseKernel4, transverse8_ambientCons9] using hi
  exact him.mono_set unitBall_subset_poleBox_image

theorem transverse8_ae_ne_zero : ∀ᵐ v ∂(volume : Measure Ambient9), transverse8 v ≠ 0 := by
  have ht : ∀ᵐ u ∂(volume : Measure (Fin 8 → ℝ)), u ≠ 0 := by simp [ae_iff]
  have hp : ∀ᵐ p ∂(volume : Measure (ℝ × (Fin 8 → ℝ))), p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (measurable_snd ((measurableSet_singleton 0).compl))).mpr
    exact Filter.Eventually.of_forall (fun _ => ht)
  rw [← ambientCons9_measurePreserving.map_eq]
  apply ambientCons9.measurableEmbedding.ae_map_iff.mpr
  simpa only [transverse8_ambientCons9] using hp

theorem transverseKernel4_ball_comap_integrable :
    Integrable (fun z : Nonzero9 => transverseKernel4 z)
      (((volume : Measure Ambient9).comap Subtype.val).restrict unitBallNonzero9) := by
  have he : MeasurableEmbedding (Subtype.val : Nonzero9 → Ambient9) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl
  have hi := transverseKernel4_unitBall_integrable.mono_set
    (inter_subset_left (s := ball (0 : Ambient9) 1) (t := Nonzero9))
  have hr : ball (0 : Ambient9) 1 ∩ Nonzero9 ⊆ range (Subtype.val : Nonzero9 → Ambient9) := by
    intro v hv
    exact ⟨⟨v, hv.2⟩, rfl⟩
  have hh := (he.integrableOn_iff_comap hr).mp hi
  have hs : (Subtype.val : Nonzero9 → Ambient9) ⁻¹' (ball 0 1 ∩ Nonzero9) = unitBallNonzero9 := by
    ext z
    simp [unitBallNonzero9]
  simpa only [hs, IntegrableOn, Function.comp_def] using hh

theorem sphereKernel4_northPole_integrable : Integrable (sphereKernel4 northPole8) sphereProbability8 := by
  apply (sphereKernel4_ball_integrable_iff northPole8).mpr
  have ht : ∀ᵐ (z : Nonzero9) ∂(((volume : Measure Ambient9).comap Subtype.val).restrict unitBallNonzero9),
      transverse8 z ≠ 0 := by
    apply ae_restrict_of_ae
    exact (ae_restrict_iff_subtype (measurableSet_singleton (0 : Ambient9)).compl).mp
      (ae_restrict_of_ae transverse8_ae_ne_zero)
  have h : Integrable (fun z => sphereKernel4 northPole8 (sphereDirection8 z))
      (((volume : Measure Ambient9).comap Subtype.val).restrict unitBallNonzero9) := by
    apply transverseKernel4_ball_comap_integrable.mono'
      ((sphereKernel4_measurable northPole8).comp sphereDirection8_measurable).aestronglyMeasurable
    filter_upwards [ht, ae_restrict_mem unitBallNonzero9_measurable] with z hz hzb
    change ‖sphereKernel4 northPole8 (sphereDirection8 z)‖ ≤ transverseKernel4 z
    rw [Real.norm_eq_abs, abs_of_nonneg (sphereKernel4_nonneg northPole8 (sphereDirection8 z))]
    exact sphereKernel4_transverse_bound z hzb hz
  unfold sphereBallProbability8 sphereBallMeasure8
  exact (h.smul_measure (by norm_num : (9 : ENNReal) ≠ ⊤)).smul_measure
    (ENNReal.inv_ne_top.mpr (NeZero.ne (sphereArea8 univ)))

theorem sphereKernel4_integrable (p : Sphere8) : Integrable (sphereKernel4 p) sphereProbability8 :=
  (sphereKernel4_integrable_iff p northPole8).mpr sphereKernel4_northPole_integrable

theorem sphereKernel4_pair_measurable :
    Measurable (fun pq : Sphere8 × Sphere8 => sphereKernel4 pq.1 pq.2) := by
  unfold sphereKernel4
  fun_prop

theorem sphereKernel4_pair_integrable :
    Integrable (fun pq : Sphere8 × Sphere8 => sphereKernel4 pq.1 pq.2)
      (sphereProbability8.prod sphereProbability8) := by
  apply (integrable_prod_iff sphereKernel4_pair_measurable.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall sphereKernel4_integrable, ?_⟩
  have hi : (fun x : Sphere8 => ∫ y, ‖sphereKernel4 x y‖ ∂sphereProbability8) =
      fun _x : Sphere8 => spherePotential4 northPole8 := by
    funext x
    calc
      _ = ∫ y, sphereKernel4 x y ∂sphereProbability8 :=
        integral_congr_ae (Filter.Eventually.of_forall (fun y =>
          Real.norm_of_nonneg (sphereKernel4_nonneg x y)))
      _ = spherePotential4 northPole8 := spherePotential4_constant x northPole8
  rw [hi]
  exact integrable_const _

#print axioms sphereKernel4_nonneg
#print axioms transverse8_norm_le
#print axioms sphereKernel4_transverse_bound
#print axioms ambientCons9_measurePreserving
#print axioms inverseFourth8_ball_integrable
#print axioms transverseKernel4_unitBall_integrable
#print axioms transverse8_ae_ne_zero
#print axioms transverseKernel4_ball_comap_integrable
#print axioms sphereKernel4_northPole_integrable
#print axioms sphereKernel4_integrable
#print axioms sphereKernel4_pair_measurable
#print axioms sphereKernel4_pair_integrable

end SphericalRiesz
