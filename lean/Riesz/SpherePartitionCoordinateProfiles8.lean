import Riesz.SphereCutoffPartition8
import Riesz.EqualAreaEuclideanTransport8

/-!
Actual compact Euclidean coordinate profiles of the normalized finite
Sphere8 cutoffs, and exact weighted transport of the original probability
integral. A coordinate inverse on the opposite hemisphere can fold back
into the chart: profile(u_i(x))=eta_i(x) is asserted only on the relevant
hemisphere. The globally valid identity retains the outer cutoff factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

theorem rotatedSphereChartCutoff8_apply (ρ : ℝ) (hρ : 0 < ρ)
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) :
    rotatedSphereChartCutoff8 ρ hρ g (sphereRotation8 g x) = sphereChartCutoff8 ρ hρ x := by
  unfold rotatedSphereChartCutoff8
  rw [show sphereRotation8 g.symm (sphereRotation8 g x) = x from (sphereRotation8 g).left_inv x]

theorem rotatedSphereEqualAreaCoordinates8_apply (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) :
    rotatedSphereEqualAreaCoordinates8 g (sphereRotation8 g x) = sphereEqualAreaCoordinates8 x := by
  unfold rotatedSphereEqualAreaCoordinates8
  rw [show sphereRotation8 g.symm (sphereRotation8 g x) = x from (sphereRotation8 g).left_inv x]

def sphereFiniteCutoffProfile8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K)
    (u : EuclideanSpace ℝ (Fin 8)) : ℝ := by
  classical
  exact if hu : u ∈ equalAreaEuclideanDomain8 then
    sphereFiniteCutoffWeight8 ρ hρ g i
      (sphereRotation8 (g i) (equalAreaEuclideanSphereChart8 ⟨u,hu⟩)) else 0

theorem sphereFiniteCutoffProfile8_chart {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) (u : equalAreaEuclideanDomain8) :
    sphereFiniteCutoffProfile8 ρ hρ g i (u : EuclideanSpace ℝ (Fin 8)) =
      sphereFiniteCutoffWeight8 ρ hρ g i (sphereRotation8 (g i) (equalAreaEuclideanSphereChart8 u)) := by
  rw [sphereFiniteCutoffProfile8, dite_eq_left u.property]

theorem sphereFiniteCutoffProfile8_zero_off_domain {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) (u : EuclideanSpace ℝ (Fin 8))
    (hu : u ∉ equalAreaEuclideanDomain8) : sphereFiniteCutoffProfile8 ρ hρ g i u = 0 := by
  rw [sphereFiniteCutoffProfile8, dite_eq_right hu]

theorem sphereFiniteCutoffProfile8_nonneg {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) (u : EuclideanSpace ℝ (Fin 8)) :
    0 ≤ sphereFiniteCutoffProfile8 ρ hρ g i u := by
  unfold sphereFiniteCutoffProfile8
  split_ifs
  · exact sphereFiniteCutoffWeight8_nonneg ρ hρ g i _
  · exact le_rfl

theorem sphereFiniteCutoffProfile8_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (i : Fin K) (u : EuclideanSpace ℝ (Fin 8)) : sphereFiniteCutoffProfile8 ρ hρ g i u ≤ 1 := by
  unfold sphereFiniteCutoffProfile8
  split_ifs
  · exact sphereFiniteCutoffWeight8_le_one ρ hρ g hpos i _
  · exact zero_le_one

theorem sphereFiniteCutoffProfile8_zero_of_norm {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) (u : EuclideanSpace ℝ (Fin 8))
    (hu : ρ ≤ ‖u‖) : sphereFiniteCutoffProfile8 ρ hρ g i u = 0 := by
  by_cases hd : u ∈ equalAreaEuclideanDomain8
  · rw [sphereFiniteCutoffProfile8, dite_eq_left hd]
    simp only [sphereFiniteCutoffWeight8, finiteCutoffSquarePartition,
      rotatedSphereChartCutoff8_apply, sphereChartCutoff8_chart,
      coordinateCutoff_zero_of_norm ρ hρ u hu, zero_div]
  · exact sphereFiniteCutoffProfile8_zero_off_domain ρ hρ g i u hd

theorem sphereFiniteCutoffProfile8_compactSupport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) :
    HasCompactSupport (sphereFiniteCutoffProfile8 ρ hρ g i) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 8)) ρ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  have hn : ‖u‖ < ρ := by
    by_contra h
    exact hu (sphereFiniteCutoffProfile8_zero_of_norm ρ hρ g i u (not_lt.mp h))
  simpa only [mem_closedBall, dist_zero_right] using hn.le

theorem sphereFiniteCutoffProfile8_continuous {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) :
    Continuous (sphereFiniteCutoffProfile8 ρ hρ g i) := by
  have hD : ContinuousOn (sphereFiniteCutoffProfile8 ρ hρ g i) equalAreaEuclideanDomain8 := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : equalAreaEuclideanDomain8.domRestrict (sphereFiniteCutoffProfile8 ρ hρ g i) =
        fun u => sphereFiniteCutoffWeight8 ρ hρ g i
          (sphereRotation8 (g i) (equalAreaEuclideanSphereChart8 u)) := by
      funext u
      exact sphereFiniteCutoffProfile8_chart ρ hρ g i u
    rw [he]
    exact (sphereFiniteCutoffWeight8_continuous ρ hρ g hc hpos i).comp
      ((sphereRotation8 (g i)).continuous.comp equalAreaEuclideanSphereChart8_continuous)
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u ∈ equalAreaEuclideanDomain8
  · exact hD.continuousAt (equalAreaEuclideanDomain8_isOpen.mem_nhds hu)
  · have hn : ρ < ‖u‖ := by
      by_contra h
      exact hu (equalAreaEuclidean8_small_norm_domain u ((not_lt.mp h).trans hr))
    have he : ∀ᶠ v : EuclideanSpace ℝ (Fin 8) in 𝓝 u, ρ < ‖v‖ :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn
    apply (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℝ (Fin 8) => (0 : ℝ)) u).congr_of_eventuallyEq
    filter_upwards [he] with v hv
    exact sphereFiniteCutoffProfile8_zero_of_norm ρ hρ g i v hv.le

theorem sphereFiniteCutoffWeight8_rotated_zero_off_hemisphere {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) (x : Sphere8)
    (hx : x ∉ equalAreaHemisphere8) :
    sphereFiniteCutoffWeight8 ρ hρ g i (sphereRotation8 (g i) x) = 0 := by
  by_contra hn
  have h := (sphereFiniteCutoffWeight8_ne_zero_iff ρ hρ g hpos i _).mp hn
  rw [rotatedSphereChartCutoff8_apply] at h
  have hx' : ¬ 0 < (x : Ambient9) 0 := hx
  exact h (by simp only [sphereChartCutoff8, hx', ite_false])

theorem sphereFiniteCutoffProfile8_coordinates_on_hemisphere {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (i : Fin K) (x : Sphere8)
    (hx : sphereRotation8 (g i).symm x ∈ equalAreaHemisphere8) :
    sphereFiniteCutoffProfile8 ρ hρ g i (rotatedSphereEqualAreaCoordinates8 (g i) x) =
      sphereFiniteCutoffWeight8 ρ hρ g i x := by
  have hd : sphereEqualAreaCoordinates8 (sphereRotation8 (g i).symm x) ∈ equalAreaEuclideanDomain8 := by
    simpa only [equalAreaEuclideanDomain8, mem_preimage, sphereEqualAreaCoordinates8,
      WithLp.ofLp_toLp] using equalAreaInverse8_mem_domain _ hx
  have hchart : equalAreaEuclideanSphereChart8
      ⟨sphereEqualAreaCoordinates8 (sphereRotation8 (g i).symm x),hd⟩ =
      sphereRotation8 (g i).symm x := by
    apply Subtype.ext
    exact equalAreaPhiEuclidean8_inverse _ hx
  rw [rotatedSphereEqualAreaCoordinates8, sphereFiniteCutoffProfile8, dite_eq_left hd, hchart]
  rw [show sphereRotation8 (g i) (sphereRotation8 (g i).symm x) = x from
    (sphereRotation8 (g i)).right_inv x]

theorem sphereFiniteCutoffWeight8_times_profile_eq_square {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) (x : Sphere8) :
    sphereFiniteCutoffWeight8 ρ hρ g i x*
      sphereFiniteCutoffProfile8 ρ hρ g i (rotatedSphereEqualAreaCoordinates8 (g i) x) =
      (sphereFiniteCutoffWeight8 ρ hρ g i x)^2 := by
  by_cases hx : sphereFiniteCutoffWeight8 ρ hρ g i x = 0
  · rw [hx, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · have hr := (sphereFiniteCutoffWeight8_ne_zero_iff ρ hρ g hpos i x).mp hx
    change sphereRotation8 (g i).symm x ∈ Function.support (sphereChartCutoff8 ρ hρ) at hr
    rw [sphereChartCutoff8_support] at hr
    rw [sphereFiniteCutoffProfile8_coordinates_on_hemisphere ρ hρ g i x hr.1, pow_two]

theorem sphereFiniteCutoffWeight8_probability_integral {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K)
    (F : EuclideanSpace ℝ (Fin 8) → ℝ) :
    (∫ x, sphereFiniteCutoffWeight8 ρ hρ g i x*F (rotatedSphereEqualAreaCoordinates8 (g i) x)
      ∂sphereProbability8) = (sphereArea8.real univ)⁻¹ *
      ∫ u, sphereFiniteCutoffProfile8 ρ hρ g i u*F u := by
  rw [← sphereProbability8_integral_rotation (g i)
    (fun x => sphereFiniteCutoffWeight8 ρ hρ g i x*F (rotatedSphereEqualAreaCoordinates8 (g i) x))]
  simp_rw [rotatedSphereEqualAreaCoordinates8_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := equalAreaHemisphere8)
    (fun x hx => by rw [sphereFiniteCutoffWeight8_rotated_zero_off_hemisphere ρ hρ g hpos i x hx,
      zero_mul]), equalAreaEuclideanSphereChart8_probability_integral]
  simp_rw [equalAreaEuclideanSphereChart8_coordinates, ← sphereFiniteCutoffProfile8_chart]
  congr 1
  calc
    _ = ∫ u in equalAreaEuclideanDomain8, sphereFiniteCutoffProfile8 ρ hρ g i u*F u :=
      integral_subtype_comap equalAreaEuclideanDomain8_measurable
        (fun u => sphereFiniteCutoffProfile8 ρ hρ g i u*F u)
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [sphereFiniteCutoffProfile8_zero_off_domain ρ hρ g i u hu, zero_mul])

theorem sphereFiniteCutoffWeight8_square_mass_transport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (i : Fin K) :
    (∫ x, (sphereFiniteCutoffWeight8 ρ hρ g i x)^2 ∂sphereProbability8) =
      (sphereArea8.real univ)⁻¹ * ∫ u, (sphereFiniteCutoffProfile8 ρ hρ g i u)^2 := by
  have h := sphereFiniteCutoffWeight8_probability_integral ρ hρ g hpos i
    (sphereFiniteCutoffProfile8 ρ hρ g i)
  simp_rw [sphereFiniteCutoffWeight8_times_profile_eq_square ρ hρ g hpos, ← pow_two] at h
  exact h

end SphericalRiesz
