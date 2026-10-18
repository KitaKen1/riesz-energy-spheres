import Riesz.EqualAreaPatchFar8
import Riesz.E8PotentialAveraging

/-! Average the actual curved far rows by symmetry and finite-sum/integral
exchange. A finite continuous extension agrees on the whole cube product;
global injectivity and high derivatives of the potential are unnecessary. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem curvedRieszFour8_symm (F : (Fin 8 → ℝ) → Ambient9) (x y : Fin 8 → ℝ) :
    curvedRieszFour F x y = curvedRieszFour F y x := by
  simp only [curvedRieszFour,dist_comm]

theorem curvedNearRieszFour8_symm (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (x y : Fin 8 → ℝ) :
    curvedNearRieszFour F r x y = curvedNearRieszFour F r y x := by
  unfold curvedNearRieszFour
  rw [curvedRieszFour8_symm]
  congr 1
  rw [show r⁻¹ • (y-x) = -(r⁻¹ • (x-y)) by rw [← smul_neg,neg_sub]]
  exact (outerUnitBump 8).neg _

theorem curvedFarRieszFour8_symm (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (x y : Fin 8 → ℝ) :
    curvedFarRieszFour8 F r x y = curvedFarRieszFour8 F r y x := by
  unfold curvedFarRieszFour8
  rw [curvedRieszFour8_symm,curvedNearRieszFour8_symm]

theorem curvedAnnularExtension8_joint_continuous (F : (Fin 8 → ℝ) → Ambient9)
    (hF : Continuous F) (r : ℝ) :
    Continuous (fun p : (Fin 8 → ℝ) × (Fin 8 → ℝ) => curvedAnnularExtension8 F r p.1 p.2) := by
  by_cases h : r ≤ 2
  · simp only [curvedAnnularExtension8,ite_eq_left h]
    unfold regularizedCurvedAnnular8 curvedAnnularPair8
    apply continuous_const.mul
    apply (curvedAnnularAuxiliary8_contDiff _ _ _ _).continuous.comp
    exact (((hF.comp continuous_snd).sub (hF.comp continuous_fst)).const_smul r⁻¹).prodMk
      ((continuous_snd.sub continuous_fst).const_smul r⁻¹)
  · simp only [curvedAnnularExtension8,ite_eq_right h]
    exact continuous_const

theorem curvedFarRieszFour8_continuous_extension (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r) :
    ∃ H : (Fin 8 → ℝ) × (Fin 8 → ℝ) → ℝ, Continuous H ∧
      ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8, H (x,y) = curvedFarRieszFour8 F r x y := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2/r) (by norm_num : (1:ℝ) < 2)
  have hn' : 1 ≤ ((2:ℝ)^n*r)/2 := by
    have hp := (div_lt_iff₀ hr).mp hn
    linarith
  let H : (Fin 8 → ℝ) × (Fin 8 → ℝ) → ℝ :=
    fun p => ∑ k ∈ Finset.range n, curvedAnnularExtension8 F ((2:ℝ)^k*r) p.1 p.2
  refine ⟨H,continuous_finsetSum _ (fun k _ => curvedAnnularExtension8_joint_continuous F hF.continuous _),?_⟩
  intro x hx y hy
  exact (curvedFarRieszFour8_eq_extension_sum_on F hF r hr n x hx
    (fun z hz => (unitCube8_sub_norm z x hz hx).trans hn') hy).symm

def curvedFarPotential8 (F : (Fin 8 → ℝ) → Ambient9) (r : ℝ) (x : Fin 8 → ℝ) : ℝ :=
  ∫ y in UnitCube 8, curvedFarRieszFour8 F r x y

theorem curvedFarRieszFour8_continuousOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    ContinuousOn (curvedFarRieszFour8 F r x) (UnitCube 8) := by
  obtain ⟨H,hH,heq⟩ := curvedFarRieszFour8_continuous_extension F hF r hr
  exact (hH.comp (continuous_const.prodMk continuous_id)).continuousOn.congr (fun y hy => (heq x hx y hy).symm)

theorem curvedFarPotential8_continuousOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r) :
    ContinuousOn (curvedFarPotential8 F r) (UnitCube 8) := by
  obtain ⟨H,hH,heq⟩ := curvedFarRieszFour8_continuous_extension F hF r hr
  have hc := continuous_cubeIntegral_param 8 (F := fun x y => H (x,y)) hH
  apply hc.continuousOn.congr
  intro x hx
  change (∫ y in UnitCube 8, curvedFarRieszFour8 F r x y) = cubeIntegral 8 (fun y => H (x,y))
  have hcH : Continuous (fun y => H (x,y)) := hH.comp (continuous_const.prodMk continuous_id)
  rw [cubeIntegral_eq_setIntegral 8 (fun y => H (x,y)) hcH]
  exact setIntegral_congr_fun (unitCube_measurableSet 8) (fun y hy => (heq x hx y hy).symm)

theorem curvedFarRowQuadrature8_continuousOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r) (m : ℕ) (hm : 8 ≤ m) :
    ContinuousOn (fun y => cubeQuadrature 8 m (curvedFarRieszFour8 F r y)) (UnitCube 8) := by
  obtain ⟨H,hH,heq⟩ := curvedFarRieszFour8_continuous_extension F hF r hr
  apply (cubeQuadrature_continuous_parameter 8 m hH).continuousOn.congr
  intro y hy
  apply cubeQuadrature_congr 8 m hm
  intro x hx
  exact (curvedFarRieszFour8_symm F r y x).trans (heq x hx y hy).symm

theorem curvedFarPotential8_quadrature_integral_identity (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (r : ℝ) (hr : 0 < r) (m : ℕ) (hm : 8 ≤ m) :
    cubeQuadrature 8 m (curvedFarPotential8 F r)-∫ y in UnitCube 8, curvedFarPotential8 F r y =
      ∫ y in UnitCube 8,
        (cubeQuadrature 8 m (curvedFarRieszFour8 F r y)-curvedFarPotential8 F r y) := by
  obtain ⟨H,hH,heq⟩ := curvedFarRieszFour8_continuous_extension F hF r hr
  have hp : EqOn (curvedFarPotential8 F r) (fun x => ∫ y in UnitCube 8, H (x,y)) (UnitCube 8) := by
    intro x hx
    exact setIntegral_congr_fun (unitCube_measurableSet 8) (fun y hy => (heq x hx y hy).symm)
  have hq : cubeQuadrature 8 m (curvedFarPotential8 F r) =
      ∫ y in UnitCube 8, cubeQuadrature 8 m (curvedFarRieszFour8 F r y) := by
    rw [cubeQuadrature_congr 8 m hm hp,cubeQuadrature_setIntegral_comm 8 m hH]
    apply setIntegral_congr_fun (unitCube_measurableSet 8)
    intro y hy
    apply cubeQuadrature_congr 8 m hm
    intro x hx
    exact (heq x hx y hy).trans (curvedFarRieszFour8_symm F r x y)
  rw [hq,integral_sub]
  · exact (curvedFarRowQuadrature8_continuousOn F hF r hr m hm).integrableOn_compact (unitCube_isCompact 8)
  · exact (curvedFarPotential8_continuousOn F hF r hr).integrableOn_compact (unitCube_isCompact 8)

theorem curvedFarPotential8_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      |cubeQuadrature 8 m (curvedFarPotential8 F r)-∫ x in UnitCube 8, curvedFarPotential8 F r x|
        ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C,hC,hb⟩ := curvedFarRieszFour8_quadrature_bound
  refine ⟨C,hC,?_⟩
  intro F hF m hm r hr hmesh
  rw [curvedFarPotential8_quadrature_integral_identity F hF r hr m hm]
  have hdiff := (curvedFarRowQuadrature8_continuousOn F hF r hr m hm).sub
    (curvedFarPotential8_continuousOn F hF r hr)
  change ContinuousOn (fun y => cubeQuadrature 8 m (curvedFarRieszFour8 F r y)-curvedFarPotential8 F r y)
    (UnitCube 8) at hdiff
  rw [← cubeIntegral_eq_setIntegral_on 8 _ hdiff]
  apply cubeIntegral_abs_le
  intro x hx
  have h := hb F hF m hm r hr hmesh x hx
  rw [cubeIntegral_eq_setIntegral_on 8 _ (curvedFarRieszFour8_continuousOn F hF r hr x hx)] at h
  exact h

theorem curvedFarPotential8_scaled_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      ∀ m : ℕ, 8 ≤ m → ∀ R : ℝ, 1 ≤ R →
      |(m:ℝ)^4*(cubeQuadrature 8 m (curvedFarPotential8 F (R/(m:ℝ)))-
        ∫ x in UnitCube 8, curvedFarPotential8 F (R/(m:ℝ)) x)| ≤ C/R^2 := by
  obtain ⟨C,hC,hb⟩ := curvedFarPotential8_quadrature_bound
  refine ⟨C,hC,?_⟩
  intro F hF m hm R hR
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR0 : 0 < R := by linarith
  have hmesh : 1/(m:ℝ) ≤ R/(m:ℝ) := div_le_div_of_nonneg_right hR hm0.le
  rw [abs_mul,abs_of_nonneg (pow_nonneg hm0.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(C/((m:ℝ)^6*(R/(m:ℝ))^2)) :=
      mul_le_mul_of_nonneg_left (hb F hF m hm _ (div_pos hR0 hm0) hmesh) (by positivity)
    _ = C/R^2 := by field_simp [hm0.ne',hR0.ne']

theorem equalAreaPatchFarPotential8_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, 8 ≤ m → ∀ R : ℝ, 1 ≤ R →
      |(m:ℝ)^4*(cubeQuadrature 8 m (curvedFarPotential8 (equalAreaNormalizedE8Patch g v c ε) (R/(m:ℝ)))-
        ∫ x in UnitCube 8, curvedFarPotential8 (equalAreaNormalizedE8Patch g v c ε) (R/(m:ℝ)) x)| ≤ C/R^2 := by
  obtain ⟨ρ,hρ,hρb,hdata⟩ := equalAreaNormalizedE8Patch_annular_data_uniform
  obtain ⟨C,hC,hb⟩ := curvedFarPotential8_scaled_quadrature_bound
  exact ⟨ρ,hρ,hρb,C,hC,fun v hv ε hε hs g c hc m hm R hR =>
    hb _ (hdata v hv ε hε hs g c hc) m hm R hR⟩

end SphericalRiesz
