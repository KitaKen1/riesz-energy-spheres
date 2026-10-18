import Riesz.EqualAreaCone8
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual derivatives of the explicit radial cone. The orthogonality
is obtained by differentiating the actual identity |Phi|^2=1 locally,
rather than expanding seven transverse coordinate sums. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

def equalAreaTailProjection9 : (Fin 9 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.succ)

def equalAreaConeDerivative (z : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] Ambient9 :=
  z 0 • (equalAreaPhiDerivative (Fin.tail z)).comp equalAreaTailProjection9 +
    (ContinuousLinearMap.proj 0).smulRight (equalAreaPhi (Fin.tail z))

def equalAreaConeCoordinates (z : Fin 9 → ℝ) : Fin 9 → ℝ :=
  WithLp.ofLp (equalAreaCone z)

def equalAreaConeCoordinateDerivative (z : Fin 9 → ℝ) :
    (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).toContinuousLinearMap.comp
    (equalAreaConeDerivative z)

theorem equalAreaTailProjection9_apply (v : Fin 9 → ℝ) :
    equalAreaTailProjection9 v = Fin.tail v := rfl

theorem equalAreaCone_hasFDerivAt (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    HasFDerivAt equalAreaCone (equalAreaConeDerivative z) z := by
  have hp := (equalAreaPhi_hasFDerivAt (Fin.tail z) hz).comp z
    (equalAreaTailProjection9.hasFDerivAt (x := z))
  simpa only [equalAreaCone,equalAreaConeDerivative,Pi.smul_apply,
    Function.comp_def,equalAreaTailProjection9_apply] using!
    (ContinuousLinearMap.proj (0:Fin 9) : (Fin 9 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := z) |>.smul hp

theorem equalAreaConeCoordinates_hasFDerivAt (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    HasFDerivAt equalAreaConeCoordinates (equalAreaConeCoordinateDerivative z) z := by
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).toContinuousLinearMap.hasFDerivAt
    (x := equalAreaCone z)).comp z (equalAreaCone_hasFDerivAt z hz)

theorem equalAreaConeCoordinates_fderiv (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    fderiv ℝ equalAreaConeCoordinates z = equalAreaConeCoordinateDerivative z :=
  (equalAreaConeCoordinates_hasFDerivAt z hz).fderiv

theorem equalAreaPhi_derivative_orthogonal (p v : Fin 8 → ℝ)
    (hp : equalAreaSquaredNorm p < 1) :
    inner ℝ (equalAreaPhi p) (equalAreaPhiDerivative p v) = 0 := by
  have hq : Continuous equalAreaSquaredNorm := by unfold equalAreaSquaredNorm; fun_prop
  have he : (fun x => ‖equalAreaPhi x‖^2) =ᶠ[𝓝 p] (fun _ => (1:ℝ)) := by
    filter_upwards [(isOpen_lt hq continuous_const).mem_nhds hp] with x hx
    have hn := equalAreaPhi_norm_sq x
    rw [equalAreaHeight_sq x hx] at hn
    linarith
  have hc : HasFDerivAt (fun x => ‖equalAreaPhi x‖^2) 0 p :=
    (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).congr_of_eventuallyEq he
  have hd := (equalAreaPhi_hasFDerivAt p hp).norm_sq.unique hc
  have hv := congrArg (fun L : (Fin 8 → ℝ) →L[ℝ] ℝ => L v) hd
  simp only [two_smul,add_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,zero_apply] at hv
  linarith

end SphericalRiesz
