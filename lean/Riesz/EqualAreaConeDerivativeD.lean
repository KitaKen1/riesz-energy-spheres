import Riesz.EqualAreaConeD
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual derivatives of the explicit radial cone. The orthogonality
is obtained by differentiating the actual identity |Phi|^2=1 locally,
rather than expanding seven transverse coordinate sums. -/

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

variable {n : ℕ}

def equalAreaTailProjection9D : (Fin (n+1+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.succ)

def equalAreaConeDerivativeD (z : Fin (n+1+1) → ℝ) : (Fin (n+1+1) → ℝ) →L[ℝ] (AmbientD (n+1)) :=
  z 0 • (equalAreaPhiDerivativeD (Fin.tail z)).comp equalAreaTailProjection9D +
    (ContinuousLinearMap.proj 0).smulRight (equalAreaPhiD (Fin.tail z))

def equalAreaConeCoordinatesD (z : Fin (n+1+1) → ℝ) : Fin (n+1+1) → ℝ :=
  WithLp.ofLp (equalAreaConeD z)

def equalAreaConeCoordinateDerivativeD (z : Fin (n+1+1) → ℝ) :
    (Fin (n+1+1) → ℝ) →L[ℝ] (Fin (n+1+1) → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1+1) => ℝ)).toContinuousLinearMap.comp
    (equalAreaConeDerivativeD z)

theorem equalAreaTailProjection9D_apply (v : Fin (n+1+1) → ℝ) :
    equalAreaTailProjection9D v = Fin.tail v := rfl

theorem equalAreaConeD_hasFDerivAt (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    HasFDerivAt equalAreaConeD (equalAreaConeDerivativeD z) z := by
  have hp := (equalAreaPhiD_hasFDerivAt (Fin.tail z) hz).comp z
    (equalAreaTailProjection9D.hasFDerivAt (x := z))
  simpa only [equalAreaConeD,equalAreaConeDerivativeD,Pi.smul_apply,
    Function.comp_def,equalAreaTailProjection9D_apply] using!
    (ContinuousLinearMap.proj (0:Fin (n+1+1)) : (Fin (n+1+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := z) |>.smul hp

theorem equalAreaConeCoordinatesD_hasFDerivAt (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    HasFDerivAt equalAreaConeCoordinatesD (equalAreaConeCoordinateDerivativeD z) z := by
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1+1) => ℝ)).toContinuousLinearMap.hasFDerivAt
    (x := equalAreaConeD z)).comp z (equalAreaConeD_hasFDerivAt z hz)

theorem equalAreaConeCoordinatesD_fderiv (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    fderiv ℝ equalAreaConeCoordinatesD z = equalAreaConeCoordinateDerivativeD z :=
  (equalAreaConeCoordinatesD_hasFDerivAt z hz).fderiv

theorem equalAreaPhiD_derivative_orthogonal (p v : Fin (n+1) → ℝ)
    (hp : equalAreaSquaredNormD p < 1) :
    inner ℝ (equalAreaPhiD p) (equalAreaPhiDerivativeD p v) = 0 := by
  have hq : Continuous (equalAreaSquaredNormD (n := n)) := by unfold equalAreaSquaredNormD; fun_prop
  have he : (fun x => ‖equalAreaPhiD x‖^2) =ᶠ[𝓝 p] (fun _ => (1:ℝ)) := by
    filter_upwards [(isOpen_lt hq continuous_const).mem_nhds hp] with x hx
    have hn := equalAreaPhiD_norm_sq x
    rw [equalAreaHeightD_sq x hx] at hn
    linarith
  have hc : HasFDerivAt (fun x => ‖equalAreaPhiD x‖^2) 0 p :=
    (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) p).congr_of_eventuallyEq he
  have hd := (equalAreaPhiD_hasFDerivAt p hp).norm_sq.unique hc
  have hv := congrArg (fun L : (Fin (n+1) → ℝ) →L[ℝ] ℝ => L v) hd
  simp only [two_smul,add_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,zero_apply] at hv
  linarith

end SphericalRiesz
