import Riesz.SphereMeasure8
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The explicit spherical chart with Gram determinant one

Coordinate 0 is the angle and the other seven coordinates are u.
The output is (h cos(theta), h sin(theta), u), h=sqrt(1-|u|^2).
This is the paper's chart up to a fixed coordinate permutation.
Actual sphere membership, local injectivity and smoothness are proved here.
The derivative/Gram determinant do not by themselves identify the actual
surface-area measure: that measure connection remains a separate obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SphericalRiesz

def equalAreaSquaredNorm (p : Fin 8 → ℝ) : ℝ := ∑ j : Fin 7, p j.succ^2
def equalAreaHeight (p : Fin 8 → ℝ) : ℝ := Real.sqrt (1-equalAreaSquaredNorm p)
def equalAreaPhi (p : Fin 8 → ℝ) : Ambient9 :=
  WithLp.toLp 2 (Fin.cons (equalAreaHeight p*Real.cos (p 0))
    (Fin.cons (equalAreaHeight p*Real.sin (p 0)) (Fin.tail p)))

def equalAreaChartDomain : Set (Fin 8 → ℝ) :=
  {p | equalAreaSquaredNorm p < 1 ∧ p 0 ∈ Ioo (-(Real.pi/2)) (Real.pi/2)}

theorem equalAreaSquaredNorm_nonneg (p : Fin 8 → ℝ) : 0 ≤ equalAreaSquaredNorm p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem equalAreaHeight_pos (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    0 < equalAreaHeight p := Real.sqrt_pos.mpr (by linarith)

theorem equalAreaHeight_sq (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    equalAreaHeight p^2 = 1-equalAreaSquaredNorm p := Real.sq_sqrt (by linarith)

theorem equalAreaSquaredNorm_eq_euclidean (p : Fin 8 → ℝ) :
    equalAreaSquaredNorm p = ‖(WithLp.toLp 2 (Fin.tail p) : EuclideanSpace ℝ (Fin 7))‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem equalAreaPhi_norm_sq (p : Fin 8 → ℝ) :
    ‖equalAreaPhi p‖^2 = equalAreaHeight p^2+equalAreaSquaredNorm p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [equalAreaPhi,PiLp.toLp_apply,Fin.cons_zero,Fin.cons_succ,Fin.tail]
  change (equalAreaHeight p*Real.cos (p 0))^2 +
    ((equalAreaHeight p*Real.sin (p 0))^2+equalAreaSquaredNorm p) = _
  calc
    _ = equalAreaHeight p^2*(Real.sin (p 0)^2+Real.cos (p 0)^2)+equalAreaSquaredNorm p := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq,mul_one]

theorem equalAreaPhi_mem_sphere (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    equalAreaPhi p ∈ Metric.sphere (0 : Ambient9) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h := equalAreaPhi_norm_sq p
  rw [equalAreaHeight_sq p hp] at h
  nlinarith [norm_nonneg (equalAreaPhi p)]

theorem equalAreaPhi_continuous : Continuous equalAreaPhi := by
  unfold equalAreaPhi equalAreaHeight equalAreaSquaredNorm
  fun_prop

theorem equalAreaPhi_contDiffOn :
    ContDiffOn ℝ ∞ equalAreaPhi {p | equalAreaSquaredNorm p < 1} := by
  have hq : ContDiff ℝ ∞ equalAreaSquaredNorm := by
    unfold equalAreaSquaredNorm
    fun_prop
  have hh : ContDiffOn ℝ ∞ equalAreaHeight {p | equalAreaSquaredNorm p < 1} := by
    apply (contDiff_const.sub hq).contDiffOn.sqrt
    intro p hp
    exact ne_of_gt (by change equalAreaSquaredNorm p < 1 at hp; linarith)
  unfold equalAreaPhi
  apply PiLp.contDiff_toLp.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact hh.mul (by fun_prop)
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_succ,Fin.cons_zero]
      exact hh.mul (by fun_prop)
    · simp only [Fin.cons_succ,Fin.tail]
      fun_prop

theorem equalAreaPhi_injOn : InjOn equalAreaPhi equalAreaChartDomain := by
  intro p hp q hq h
  have hu : Fin.tail p = Fin.tail q := by
    funext i
    have he := congrArg (fun z : Ambient9 => z i.succ.succ) h
    simpa only [equalAreaPhi,PiLp.toLp_apply,Fin.cons_succ] using he
  have hn : equalAreaSquaredNorm p = equalAreaSquaredNorm q := by
    rw [equalAreaSquaredNorm_eq_euclidean,equalAreaSquaredNorm_eq_euclidean,hu]
  have hh : equalAreaHeight p = equalAreaHeight q := by unfold equalAreaHeight; rw [hn]
  have hs : Real.sin (p 0) = Real.sin (q 0) := by
    have he := congrArg (fun z : Ambient9 => z (1 : Fin 9)) h
    have hmul : equalAreaHeight p*Real.sin (p 0) = equalAreaHeight p*Real.sin (q 0) := by
      simpa only [equalAreaPhi,PiLp.toLp_apply,show (1:Fin 9) = (0:Fin 8).succ from rfl,
        Fin.cons_succ,Fin.cons_zero,← hh] using he
    exact mul_left_cancel₀ (equalAreaHeight_pos p hp.1).ne' hmul
  have ht : p 0 = q 0 := Real.injOn_sin ⟨hp.2.1.le,hp.2.2.le⟩ ⟨hq.2.1.le,hq.2.2.le⟩ hs
  funext i
  exact Fin.cases ht (fun j => congrFun hu j) i

def equalAreaSphereChart : equalAreaChartDomain ↪ Sphere8 where
  toFun p := ⟨equalAreaPhi p,equalAreaPhi_mem_sphere p p.property.1⟩
  inj' := fun p q h => Subtype.ext
    (equalAreaPhi_injOn p.property q.property (congrArg Subtype.val h))

def equalAreaNormGradient (p : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 7, p j.succ • ContinuousLinearMap.proj j.succ

def equalAreaHeightGradient (p : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] ℝ :=
  -((equalAreaHeight p)⁻¹) • equalAreaNormGradient p

def equalAreaPhiDerivative (p : Fin 8 → ℝ) : (Fin 8 → ℝ) →L[ℝ] Ambient9 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.cons
      (Real.cos (p 0) • equalAreaHeightGradient p+
        (-equalAreaHeight p*Real.sin (p 0)) • ContinuousLinearMap.proj 0)
      (Fin.cons
        (Real.sin (p 0) • equalAreaHeightGradient p+
          (equalAreaHeight p*Real.cos (p 0)) • ContinuousLinearMap.proj 0)
        (fun j : Fin 7 => (ContinuousLinearMap.proj j.succ : (Fin 8 → ℝ) →L[ℝ] ℝ)))))

theorem equalAreaNormGradient_apply (p v : Fin 8 → ℝ) :
    equalAreaNormGradient p v = ∑ j : Fin 7, p j.succ*v j.succ := by
  simp [equalAreaNormGradient]

theorem equalAreaSquaredNorm_hasFDerivAt (p : Fin 8 → ℝ) :
    HasFDerivAt equalAreaSquaredNorm ((2:ℝ) • equalAreaNormGradient p) p := by
  have h : HasFDerivAt (fun x : Fin 8 → ℝ => ∑ j : Fin 7, x j.succ^2)
      (∑ j : Fin 7, (2*p j.succ) • (ContinuousLinearMap.proj j.succ : (Fin 8 → ℝ) →L[ℝ] ℝ)) p := by
    apply HasFDerivAt.fun_sum
    intro j _
    simpa using
      (ContinuousLinearMap.proj j.succ : (Fin 8 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p) |>.pow 2
  apply h.congr_fderiv
  simp only [equalAreaNormGradient,Finset.smul_sum,smul_smul]

theorem equalAreaHeight_hasFDerivAt (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    HasFDerivAt equalAreaHeight (equalAreaHeightGradient p) p := by
  have hr : 0 < 1-equalAreaSquaredNorm p := by linarith
  have h := ((equalAreaSquaredNorm_hasFDerivAt p).const_sub 1).sqrt hr.ne'
  change HasFDerivAt (fun x => Real.sqrt (1-equalAreaSquaredNorm x)) _ p
  convert h using 1
  ext v
  simp only [equalAreaHeightGradient,equalAreaHeight,smul_apply,
    neg_apply,
    smul_eq_mul]
  ring

theorem equalAreaPhi_hasFDerivAt (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    HasFDerivAt equalAreaPhi (equalAreaPhiDerivative p) p := by
  have hh := equalAreaHeight_hasFDerivAt p hp
  have ht := (ContinuousLinearMap.proj (0:Fin 8) : (Fin 8 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hc := ht.cos
  have hs := ht.sin
  have hpi : HasFDerivAt
      (fun x : Fin 8 → ℝ => (Fin.cons (equalAreaHeight x*Real.cos (x 0))
        (Fin.cons (equalAreaHeight x*Real.sin (x 0)) (Fin.tail x)) : Fin 9 → ℝ))
      ((ContinuousLinearMap.pi (Fin.cons
        (Real.cos (p 0) • equalAreaHeightGradient p+
          (-equalAreaHeight p*Real.sin (p 0)) • ContinuousLinearMap.proj 0)
        (Fin.cons
          (Real.sin (p 0) • equalAreaHeightGradient p+
            (equalAreaHeight p*Real.cos (p 0)) • ContinuousLinearMap.proj 0)
          (fun j : Fin 7 => (ContinuousLinearMap.proj j.succ : (Fin 8 → ℝ) →L[ℝ] ℝ))))) :
        (Fin 8 → ℝ) →L[ℝ] (Fin 9 → ℝ)) p := by
    apply hasFDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply (hh.mul hc).congr_fderiv
      ext v
      simp
      ring
    · refine Fin.cases ?_ (fun k => ?_) j
      · apply (hh.mul hs).congr_fderiv
        ext v
        simp
        ring
      · simpa [Fin.tail] using!
          (ContinuousLinearMap.proj k.succ : (Fin 8 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  exact (PiLp.hasFDerivAt_toLp 2 _).comp p hpi

theorem equalAreaPhi_fderiv (p : Fin 8 → ℝ) (hp : equalAreaSquaredNorm p < 1) :
    fderiv ℝ equalAreaPhi p = equalAreaPhiDerivative p :=
  (equalAreaPhi_hasFDerivAt p hp).fderiv

theorem equalAreaChartDomain_isOpen : IsOpen equalAreaChartDomain := by
  have hq : Continuous equalAreaSquaredNorm := by unfold equalAreaSquaredNorm; fun_prop
  exact (isOpen_lt hq continuous_const).inter
    (isOpen_Ioo.preimage (continuous_apply 0))

theorem equalAreaChartDomain_measurable : MeasurableSet equalAreaChartDomain :=
  equalAreaChartDomain_isOpen.measurableSet

end SphericalRiesz
