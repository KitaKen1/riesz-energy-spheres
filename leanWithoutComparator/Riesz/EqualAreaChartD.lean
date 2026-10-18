import Riesz.SphereMeasureD
import Riesz.EqualAreaChart8

/-! The cylindrical equal-area chart of `S^(n+1)` in every dimension (stage P24).

Coordinate `0` is an angle `θ`, the other `n` coordinates are `u`, and the chart is
`(θ, u) ↦ (h cos θ, h sin θ, u)` with `h = √(1 - |u|²)` (Archimedes' hat-box map in higher
dimension). Sphere membership, injectivity on `{|u| < 1, |θ| < π/2}`, smoothness and the explicit
derivative are proved for every `n`; for `n = 7` the chart is the `S⁸` chart. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SphericalRiesz

variable {n : ℕ}

def equalAreaSquaredNormD (p : Fin (n+1) → ℝ) : ℝ := ∑ j : Fin n, p j.succ^2
def equalAreaHeightD (p : Fin (n+1) → ℝ) : ℝ := Real.sqrt (1-equalAreaSquaredNormD p)
def equalAreaPhiD (p : Fin (n+1) → ℝ) : AmbientD (n+1) :=
  WithLp.toLp 2 (Fin.cons (equalAreaHeightD p*Real.cos (p 0))
    (Fin.cons (equalAreaHeightD p*Real.sin (p 0)) (Fin.tail p)))

def equalAreaChartDomainD : Set (Fin (n+1) → ℝ) :=
  {p | equalAreaSquaredNormD p < 1 ∧ p 0 ∈ Ioo (-(Real.pi/2)) (Real.pi/2)}

/-- For `n = 7` the generic chart is the `S⁸` chart. -/
theorem equalAreaPhiD_seven (p : Fin 8 → ℝ) : equalAreaPhiD (n := 7) p = equalAreaPhi p := rfl

theorem equalAreaChartDomainD_seven :
    (equalAreaChartDomainD : Set (Fin 8 → ℝ)) = equalAreaChartDomain := rfl

theorem equalAreaSquaredNormD_nonneg (p : Fin (n+1) → ℝ) : 0 ≤ equalAreaSquaredNormD p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem equalAreaHeightD_pos (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    0 < equalAreaHeightD p := Real.sqrt_pos.mpr (by linarith)

theorem equalAreaHeightD_sq (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    equalAreaHeightD p^2 = 1-equalAreaSquaredNormD p := Real.sq_sqrt (by linarith)

theorem equalAreaSquaredNormD_eq_euclidean (p : Fin (n+1) → ℝ) :
    equalAreaSquaredNormD p = ‖(WithLp.toLp 2 (Fin.tail p) : EuclideanSpace ℝ (Fin n))‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem equalAreaPhiD_norm_sq (p : Fin (n+1) → ℝ) :
    ‖equalAreaPhiD p‖^2 = equalAreaHeightD p^2+equalAreaSquaredNormD p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [equalAreaPhiD, PiLp.toLp_apply, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  change (equalAreaHeightD p*Real.cos (p 0))^2 +
    ((equalAreaHeightD p*Real.sin (p 0))^2+equalAreaSquaredNormD p) = _
  calc
    _ = equalAreaHeightD p^2*(Real.sin (p 0)^2+Real.cos (p 0)^2)+equalAreaSquaredNormD p := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem equalAreaPhiD_mem_sphere (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    equalAreaPhiD p ∈ Metric.sphere (0 : AmbientD (n+1)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h := equalAreaPhiD_norm_sq p
  rw [equalAreaHeightD_sq p hp] at h
  nlinarith [norm_nonneg (equalAreaPhiD p)]

theorem equalAreaPhiD_continuous : Continuous (equalAreaPhiD (n := n)) := by
  unfold equalAreaPhiD equalAreaHeightD equalAreaSquaredNormD
  fun_prop

theorem equalAreaPhiD_contDiffOn :
    ContDiffOn ℝ ∞ (equalAreaPhiD (n := n)) {p | equalAreaSquaredNormD p < 1} := by
  have hq : ContDiff ℝ ∞ (equalAreaSquaredNormD (n := n)) := by
    unfold equalAreaSquaredNormD
    fun_prop
  have hh : ContDiffOn ℝ ∞ (equalAreaHeightD (n := n)) {p | equalAreaSquaredNormD p < 1} := by
    apply (contDiff_const.sub hq).contDiffOn.sqrt
    intro p hp
    exact ne_of_gt (by change equalAreaSquaredNormD p < 1 at hp; linarith)
  unfold equalAreaPhiD
  apply PiLp.contDiff_toLp.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact hh.mul (by fun_prop)
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_succ, Fin.cons_zero]
      exact hh.mul (by fun_prop)
    · simp only [Fin.cons_succ, Fin.tail]
      fun_prop

theorem equalAreaPhiD_injOn : InjOn (equalAreaPhiD (n := n)) equalAreaChartDomainD := by
  intro p hp q hq h
  have hu : Fin.tail p = Fin.tail q := by
    funext i
    have he := congrArg (fun z : AmbientD (n+1) => z i.succ.succ) h
    simpa only [equalAreaPhiD, PiLp.toLp_apply, Fin.cons_succ] using he
  have hn : equalAreaSquaredNormD p = equalAreaSquaredNormD q := by
    rw [equalAreaSquaredNormD_eq_euclidean, equalAreaSquaredNormD_eq_euclidean, hu]
  have hh : equalAreaHeightD p = equalAreaHeightD q := by unfold equalAreaHeightD; rw [hn]
  have hs : Real.sin (p 0) = Real.sin (q 0) := by
    have he := congrArg (fun z : AmbientD (n+1) => z (Fin.succ (0 : Fin (n+1)))) h
    have hmul : equalAreaHeightD p*Real.sin (p 0) = equalAreaHeightD p*Real.sin (q 0) := by
      simpa only [equalAreaPhiD, PiLp.toLp_apply, Fin.cons_succ, Fin.cons_zero, ← hh] using he
    exact mul_left_cancel₀ (equalAreaHeightD_pos p hp.1).ne' hmul
  have ht : p 0 = q 0 := Real.injOn_sin ⟨hp.2.1.le, hp.2.2.le⟩ ⟨hq.2.1.le, hq.2.2.le⟩ hs
  funext i
  exact Fin.cases ht (fun j => congrFun hu j) i

def equalAreaSphereChartD : (equalAreaChartDomainD : Set (Fin (n+1) → ℝ)) ↪ SphereD (n+1) where
  toFun p := ⟨equalAreaPhiD p.1, equalAreaPhiD_mem_sphere p.1 p.2.1⟩
  inj' := fun p q h => Subtype.ext
    (equalAreaPhiD_injOn p.property q.property (congrArg Subtype.val h))

def equalAreaNormGradientD (p : Fin (n+1) → ℝ) : (Fin (n+1) → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin n, p j.succ • ContinuousLinearMap.proj j.succ

def equalAreaHeightGradientD (p : Fin (n+1) → ℝ) : (Fin (n+1) → ℝ) →L[ℝ] ℝ :=
  -((equalAreaHeightD p)⁻¹) • equalAreaNormGradientD p

def equalAreaPhiDerivativeD (p : Fin (n+1) → ℝ) : (Fin (n+1) → ℝ) →L[ℝ] AmbientD (n+1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1+1) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.cons
      (Real.cos (p 0) • equalAreaHeightGradientD p+
        (-equalAreaHeightD p*Real.sin (p 0)) • ContinuousLinearMap.proj 0)
      (Fin.cons
        (Real.sin (p 0) • equalAreaHeightGradientD p+
          (equalAreaHeightD p*Real.cos (p 0)) • ContinuousLinearMap.proj 0)
        (fun j : Fin n => (ContinuousLinearMap.proj j.succ : (Fin (n+1) → ℝ) →L[ℝ] ℝ)))))

theorem equalAreaNormGradientD_apply (p v : Fin (n+1) → ℝ) :
    equalAreaNormGradientD p v = ∑ j : Fin n, p j.succ*v j.succ := by
  simp [equalAreaNormGradientD]

theorem equalAreaSquaredNormD_hasFDerivAt (p : Fin (n+1) → ℝ) :
    HasFDerivAt equalAreaSquaredNormD ((2:ℝ) • equalAreaNormGradientD p) p := by
  have h : HasFDerivAt (fun x : Fin (n+1) → ℝ => ∑ j : Fin n, x j.succ^2)
      (∑ j : Fin n, (2*p j.succ) • (ContinuousLinearMap.proj j.succ : (Fin (n+1) → ℝ) →L[ℝ] ℝ))
      p := by
    apply HasFDerivAt.fun_sum
    intro j _
    simpa using
      (ContinuousLinearMap.proj j.succ : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p) |>.pow 2
  apply h.congr_fderiv
  simp only [equalAreaNormGradientD, Finset.smul_sum, smul_smul]

theorem equalAreaHeightD_hasFDerivAt (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    HasFDerivAt equalAreaHeightD (equalAreaHeightGradientD p) p := by
  have hr : 0 < 1-equalAreaSquaredNormD p := by linarith
  have h := ((equalAreaSquaredNormD_hasFDerivAt p).const_sub 1).sqrt hr.ne'
  change HasFDerivAt (fun x => Real.sqrt (1-equalAreaSquaredNormD x)) _ p
  convert h using 1
  ext v
  simp only [equalAreaHeightGradientD, equalAreaHeightD, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul]
  ring

theorem equalAreaPhiD_hasFDerivAt (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    HasFDerivAt equalAreaPhiD (equalAreaPhiDerivativeD p) p := by
  have hh := equalAreaHeightD_hasFDerivAt p hp
  have ht := (ContinuousLinearMap.proj (0:Fin (n+1)) : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hc := ht.cos
  have hs := ht.sin
  have hpi : HasFDerivAt
      (fun x : Fin (n+1) → ℝ => (Fin.cons (equalAreaHeightD x*Real.cos (x 0))
        (Fin.cons (equalAreaHeightD x*Real.sin (x 0)) (Fin.tail x)) : Fin (n+1+1) → ℝ))
      ((ContinuousLinearMap.pi (Fin.cons
        (Real.cos (p 0) • equalAreaHeightGradientD p+
          (-equalAreaHeightD p*Real.sin (p 0)) • ContinuousLinearMap.proj 0)
        (Fin.cons
          (Real.sin (p 0) • equalAreaHeightGradientD p+
            (equalAreaHeightD p*Real.cos (p 0)) • ContinuousLinearMap.proj 0)
          (fun j : Fin n => (ContinuousLinearMap.proj j.succ : (Fin (n+1) → ℝ) →L[ℝ] ℝ))))) :
        (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1+1) → ℝ)) p := by
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
          (ContinuousLinearMap.proj k.succ : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)
  exact (PiLp.hasFDerivAt_toLp 2 _).comp p hpi

theorem equalAreaPhiD_fderiv (p : Fin (n+1) → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    fderiv ℝ equalAreaPhiD p = equalAreaPhiDerivativeD p :=
  (equalAreaPhiD_hasFDerivAt p hp).fderiv

theorem equalAreaChartDomainD_isOpen : IsOpen (equalAreaChartDomainD : Set (Fin (n+1) → ℝ)) := by
  have hq : Continuous (equalAreaSquaredNormD (n := n)) := by
    unfold equalAreaSquaredNormD; fun_prop
  exact (isOpen_lt hq continuous_const).inter
    (isOpen_Ioo.preimage (continuous_apply 0))

theorem equalAreaChartDomainD_measurable :
    MeasurableSet (equalAreaChartDomainD : Set (Fin (n+1) → ℝ)) :=
  equalAreaChartDomainD_isOpen.measurableSet

#print axioms equalAreaPhiD_seven
#print axioms equalAreaChartDomainD_seven
#print axioms equalAreaPhiD_norm_sq
#print axioms equalAreaPhiD_mem_sphere
#print axioms equalAreaPhiD_continuous
#print axioms equalAreaPhiD_contDiffOn
#print axioms equalAreaPhiD_injOn
#print axioms equalAreaNormGradientD_apply
#print axioms equalAreaSquaredNormD_hasFDerivAt
#print axioms equalAreaHeightD_hasFDerivAt
#print axioms equalAreaPhiD_hasFDerivAt
#print axioms equalAreaPhiD_fderiv
#print axioms equalAreaChartDomainD_isOpen
#print axioms equalAreaChartDomainD_measurable

end SphericalRiesz
