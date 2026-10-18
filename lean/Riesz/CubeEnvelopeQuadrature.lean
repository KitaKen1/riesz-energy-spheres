import Riesz.L1Quadrature
import Riesz.CubeLebesgue
import Riesz.BoxQuadrature

/-! Sixth-order tensor quadrature with a product envelope.

If every pure sixth slice derivative of `f` is bounded by `A ∏ⱼ φⱼ(vⱼ)` with nonnegative
continuous `φⱼ`, and both the one-dimensional rule and the integral of each `φⱼ` are at most `Bⱼ`,
then `|Q f - I f| ≤ (64/m⁶)·d·A·∏ⱼ Bⱼ`.  The head coordinate uses the one-dimensional `L¹`
Peano bound; the remaining coordinates see the rule average of the envelope.  This localizes the
error of a narrow bump to its own width, unlike the sup-norm bound. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem quadrature_abs_le_of_le {m : ℕ} (hm : 8 ≤ m) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ g x) : |quadrature m f| ≤ quadrature m g := by
  apply abs_le.mpr
  constructor
  · have hl := quadrature_mono hm (f := fun x => (-1)*g x) (g := f)
      (fun x hx => by have := (abs_le.mp (h x hx)).1; linarith)
    rw [quadrature_mul_const] at hl
    linarith
  · exact quadrature_mono hm (fun x hx => (abs_le.mp (h x hx)).2)

theorem cubeIntegral_prod (d : ℕ) (φ : Fin d → ℝ → ℝ) :
    cubeIntegral d (fun v => ∏ j, φ j (v j)) = ∏ j, ∫ t in (0:ℝ)..1, φ j t := by
  induction d with
  | zero => simp [cubeIntegral]
  | succ d ih =>
    have h : (fun v : Fin d → ℝ => ∫ t in (0:ℝ)..1,
        ∏ j, φ j ((Fin.cons t v : Fin (d+1) → ℝ) j)) =
        fun v => (∫ t in (0:ℝ)..1, φ 0 t)*∏ j : Fin d, φ j.succ (v j) := by
      funext v
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [intervalIntegral.integral_mul_const]
    change cubeIntegral d (fun v => ∫ t in (0:ℝ)..1,
      ∏ j, φ j ((Fin.cons t v : Fin (d+1) → ℝ) j)) = _
    rw [h, cubeIntegral_mul_const, ih (fun j => φ j.succ), Fin.prod_univ_succ]

theorem cubeIntegral_abs_le_of_le (d : ℕ) {f g : (Fin d → ℝ) → ℝ}
    (hf : ContinuousOn f (UnitCube d)) (hg : ContinuousOn g (UnitCube d))
    (h : ∀ v ∈ UnitCube d, |f v| ≤ g v) : |cubeIntegral d f| ≤ cubeIntegral d g := by
  rw [cubeIntegral_eq_setIntegral_on d f hf, cubeIntegral_eq_setIntegral_on d g hg]
  have hig : IntegrableOn g (UnitCube d) := hg.integrableOn_compact (unitCube_isCompact d)
  calc |∫ v in UnitCube d, f v| = ‖∫ v in UnitCube d, f v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ v in UnitCube d, ‖f v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in UnitCube d, g v := by
        apply setIntegral_mono_on (hf.norm.integrableOn_compact (unitCube_isCompact d)) hig
          (unitCube_measurableSet d)
        intro v hv
        rw [Real.norm_eq_abs]
        exact h v hv

/-- Tensor sixth-order bound with a product envelope. -/
theorem cubeQuadrature_sixth_order_envelope (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1))
    (φ : Fin d → ℝ → ℝ) (hφ : ∀ j, Continuous (φ j)) (hφ0 : ∀ j t, 0 ≤ φ j t)
    (B : Fin d → ℝ) (hQ : ∀ j, quadrature m (φ j) ≤ B j)
    (hI : ∀ j, (∫ t in (0:ℝ)..1, φ j t) ≤ B j) {A : ℝ} (hA : 0 ≤ A)
    (hM : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u)) (Set.Icc (0 : ℝ) 1) t| ≤
        A*∏ j, φ j (Function.update v i t j)) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤ (64/(m : ℝ)^6)*(d*(A*∏ j, B j)) := by
  induction d generalizing A with
  | zero => simp [cubeQuadrature, cubeIntegral]
  | succ d ih =>
    have hB0 : ∀ j, 0 ≤ B j := fun j =>
      (intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hφ0 j t)).trans (hI j)
    let q : (Fin d → ℝ) → ℝ := fun v => quadrature m (fun t => f (Fin.cons t v))
    let a : (Fin d → ℝ) → ℝ := fun v => ∫ t in (0 : ℝ)..1, f (Fin.cons t v)
    let P0 : (Fin d → ℝ) → ℝ := fun v => ∏ j : Fin d, φ j.succ (v j)
    have hq : Continuous q := continuous_quadrature_param m (hf.comp (by fun_prop))
    have ha : Continuous a := continuous_unitIntegral_param (hf.comp (by fun_prop))
    have hP0 : Continuous P0 := continuous_finsetProd _ fun j _ => (hφ j.succ).comp (by fun_prop)
    have hP0nn : ∀ v, 0 ≤ P0 v := fun v => Finset.prod_nonneg fun j _ => hφ0 _ _
    have hsq : ∀ i v, v ∈ UnitCube d →
        ContDiffOn ℝ 6 (fun t => q (Function.update v i t)) (Set.Icc (0 : ℝ) 1) := by
      intro i v hv
      apply contDiffOn_quadrature_param
      intro j
      simpa only [Nat.cast_ofNat, ← Fin.cons_update] using
        hs i.succ (Fin.cons (ruleNode m j) v)
          (cons_mem_unitCube (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm j)) hv)
    have hMq : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDerivWithin 6 (fun u => q (Function.update v i u))
          (Set.Icc (0 : ℝ) 1) t| ≤ (A*B 0)*∏ j : Fin d, φ j.succ (Function.update v i t j) := by
      intro i v hv t ht
      have hsl : ∀ j : NodeIndex m, ContDiffOn ℝ 6
          (fun u => f (Fin.cons (ruleNode m j) (Function.update v i u)))
            (Set.Icc (0 : ℝ) 1) := by
        intro j
        simpa only [← Fin.cons_update] using
          hs i.succ (Fin.cons (ruleNode m j) v)
            (cons_mem_unitCube (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm j)) hv)
      dsimp only [q]
      rw [iteratedDerivWithin_quadrature_param m 6 (uniqueDiffOn_Icc (by norm_num)) hsl ht]
      set P := ∏ j : Fin d, φ j.succ (Function.update v i t j) with hPdef
      have hPnn : 0 ≤ P := Finset.prod_nonneg fun j _ => hφ0 _ _
      have hpt : ∀ z ∈ Set.Icc (0 : ℝ) 1,
          |iteratedDerivWithin 6 (fun u => f (Fin.cons z (Function.update v i u)))
            (Set.Icc (0 : ℝ) 1) t| ≤ (A*P)*φ 0 z := by
        intro z hz
        have h := hM i.succ (Fin.cons z v) (cons_mem_unitCube hz hv) t ht
        simp only [← Fin.cons_update] at h
        rw [Fin.prod_univ_succ] at h
        simp only [Fin.cons_zero, Fin.cons_succ] at h
        calc _ ≤ A*(φ 0 z*∏ j : Fin d, φ j.succ (Function.update v i t j)) := h
          _ = (A*P)*φ 0 z := by rw [hPdef]; ring
      calc _ ≤ quadrature m (fun z => (A*P)*φ 0 z) := quadrature_abs_le_of_le hm hpt
        _ = (A*P)*quadrature m (φ 0) := quadrature_mul_const m _ _
        _ ≤ (A*P)*B 0 := mul_le_mul_of_nonneg_left (hQ 0) (mul_nonneg hA hPnn)
        _ = (A*B 0)*P := by ring
    have hfirst := ih hq hsq (fun j => φ j.succ) (fun j => hφ j.succ) (fun j t => hφ0 j.succ t)
      (fun j => B j.succ) (fun j => hQ j.succ) (fun j => hI j.succ) (mul_nonneg hA (hB0 0)) hMq
    have hhead : ∀ v ∈ UnitCube d, |q v-a v| ≤ (64/(m : ℝ)^6)*((A*B 0)*P0 v) := by
      intro v hv
      have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hsl : ContDiffOn ℝ 6 (fun t => f (Fin.cons t v)) (Set.Icc (0 : ℝ) 1) := by
        simpa only [Fin.update_cons_zero] using hs 0 (Fin.cons 0 v) (cons_mem_unitCube hz hv)
      have hl1 := quadrature_sixth_order_l1_bound_on hm hsl
      have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |iteratedDerivWithin 6 (fun t => f (Fin.cons t v)) (Set.Icc (0 : ℝ) 1) t| ≤
            (A*P0 v)*φ 0 t := by
        intro t ht
        have h := hM 0 (Fin.cons 0 v) (cons_mem_unitCube hz hv) t ht
        simp only [Fin.update_cons_zero] at h
        rw [Fin.prod_univ_succ] at h
        simp only [Fin.cons_zero, Fin.cons_succ] at h
        calc _ ≤ A*(φ 0 t*∏ j : Fin d, φ j.succ (v j)) := h
          _ = (A*P0 v)*φ 0 t := by ring
      have hcont : ContinuousOn
          (fun t => |iteratedDerivWithin 6 (fun t => f (Fin.cons t v)) (Set.Icc (0 : ℝ) 1) t|)
          (Set.Icc (0 : ℝ) 1) :=
        (hsl.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc (by norm_num))).abs
      have hint : (∫ t in (0 : ℝ)..1,
          |iteratedDerivWithin 6 (fun t => f (Fin.cons t v)) (Set.Icc (0 : ℝ) 1) t|) ≤
          (A*P0 v)*B 0 := by
        calc _ ≤ ∫ t in (0 : ℝ)..1, (A*P0 v)*φ 0 t := by
              apply intervalIntegral.integral_mono_on (by norm_num)
              · apply ContinuousOn.intervalIntegrable
                simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hcont
              · exact ((hφ 0).const_smul (A*P0 v)).intervalIntegrable _ _
              · exact hpt
          _ = (A*P0 v)*∫ t in (0 : ℝ)..1, φ 0 t := intervalIntegral.integral_const_mul _ _
          _ ≤ (A*P0 v)*B 0 := mul_le_mul_of_nonneg_left (hI 0) (mul_nonneg hA (hP0nn v))
      calc |q v-a v| ≤ (64/(m : ℝ)^6)*(∫ t in (0 : ℝ)..1,
            |iteratedDerivWithin 6 (fun t => f (Fin.cons t v)) (Set.Icc (0 : ℝ) 1) t|) := hl1
        _ ≤ (64/(m : ℝ)^6)*((A*P0 v)*B 0) := mul_le_mul_of_nonneg_left hint (by positivity)
        _ = (64/(m : ℝ)^6)*((A*B 0)*P0 v) := by ring
    have hsecond : |cubeIntegral d q-cubeIntegral d a| ≤
        (64/(m : ℝ)^6)*((A*B 0)*∏ j : Fin d, B j.succ) := by
      rw [← cubeIntegral_sub d q a hq ha]
      have hle := cubeIntegral_abs_le_of_le d (f := fun v => q v-a v)
        (g := fun v => (64/(m : ℝ)^6)*((A*B 0)*P0 v)) (hq.sub ha).continuousOn
        (by fun_prop) hhead
      refine hle.trans ?_
      rw [cubeIntegral_mul_const, cubeIntegral_mul_const]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA (hB0 0))
      change cubeIntegral d (fun v => ∏ j : Fin d, φ j.succ (v j)) ≤ _
      rw [cubeIntegral_prod d (fun j => φ j.succ)]
      exact Finset.prod_le_prod₀
        (fun j _ => intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hφ0 _ t))
        (fun j _ => hI j.succ)
    change |cubeQuadrature d m q-cubeIntegral d a| ≤ _
    calc
      |cubeQuadrature d m q-cubeIntegral d a| ≤
          |cubeQuadrature d m q-cubeIntegral d q| + |cubeIntegral d q-cubeIntegral d a| := by
        rw [show cubeQuadrature d m q-cubeIntegral d a =
          (cubeQuadrature d m q-cubeIntegral d q)+(cubeIntegral d q-cubeIntegral d a) by ring]
        exact abs_add_le _ _
      _ ≤ (64/(m : ℝ)^6)*(d*((A*B 0)*∏ j : Fin d, B j.succ))+
          (64/(m : ℝ)^6)*((A*B 0)*∏ j : Fin d, B j.succ) := add_le_add hfirst hsecond
      _ = (64/(m : ℝ)^6)*(((d+1:ℕ):ℝ)*(A*∏ j, B j)) := by
        rw [Fin.prod_univ_succ]
        push_cast
        ring

/-- Continuity and smoothness only on the cube. -/
theorem cubeQuadrature_sixth_order_envelope_on (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube d))
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1))
    (φ : Fin d → ℝ → ℝ) (hφ : ∀ j, Continuous (φ j)) (hφ0 : ∀ j t, 0 ≤ φ j t)
    (B : Fin d → ℝ) (hQ : ∀ j, quadrature m (φ j) ≤ B j)
    (hI : ∀ j, (∫ t in (0:ℝ)..1, φ j t) ≤ B j) {A : ℝ} (hA : 0 ≤ A)
    (hM : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u)) (Set.Icc (0 : ℝ) 1) t| ≤
        A*∏ j, φ j (Function.update v i t j)) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤ (64/(m : ℝ)^6)*(d*(A*∏ j, B j)) := by
  let g : (Fin d → ℝ) → ℝ := fun v => f (cubeClamp d v)
  have hgf : Set.EqOn g f (UnitCube d) := fun v hv => by
    dsimp only [g]
    rw [cubeClamp_eq hv]
  have hslice (i : Fin d) (v : Fin d → ℝ) (hv : v ∈ UnitCube d) :
      Set.EqOn (fun t => g (Function.update v i t))
        (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1) :=
    fun _ ht => hgf (update_mem_unitCube hv i ht)
  have hsg : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => g (Function.update v i t)) (Set.Icc (0 : ℝ) 1) :=
    fun i v hv => (hs i v hv).congr (hslice i v hv)
  have hMg : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => g (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ A*∏ j, φ j (Function.update v i t j) := by
    intro i v hv t ht
    rw [iteratedDerivWithin_congr (hslice i v hv) ht]
    exact hM i v hv t ht
  have h := cubeQuadrature_sixth_order_envelope d hm (continuous_cube_extension hf) hsg φ hφ hφ0
    B hQ hI hA hMg
  rw [cubeQuadrature_congr d m hm hgf, cubeIntegral_congr d hgf] at h
  exact h

end SphericalRiesz.Boundary
