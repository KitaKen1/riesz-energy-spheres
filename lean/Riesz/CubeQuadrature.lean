import Riesz.LocalCellQuadrature
import Riesz.TensorQuadrature
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quadrature on a cube in any finite dimension

The first coordinate is integrated/averaged first. The recursive error
proof averages finitely many smooth slices and then uses the norm-one
bound for the remaining integrals. It does not differentiate an integral
or request mixed high derivatives.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def UnitCube (d : ℕ) : Set (Fin d → ℝ) :=
  {v | ∀ i, v i ∈ Set.Icc (0 : ℝ) 1}

theorem cons_mem_unitCube {d : ℕ} {t : ℝ} {v : Fin d → ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ UnitCube d) :
    Fin.cons t v ∈ UnitCube (d+1) := by
  intro i
  exact Fin.cases (by simpa using ht) (fun j => by simpa using hv j) i

theorem update_mem_unitCube {d : ℕ} {v : Fin d → ℝ} (hv : v ∈ UnitCube d)
    (i : Fin d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Function.update v i t ∈ UnitCube d := by
  intro j
  by_cases hji : j = i
  · subst j; simpa using ht
  · simpa [Function.update_of_ne hji] using hv j

def cubeQuadrature : (d : ℕ) → ℕ → ((Fin d → ℝ) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | d+1, m, f => cubeQuadrature d m (fun v => quadrature m (fun t => f (Fin.cons t v)))

def cubeIntegral : (d : ℕ) → ((Fin d → ℝ) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | d+1, f => cubeIntegral d (fun v => ∫ t in (0 : ℝ)..1, f (Fin.cons t v))

theorem cubeIntegral_abs_le (d : ℕ) (f : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ v ∈ UnitCube d, |f v| ≤ M) : |cubeIntegral d f| ≤ M := by
  induction d with
  | zero => exact hM Fin.elim0 (fun i => Fin.elim0 i)
  | succ d ih =>
    apply ih
    intro v hv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := fun t => f (Fin.cons t v)) (C := M) (by
        intro t ht
        rw [Real.norm_eq_abs]
        exact hM _ (cons_mem_unitCube ⟨by simpa using ht.1.le, by simpa using ht.2⟩ hv))
    simpa using h

theorem cubeQuadrature_abs_le (d m : ℕ) (hm : 8 ≤ m) (f : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ v ∈ UnitCube d, |f v| ≤ M) : |cubeQuadrature d m f| ≤ M := by
  induction d with
  | zero => exact hM Fin.elim0 (fun i => Fin.elim0 i)
  | succ d ih =>
    apply ih
    intro v hv
    exact quadrature_abs_le hm (fun t ht => hM _ (cons_mem_unitCube ht hv))

theorem cubeQuadrature_sub (d m : ℕ) (f g : (Fin d → ℝ) → ℝ) :
    cubeQuadrature d m (fun v => f v-g v) = cubeQuadrature d m f-cubeQuadrature d m g := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [cubeQuadrature, quadrature_sub]; exact ih _ _

theorem cubeQuadrature_congr (d m : ℕ) {f g : (Fin d → ℝ) → ℝ} (hm : 8 ≤ m)
    (hfg : Set.EqOn f g (UnitCube d)) : cubeQuadrature d m f = cubeQuadrature d m g := by
  induction d with
  | zero => exact hfg (fun i => Fin.elim0 i)
  | succ d ih =>
    apply ih
    intro v hv
    change quadrature m (fun t => f (Fin.cons t v)) = quadrature m (fun t => g (Fin.cons t v))
    rw [quadrature_as_node_sum, quadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hfg (cons_mem_unitCube (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm i)) hv)

theorem cubeIntegral_congr (d : ℕ) {f g : (Fin d → ℝ) → ℝ}
    (hfg : Set.EqOn f g (UnitCube d)) : cubeIntegral d f = cubeIntegral d g := by
  induction d with
  | zero => exact hfg (fun i => Fin.elim0 i)
  | succ d ih =>
    apply ih
    intro v hv
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hfg (cons_mem_unitCube ht hv)

theorem continuous_unitIntegral_param {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {F : X → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => ∫ t in (0 : ℝ)..1, F x t) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ)) hF
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  simpa only [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

theorem continuous_cubeIntegral_param {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] (d : ℕ)
    {F : X → (Fin d → ℝ) → ℝ} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => cubeIntegral d (F x)) := by
  induction d with
  | zero => exact hF.comp (continuous_id.prodMk continuous_const)
  | succ d ih =>
    apply ih
    apply continuous_unitIntegral_param
    have hc : Continuous (fun p : (X × (Fin d → ℝ)) × ℝ =>
        (p.1.1, (Fin.cons p.2 p.1.2 : Fin (d+1) → ℝ))) := by fun_prop
    exact hF.comp hc

theorem cubeIntegral_sub (d : ℕ) (f g : (Fin d → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    cubeIntegral d (fun v => f v-g v) = cubeIntegral d f-cubeIntegral d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hcf : Continuous (fun v : Fin d → ℝ => ∫ t in (0 : ℝ)..1, f (Fin.cons t v)) := by
      apply continuous_unitIntegral_param
      exact hf.comp (by fun_prop)
    have hcg : Continuous (fun v : Fin d → ℝ => ∫ t in (0 : ℝ)..1, g (Fin.cons t v)) := by
      apply continuous_unitIntegral_param
      exact hg.comp (by fun_prop)
    have heq : (fun v : Fin d → ℝ => ∫ t in (0 : ℝ)..1, f (Fin.cons t v)-g (Fin.cons t v)) =
        (fun v => (∫ t in (0 : ℝ)..1, f (Fin.cons t v)) - ∫ t in (0 : ℝ)..1, g (Fin.cons t v)) := by
      funext v
      exact intervalIntegral.integral_sub
        ((hf.comp (by fun_prop)).intervalIntegrable 0 1)
        ((hg.comp (by fun_prop)).intervalIntegrable 0 1)
    simp only [cubeIntegral]
    rw [heq]
    exact ih _ _ hcf hcg

theorem continuous_quadrature_param {X : Type*} [TopologicalSpace X]
    (m : ℕ) {F : X → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => quadrature m (F x)) := by
  simp only [quadrature_as_node_sum]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact hF.comp (continuous_id.prodMk continuous_const)

theorem contDiffOn_quadrature_param (m n : ℕ) {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ i : NodeIndex m, ContDiffOn ℝ n (fun x => F x (ruleNode m i)) s) :
    ContDiffOn ℝ n (fun x => quadrature m (F x)) s := by
  simp only [quadrature_as_node_sum]
  exact (ContDiffOn.sum (fun i _ => hF i)).div_const _

theorem iteratedDerivWithin_quadrature_param (m n : ℕ) {F : ℝ → ℝ → ℝ}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hF : ∀ i : NodeIndex m, ContDiffOn ℝ n (fun x => F x (ruleNode m i)) s)
    {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (fun u => quadrature m (F u)) s x =
      quadrature m (fun z => iteratedDerivWithin n (fun u => F u z) s x) := by
  simp only [quadrature_as_node_sum, div_eq_inv_mul]
  rw [iteratedDerivWithin_const_mul_field]
  congr 1
  exact iteratedDerivWithin_fun_sum hx hs (fun i _ => hF i x hx)

/-- Pure sixth slice derivatives suffice in every finite dimension. -/
theorem cubeQuadrature_sixth_order_bound (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1))
    (M : Fin d → ℝ)
    (hM : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ M i) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤ (64/(m : ℝ)^6)*(∑ i, M i) := by
  induction d with
  | zero => simp [cubeQuadrature, cubeIntegral]
  | succ d ih =>
    let q : (Fin d → ℝ) → ℝ := fun v => quadrature m (fun t => f (Fin.cons t v))
    let a : (Fin d → ℝ) → ℝ := fun v => ∫ t in (0 : ℝ)..1, f (Fin.cons t v)
    have hq : Continuous q := continuous_quadrature_param m (hf.comp (by fun_prop))
    have ha : Continuous a := continuous_unitIntegral_param (hf.comp (by fun_prop))
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
          (Set.Icc (0 : ℝ) 1) t| ≤ M i.succ := by
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
      apply quadrature_abs_le hm
      intro z hz
      simpa only [← Fin.cons_update] using
        hM i.succ (Fin.cons z v) (cons_mem_unitCube hz hv) t ht
    have hfirst := ih hq hsq (fun i => M i.succ) hMq
    have hhead : ∀ v ∈ UnitCube d, |q v-a v| ≤ (64/(m : ℝ)^6)*M 0 := by
      intro v hv
      have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      apply quadrature_sixth_order_bound_on hm
      · simpa only [Fin.update_cons_zero] using
          hs 0 (Fin.cons 0 v) (cons_mem_unitCube hz hv)
      · intro t ht
        simpa only [Fin.update_cons_zero] using
          hM 0 (Fin.cons 0 v) (cons_mem_unitCube hz hv) t ht
    have hsecond : |cubeIntegral d q-cubeIntegral d a| ≤ (64/(m : ℝ)^6)*M 0 := by
      rw [← cubeIntegral_sub d q a hq ha]
      exact cubeIntegral_abs_le d _ _ hhead
    change |cubeQuadrature d m q-cubeIntegral d a| ≤ _
    calc
      |cubeQuadrature d m q-cubeIntegral d a| ≤
          |cubeQuadrature d m q-cubeIntegral d q| + |cubeIntegral d q-cubeIntegral d a| := by
        rw [show cubeQuadrature d m q-cubeIntegral d a =
          (cubeQuadrature d m q-cubeIntegral d q)+(cubeIntegral d q-cubeIntegral d a) by ring]
        exact abs_add_le _ _
      _ ≤ (64/(m : ℝ)^6)*(∑ i : Fin d, M i.succ)+(64/(m : ℝ)^6)*M 0 := add_le_add hfirst hsecond
      _ = (64/(m : ℝ)^6)*(∑ i, M i) := by rw [Fin.sum_univ_succ]; ring

def cubeClamp (d : ℕ) (v : Fin d → ℝ) : Fin d → ℝ := fun i => unitClamp (v i)

theorem cubeClamp_mem (d : ℕ) (v : Fin d → ℝ) : cubeClamp d v ∈ UnitCube d :=
  fun i => unitClamp_mem (v i)

theorem cubeClamp_eq {d : ℕ} {v : Fin d → ℝ} (hv : v ∈ UnitCube d) : cubeClamp d v = v := by
  funext i
  exact unitClamp_eq (hv i)

theorem continuous_cubeClamp (d : ℕ) : Continuous (cubeClamp d) :=
  continuous_pi (fun i => continuous_unitClamp.comp (continuous_apply i))

theorem continuous_cube_extension {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContinuousOn f (UnitCube d)) : Continuous (fun v => f (cubeClamp d v)) :=
  hf.comp_continuous (continuous_cubeClamp d) (cubeClamp_mem d)

/-- All continuity and smoothness assumptions are local to the cube. -/
theorem cubeQuadrature_sixth_order_bound_on (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube d))
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1))
    (M : Fin d → ℝ)
    (hM : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ M i) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤ (64/(m : ℝ)^6)*(∑ i, M i) := by
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
        (Set.Icc (0 : ℝ) 1) t| ≤ M i := by
    intro i v hv t ht
    rw [iteratedDerivWithin_congr (hslice i v hv) ht]
    exact hM i v hv t ht
  have h := cubeQuadrature_sixth_order_bound d hm (continuous_cube_extension hf) hsg M hMg
  rw [cubeQuadrature_congr d m hm hgf, cubeIntegral_congr d hgf] at h
  exact h

#print axioms iteratedDerivWithin_quadrature_param
#print axioms cubeQuadrature_sixth_order_bound_on

end SphericalRiesz.Boundary
