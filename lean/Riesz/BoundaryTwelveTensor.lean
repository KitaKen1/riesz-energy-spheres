import Riesz.BoundaryTwelveLocalError
import Riesz.CubeQuadrature

/-! Actual tensor points and twelfth-order error in any finite dimension.
This reuses the original pure-slice induction without mixed derivatives. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz.Boundary

theorem twelveQuadrature_const {m : ℕ} (hm : 74 ≤ m) (c : ℝ) :
    twelveQuadrature m (fun _ => c) = c := by
  have h : twelveQuadrature m (fun _ => (1 : ℝ)) = 1 := by
    simpa using twelveQuadrature_monomial hm (0 : Fin 12)
  simpa using (twelveQuadrature_mul_const m c (fun _ => 1)).trans (by rw [h, mul_one])

theorem twelveQuadrature_sub (m : ℕ) (f g : ℝ → ℝ) :
    twelveQuadrature m (fun x => f x-g x) = twelveQuadrature m f-twelveQuadrature m g := by
  simp only [twelveQuadrature, Finset.sum_sub_distrib]
  ring

theorem twelveQuadrature_mono {m : ℕ} (hm : 74 ≤ m) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ g x) : twelveQuadrature m f ≤ twelveQuadrature m g := by
  rw [twelveQuadrature_as_node_sum, twelveQuadrature_as_node_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  exact h _ (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm i))

theorem twelveQuadrature_abs_le {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) : |twelveQuadrature m f| ≤ M := by
  apply abs_le.mpr
  constructor
  · have hl := twelveQuadrature_mono hm (f := fun _ => -M) (g := f)
      (fun x hx => (abs_le.mp (h x hx)).1)
    simpa only [twelveQuadrature_const hm] using hl
  · have hu := twelveQuadrature_mono hm (f := f) (g := fun _ => M)
      (fun x hx => (abs_le.mp (h x hx)).2)
    simpa only [twelveQuadrature_const hm] using hu

def twelveCubeQuadrature : (d : ℕ) → ℕ → ((Fin d → ℝ) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | d+1, m, f => twelveCubeQuadrature d m (fun v => twelveQuadrature m (fun t => f (Fin.cons t v)))

theorem twelveCubeQuadrature_abs_le (d m : ℕ) (hm : 74 ≤ m) (f : (Fin d → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ v ∈ UnitCube d, |f v| ≤ M) : |twelveCubeQuadrature d m f| ≤ M := by
  induction d with
  | zero => exact hM Fin.elim0 (fun i => Fin.elim0 i)
  | succ d ih =>
    apply ih
    intro v hv
    exact twelveQuadrature_abs_le hm (fun t ht => hM _ (cons_mem_unitCube ht hv))

theorem twelveCubeQuadrature_sub (d m : ℕ) (f g : (Fin d → ℝ) → ℝ) :
    twelveCubeQuadrature d m (fun v => f v-g v) = twelveCubeQuadrature d m f-twelveCubeQuadrature d m g := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [twelveCubeQuadrature, twelveQuadrature_sub]; exact ih _ _

theorem twelveCubeQuadrature_congr (d m : ℕ) {f g : (Fin d → ℝ) → ℝ} (hm : 74 ≤ m)
    (hfg : Set.EqOn f g (UnitCube d)) : twelveCubeQuadrature d m f = twelveCubeQuadrature d m g := by
  induction d with
  | zero => exact hfg (fun i => Fin.elim0 i)
  | succ d ih =>
    apply ih
    intro v hv
    change twelveQuadrature m (fun t => f (Fin.cons t v)) = twelveQuadrature m (fun t => g (Fin.cons t v))
    rw [twelveQuadrature_as_node_sum, twelveQuadrature_as_node_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hfg (cons_mem_unitCube (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm i)) hv)

theorem continuous_twelveQuadrature_param {X : Type*} [TopologicalSpace X]
    (m : ℕ) {F : X → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => twelveQuadrature m (F x)) := by
  simp only [twelveQuadrature_as_node_sum]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact hF.comp (continuous_id.prodMk continuous_const)

theorem contDiffOn_twelveQuadrature_param (m n : ℕ) {F : ℝ → ℝ → ℝ} {s : Set ℝ}
    (hF : ∀ i : TwelveNodeIndex m, ContDiffOn ℝ n (fun x => F x (twelveRuleNode m i)) s) :
    ContDiffOn ℝ n (fun x => twelveQuadrature m (F x)) s := by
  simp only [twelveQuadrature_as_node_sum]
  exact (ContDiffOn.sum (fun i _ => hF i)).div_const _

theorem iteratedDerivWithin_twelveQuadrature_param (m n : ℕ) {F : ℝ → ℝ → ℝ}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hF : ∀ i : TwelveNodeIndex m, ContDiffOn ℝ n (fun x => F x (twelveRuleNode m i)) s)
    {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (fun u => twelveQuadrature m (F u)) s x =
      twelveQuadrature m (fun z => iteratedDerivWithin n (fun u => F u z) s x) := by
  simp only [twelveQuadrature_as_node_sum, div_eq_inv_mul]
  rw [iteratedDerivWithin_const_mul_field]
  congr 1
  exact iteratedDerivWithin_fun_sum hx hs (fun i _ => hF i x hx)

/-- Pure twelfth slice derivatives suffice in every finite dimension. -/
theorem twelveCubeQuadrature_twelfth_order_bound (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 12 (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1))
    (M : Fin d → ℝ)
    (hM : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ M i) :
    |twelveCubeQuadrature d m f-cubeIntegral d f| ≤ ((10^24)/(m : ℝ)^12)*(∑ i, M i) := by
  induction d with
  | zero => simp [twelveCubeQuadrature, cubeIntegral]
  | succ d ih =>
    let q : (Fin d → ℝ) → ℝ := fun v => twelveQuadrature m (fun t => f (Fin.cons t v))
    let a : (Fin d → ℝ) → ℝ := fun v => ∫ t in (0 : ℝ)..1, f (Fin.cons t v)
    have hq : Continuous q := continuous_twelveQuadrature_param m (hf.comp (by fun_prop))
    have ha : Continuous a := continuous_unitIntegral_param (hf.comp (by fun_prop))
    have hsq : ∀ i v, v ∈ UnitCube d →
        ContDiffOn ℝ 12 (fun t => q (Function.update v i t)) (Set.Icc (0 : ℝ) 1) := by
      intro i v hv
      apply contDiffOn_twelveQuadrature_param
      intro j
      simpa only [Nat.cast_ofNat, ← Fin.cons_update] using
        hs i.succ (Fin.cons (twelveRuleNode m j) v)
          (cons_mem_unitCube (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm j)) hv)
    have hMq : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDerivWithin 12 (fun u => q (Function.update v i u))
          (Set.Icc (0 : ℝ) 1) t| ≤ M i.succ := by
      intro i v hv t ht
      have hsl : ∀ j : TwelveNodeIndex m, ContDiffOn ℝ 12
          (fun u => f (Fin.cons (twelveRuleNode m j) (Function.update v i u)))
            (Set.Icc (0 : ℝ) 1) := by
        intro j
        simpa only [← Fin.cons_update] using
          hs i.succ (Fin.cons (twelveRuleNode m j) v)
            (cons_mem_unitCube (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm j)) hv)
      dsimp only [q]
      rw [iteratedDerivWithin_twelveQuadrature_param m 12 (uniqueDiffOn_Icc (by norm_num)) hsl ht]
      apply twelveQuadrature_abs_le hm
      intro z hz
      simpa only [← Fin.cons_update] using
        hM i.succ (Fin.cons z v) (cons_mem_unitCube hz hv) t ht
    have hfirst := ih hq hsq (fun i => M i.succ) hMq
    have hhead : ∀ v ∈ UnitCube d, |q v-a v| ≤ ((10^24)/(m : ℝ)^12)*M 0 := by
      intro v hv
      have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      apply twelveQuadrature_twelfth_order_bound_on hm
      · simpa only [Fin.update_cons_zero] using
          hs 0 (Fin.cons 0 v) (cons_mem_unitCube hz hv)
      · intro t ht
        simpa only [Fin.update_cons_zero] using
          hM 0 (Fin.cons 0 v) (cons_mem_unitCube hz hv) t ht
    have hsecond : |cubeIntegral d q-cubeIntegral d a| ≤ ((10^24)/(m : ℝ)^12)*M 0 := by
      rw [← cubeIntegral_sub d q a hq ha]
      exact cubeIntegral_abs_le d _ _ hhead
    change |twelveCubeQuadrature d m q-cubeIntegral d a| ≤ _
    calc
      |twelveCubeQuadrature d m q-cubeIntegral d a| ≤
          |twelveCubeQuadrature d m q-cubeIntegral d q| + |cubeIntegral d q-cubeIntegral d a| := by
        rw [show twelveCubeQuadrature d m q-cubeIntegral d a =
          (twelveCubeQuadrature d m q-cubeIntegral d q)+(cubeIntegral d q-cubeIntegral d a) by ring]
        exact abs_add_le _ _
      _ ≤ ((10^24)/(m : ℝ)^12)*(∑ i : Fin d, M i.succ)+((10^24)/(m : ℝ)^12)*M 0 := add_le_add hfirst hsecond
      _ = ((10^24)/(m : ℝ)^12)*(∑ i, M i) := by rw [Fin.sum_univ_succ]; ring

theorem twelveCubeQuadrature_twelfth_order_bound_on (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube d))
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 12 (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1))
    (M : Fin d → ℝ)
    (hM : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ M i) :
    |twelveCubeQuadrature d m f-cubeIntegral d f| ≤ ((10^24)/(m : ℝ)^12)*(∑ i, M i) := by
  let g : (Fin d → ℝ) → ℝ := fun v => f (cubeClamp d v)
  have hgf : Set.EqOn g f (UnitCube d) := fun v hv => by
    dsimp only [g]
    rw [cubeClamp_eq hv]
  have hslice (i : Fin d) (v : Fin d → ℝ) (hv : v ∈ UnitCube d) :
      Set.EqOn (fun t => g (Function.update v i t))
        (fun t => f (Function.update v i t)) (Set.Icc (0 : ℝ) 1) :=
    fun _ ht => hgf (update_mem_unitCube hv i ht)
  have hsg : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 12 (fun t => g (Function.update v i t)) (Set.Icc (0 : ℝ) 1) :=
    fun i v hv => (hs i v hv).congr (hslice i v hv)
  have hMg : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 12 (fun u => g (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ M i := by
    intro i v hv t ht
    rw [iteratedDerivWithin_congr (hslice i v hv) ht]
    exact hM i v hv t ht
  have h := twelveCubeQuadrature_twelfth_order_bound d hm (continuous_cube_extension hf) hsg M hMg
  rw [twelveCubeQuadrature_congr d m hm hgf, cubeIntegral_congr d hgf] at h
  exact h


def twelveCubeNode (d m : ℕ) (v : Fin d → TwelveNodeIndex m) : Fin d → ℝ :=
  fun i => twelveRuleNode m (v i)

theorem twelveCubeNode_card (d m : ℕ) (hm : 74 ≤ m) :
    Fintype.card (Fin d → TwelveNodeIndex m) = m^d := by
  rw [Fintype.card_pi_const, twelveNodeIndex_card hm]

theorem twelveCubeNode_injective (d m : ℕ) (hm : 74 ≤ m) : Function.Injective (twelveCubeNode d m) := by
  intro v u h
  funext i
  exact twelveRuleNode_injective hm (congrFun h i)

theorem twelveCubeNode_mem_open (d m : ℕ) (hm : 74 ≤ m) (v : Fin d → TwelveNodeIndex m) :
    ∀ i, twelveCubeNode d m v i ∈ Set.Ioo (0 : ℝ) 1 :=
  fun i => twelveRuleNode_mem_unit hm (v i)

theorem twelveCubeNode_cons (d m : ℕ) (j : TwelveNodeIndex m) (v : Fin d → TwelveNodeIndex m) :
    twelveCubeNode (d+1) m (Fin.cons j v) = Fin.cons (twelveRuleNode m j) (twelveCubeNode d m v) := by
  funext i
  exact Fin.cases (by simp [twelveCubeNode]) (fun k => by simp [twelveCubeNode]) i

theorem twelveCubeQuadrature_as_node_sum (d m : ℕ) (f : (Fin d → ℝ) → ℝ) :
    twelveCubeQuadrature d m f =
      (∑ v : Fin d → TwelveNodeIndex m, f (twelveCubeNode d m v))/(m : ℝ)^d := by
  induction d with
  | zero =>
    have h : ∀ v : Fin 0 → TwelveNodeIndex m, twelveCubeNode 0 m v = Fin.elim0 :=
      fun _ => Subsingleton.elim _ _
    simp [twelveCubeQuadrature, h]
  | succ d ih =>
    rw [twelveCubeQuadrature, ih]
    simp_rw [twelveQuadrature_as_node_sum]
    rw [← Finset.sum_div, div_div, ← pow_succ']
    congr 1
    have heq := (Fin.consEquiv (fun _ : Fin (d+1) => TwelveNodeIndex m)).sum_comp
      (fun v => f (twelveCubeNode (d+1) m v))
    have hsum : (∑ v : Fin (d+1) → TwelveNodeIndex m, f (twelveCubeNode (d+1) m v)) =
        ∑ j : TwelveNodeIndex m, ∑ v : Fin d → TwelveNodeIndex m,
          f (Fin.cons (twelveRuleNode m j) (twelveCubeNode d m v)) := by
      simpa only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, twelveCubeNode_cons] using heq.symm
    rw [hsum, Finset.sum_comm]


end SphericalRiesz.Boundary
