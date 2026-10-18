import Riesz.CubeNodes

/-!
# Sixth-order quadrature on a physical box

Each side has its own positive width. The integral is an actual nested
interval integral, and the affine change of variables is proved by
recursion. Pure coordinate derivatives acquire their sixth powers of
the widths; no multivariable Taylor expansion is required.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

def BoxCell (d : ℕ) (a w : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {v | ∀ i, v i ∈ Set.Icc (a i) (a i+w i)}

def affineBox (d : ℕ) (a w v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => a i+w i*v i

theorem affineBox_mem {d : ℕ} (a w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    {v : Fin d → ℝ} (hv : v ∈ UnitCube d) : affineBox d a w v ∈ BoxCell d a w :=
  fun i => affine_mem_cell (a i) (w i) (hw i) (hv i)

theorem continuous_affineBox (d : ℕ) (a w : Fin d → ℝ) :
    Continuous (affineBox d a w) := by
  unfold affineBox
  fun_prop

theorem affineBox_cons (d : ℕ) (a w : Fin (d+1) → ℝ) (t : ℝ) (v : Fin d → ℝ) :
    affineBox (d+1) a w (Fin.cons t v) =
      Fin.cons (a 0+w 0*t) (affineBox d (Fin.tail a) (Fin.tail w) v) := by
  funext i
  exact Fin.cases (by simp [affineBox]) (fun j => by simp [affineBox, Fin.tail]) i

theorem affineBox_update (d : ℕ) (a w v : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    affineBox d a w (Function.update v i t) =
      Function.update (affineBox d a w v) i (a i+w i*t) := by
  funext j
  by_cases hji : j = i
  · subst j; simp [affineBox]
  · simp [affineBox, Function.update_of_ne hji]

def boxIntegral : (d : ℕ) → (Fin d → ℝ) → (Fin d → ℝ) → ((Fin d → ℝ) → ℝ) → ℝ
  | 0, _, _, f => f Fin.elim0
  | d+1, a, w, f => boxIntegral d (Fin.tail a) (Fin.tail w)
      (fun v => ∫ t in a 0..a 0+w 0, f (Fin.cons t v))

def boxQuadrature (d m : ℕ) (a w : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  (∏ i, w i)*cubeQuadrature d m (fun v => f (affineBox d a w v))

def boxNode (d m : ℕ) (a w : Fin d → ℝ) (v : Fin d → NodeIndex m) : Fin d → ℝ :=
  affineBox d a w (cubeNode d m v)

theorem boxNode_injective (d m : ℕ) (hm : 8 ≤ m) (a w : Fin d → ℝ)
    (hw : ∀ i, 0 < w i) : Function.Injective (boxNode d m a w) := by
  intro v u h
  funext i
  apply ruleNode_injective hm
  have hi := congrFun h i
  exact mul_left_cancel₀ (hw i).ne' (add_left_cancel hi)

theorem boxNode_mem_open (d m : ℕ) (hm : 8 ≤ m) (a w : Fin d → ℝ)
    (hw : ∀ i, 0 < w i) (v : Fin d → NodeIndex m) :
    ∀ i, boxNode d m a w v i ∈ Set.Ioo (a i) (a i+w i) := by
  intro i
  have ht := ruleNode_mem_unit hm (v i)
  change a i < a i+w i*ruleNode m (v i) ∧ a i+w i*ruleNode m (v i) < a i+w i
  constructor <;> nlinarith [hw i, ht.1, ht.2]

theorem boxQuadrature_as_node_sum (d m : ℕ) (a w : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) :
    boxQuadrature d m a w f =
      (∏ i, w i)*((∑ v : Fin d → NodeIndex m, f (boxNode d m a w v))/(m : ℝ)^d) := by
  rw [boxQuadrature, cubeQuadrature_as_node_sum]
  rfl

theorem cubeIntegral_mul_const (d : ℕ) (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    cubeIntegral d (fun v => c*f v) = c*cubeIntegral d f := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [cubeIntegral, intervalIntegral.integral_const_mul]
    exact ih _

/-- A change of variables for the actual nested interval integrals. -/
theorem boxIntegral_affine (d : ℕ) (a w : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) :
    boxIntegral d a w f = (∏ i, w i)*cubeIntegral d (fun v => f (affineBox d a w v)) := by
  induction d with
  | zero =>
    simp only [boxIntegral, cubeIntegral, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact congrArg f (Subsingleton.elim _ _)
  | succ d ih =>
    rw [boxIntegral, ih]
    have heq : (fun v : Fin d → ℝ => ∫ x in a 0..a 0+w 0,
        f (Fin.cons x (affineBox d (Fin.tail a) (Fin.tail w) v))) =
        (fun v => w 0*(∫ t in (0 : ℝ)..1,
          f (Fin.cons (a 0+w 0*t) (affineBox d (Fin.tail a) (Fin.tail w) v)))) := by
      funext v
      symm
      simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
        intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
          (fun x => f (Fin.cons x (affineBox d (Fin.tail a) (Fin.tail w) v))) (w 0) (a 0)
    rw [heq, cubeIntegral_mul_const, Fin.prod_univ_succ, cubeIntegral]
    simp only [affineBox_cons, Fin.tail]
    ring

/-- Local box continuity and pure sixth derivatives imply the scaled error. -/
theorem boxQuadrature_sixth_order_bound_on (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (a w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (BoxCell d a w))
    (hs : ∀ i v, v ∈ BoxCell d a w →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (a i) (a i+w i)))
    (M : Fin d → ℝ)
    (hM : ∀ i v, v ∈ BoxCell d a w → ∀ t ∈ Set.Icc (a i) (a i+w i),
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (a i) (a i+w i)) t| ≤ M i) :
    |boxQuadrature d m a w f-boxIntegral d a w f| ≤
      (64/(m : ℝ)^6)*(∏ i, w i)*(∑ i, (w i)^6*M i) := by
  let g : (Fin d → ℝ) → ℝ := fun v => f (affineBox d a w v)
  have hg : ContinuousOn g (UnitCube d) :=
    hf.comp (continuous_affineBox d a w).continuousOn (fun _ hv => affineBox_mem a w hw hv)
  have hsg : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => g (Function.update v i t)) (Set.Icc (0 : ℝ) 1) := by
    intro i v hv
    dsimp only [g]
    simp_rw [affineBox_update]
    exact (hs i _ (affineBox_mem a w hw hv)).comp (by fun_prop)
      (fun _ ht => affine_mem_cell (a i) (w i) (hw i) ht)
  have hMg : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun u => g (Function.update v i u))
        (Set.Icc (0 : ℝ) 1) t| ≤ (w i)^6*M i := by
    intro i v hv t ht
    dsimp only [g]
    simp_rw [affineBox_update]
    rw [iteratedDerivWithin_affine_cell (a i) (w i) (hw i)
      (hs i _ (affineBox_mem a w hw hv)) ht, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (w i)^6)]
    exact mul_le_mul_of_nonneg_left
      (hM i _ (affineBox_mem a w hw hv) _ (affine_mem_cell (a i) (w i) (hw i) ht)) (by positivity)
  have h := cubeQuadrature_sixth_order_bound_on d hm hg hsg (fun i => (w i)^6*M i) hMg
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [boxQuadrature, boxIntegral_affine, ← mul_sub, abs_mul, abs_of_pos hp]
  calc
    _ ≤ (∏ i, w i)*((64/(m : ℝ)^6)*(∑ i, (w i)^6*M i)) :=
      mul_le_mul_of_nonneg_left h hp.le
    _ = _ := by ring

/-- Equal side widths give the volume times the sixth-order width factor. -/
theorem boxQuadrature_uniform_sixth_order_bound_on (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (a : Fin d → ℝ) (w : ℝ) (hw : 0 < w)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (BoxCell d a (fun _ => w)))
    (hs : ∀ i v, v ∈ BoxCell d a (fun _ => w) →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (a i) (a i+w)))
    (M : Fin d → ℝ)
    (hM : ∀ i v, v ∈ BoxCell d a (fun _ => w) → ∀ t ∈ Set.Icc (a i) (a i+w),
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (a i) (a i+w)) t| ≤ M i) :
    |boxQuadrature d m a (fun _ => w) f-boxIntegral d a (fun _ => w) f| ≤
      (64/(m : ℝ)^6)*w^(d+6)*(∑ i, M i) := by
  have h := boxQuadrature_sixth_order_bound_on d hm a (fun _ => w) (fun _ => hw) hf hs M hM
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, pow_add, mul_assoc] using h

#print axioms boxIntegral_affine
#print axioms boxQuadrature_sixth_order_bound_on
#print axioms boxQuadrature_uniform_sixth_order_bound_on

end SphericalRiesz.Boundary
