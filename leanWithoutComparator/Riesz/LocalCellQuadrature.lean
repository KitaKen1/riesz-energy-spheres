import Riesz.LocalQuadrature
import Riesz.CellQuadrature

/-!
Affine rescaling with one-sided derivatives on a closed physical cell.
The chain-rule induction generalizes the argument for
`iteratedDerivWithin_comp_const_smul` in mathlib's IteratedDeriv/Lemmas.lean
(Apache-2.0; authors Chris Birkbeck and Ruben Van de Velde).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem affine_mem_cell (a w : ℝ) (hw : 0 < w) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : a+w*t ∈ Set.Icc a (a+w) := by
  constructor <;> nlinarith [ht.1, ht.2]

theorem iteratedDerivWithin_affine_cell {n : ℕ} {f : ℝ → ℝ} (a w : ℝ) (hw : 0 < w)
    (hf : ContDiffOn ℝ n f (Set.Icc a (a+w))) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin n (fun x => f (a+w*x)) (Set.Icc (0 : ℝ) 1) t =
      w^n*iteratedDerivWithin n f (Set.Icc a (a+w)) (a+w*t) := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hc : UniqueDiffOn ℝ (Set.Icc a (a+w)) := uniqueDiffOn_Icc (by linarith)
  have hmap : Set.MapsTo (fun x => a+w*x) (Set.Icc (0 : ℝ) 1) (Set.Icc a (a+w)) :=
    fun _ hx => affine_mem_cell a w hw hx
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have heq : Set.EqOn
        (iteratedDerivWithin n (fun x => f (a+w*x)) (Set.Icc (0 : ℝ) 1))
        (fun x => w^n*iteratedDerivWithin n f (Set.Icc a (a+w)) (a+w*x))
        (Set.Icc (0 : ℝ) 1) := fun x hx => ih hf.of_succ hx
    have hg : DifferentiableWithinAt ℝ (iteratedDerivWithin n f (Set.Icc a (a+w)))
        (Set.Icc a (a+w)) (a+w*t) :=
      hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast n.lt_succ_self) hc _ (hmap ht)
    have ha : HasDerivWithinAt (fun x : ℝ => a+w*x) w (Set.Icc (0 : ℝ) 1) t := by
      simpa using ((hasDerivWithinAt_id t (Set.Icc (0 : ℝ) 1)).const_mul w).const_add a
    have hcomp : DifferentiableWithinAt ℝ
        (fun x => iteratedDerivWithin n f (Set.Icc a (a+w)) (a+w*x))
        (Set.Icc (0 : ℝ) 1) t := by
      rw [← Function.comp_def]
      exact DifferentiableWithinAt.comp t hg ha.differentiableWithinAt hmap
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (ih hf.of_succ ht),
      derivWithin_const_mul (w^n) hcomp, ← Function.comp_def,
      derivWithin.scomp t hg ha.differentiableWithinAt hmap, ha.derivWithin (hu t ht),
      ← iteratedDerivWithin_succ]
    simp only [smul_eq_mul]
    ring

theorem quadrature_cell_sixth_order_bound_on {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (a w : ℝ) (hw : 0 < w) (hf : ContDiffOn ℝ 6 f (Set.Icc a (a+w))) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc a (a+w),
      |iteratedDerivWithin 6 f (Set.Icc a (a+w)) x| ≤ M) :
    |w*quadrature m (fun t => f (a+w*t)) - ∫ x in a..a+w, f x| ≤
      (64/(m : ℝ)^6)*w^7*M := by
  have hmap : Set.MapsTo (fun x => a+w*x) (Set.Icc (0 : ℝ) 1) (Set.Icc a (a+w)) :=
    fun _ hx => affine_mem_cell a w hw hx
  have hg : ContDiffOn ℝ 6 (fun t => f (a+w*t)) (Set.Icc (0 : ℝ) 1) :=
    hf.comp (by fun_prop) hmap
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin 6 (fun x => f (a+w*x)) (Set.Icc (0 : ℝ) 1) t| ≤ w^6*M := by
    intro t ht
    rw [iteratedDerivWithin_affine_cell a w hw hf ht, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ w^6)]
    exact mul_le_mul_of_nonneg_left (hM _ (hmap ht)) (by positivity)
  have h := quadrature_sixth_order_bound_on hm hg (w^6*M) hb
  have hi : (∫ x in a..a+w, f x) = w*(∫ t in (0 : ℝ)..1, f (a+w*t)) := by
    symm
    simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add] using
      intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f w a
  rw [hi, ← mul_sub, abs_mul, abs_of_pos hw]
  calc
    _ ≤ w*((64/(m : ℝ)^6)*(w^6*M)) := mul_le_mul_of_nonneg_left h hw.le
    _ = (64/(m : ℝ)^6)*w^7*M := by ring

#print axioms iteratedDerivWithin_affine_cell
#print axioms quadrature_cell_sixth_order_bound_on

end SphericalRiesz.Boundary
