import Riesz.BoundaryTwelveNodeGeometry
import Riesz.BoundaryTwelveL1Error
import Riesz.LocalizedQuadrature

/-! Twelfth-order tensor localization on the actual corrected grid. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz.Boundary

theorem twelveQuadrature_local_abs_bound {m : ℕ} (hm : 74 ≤ m)
    (c R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M)
    (hsupport : ∀ t ∈ Set.Icc (0:ℝ) 1, R < |t-c| → f t = 0) :
    |twelveQuadrature m f| ≤ (2*R+2/(m:ℝ))*M := by
  have h := twelveCubeQuadrature_local_abs_bound 1 hm (fun _ => c) R M hR hM
    (fun v => f (v 0)) (fun v hv => hbound _ (hv 0)) (by
      intro v hv hn
      apply hsupport _ (hv 0)
      apply lt_of_not_ge
      intro hh
      apply hn
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hh)
  simpa only [twelveCubeQuadrature, Fin.cons_zero, pow_one] using h

theorem twelveQuadrature_eq_zero_on {m : ℕ} (hm : 74 ≤ m) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, f t = 0) : twelveQuadrature m f = 0 := by
  apply abs_nonpos_iff.mp
  exact twelveQuadrature_abs_le hm (fun t ht => by rw [hf t ht]; norm_num)

/-- Tensor localization from the actual pure twelfth slice derivatives.
The function and those derivatives must vanish outside the stated box.
This is the input a smooth annular cutoff will have to satisfy. -/
theorem twelveCubeQuadrature_local_twelfth_order_bound (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    (c : Fin d → ℝ) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 12 (fun t => f (Function.update v i t)) (Set.Icc (0:ℝ) 1))
    (hbound : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t| ≤ M)
    (hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-c i| ≤ R) → f v = 0)
    (hDsupport : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      (¬ ∀ j, |Function.update v i t j-c j| ≤ R) →
      iteratedDerivWithin 12 (fun u => f (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t = 0) :
    |twelveCubeQuadrature d m f-cubeIntegral d f| ≤
      ((10^24)/(m:ℝ)^12)*(d:ℝ)*(2*R+2/(m:ℝ))^d*M := by
  let A := 2*R+2/(m:ℝ)
  let C := (10^24)/(m:ℝ)^12
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hRA : 2*R ≤ A := by
    dsimp only [A]
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg m)]
  induction d generalizing M with
  | zero => simp [twelveCubeQuadrature, cubeIntegral]
  | succ d ih =>
    let q : (Fin d → ℝ) → ℝ := fun v => twelveQuadrature m (fun t => f (Fin.cons t v))
    let a : (Fin d → ℝ) → ℝ := fun v => ∫ t in (0:ℝ)..1, f (Fin.cons t v)
    have hq : Continuous q := continuous_twelveQuadrature_param m (hf.comp (by fun_prop))
    have ha : Continuous a := continuous_unitIntegral_param (hf.comp (by fun_prop))
    have hsq : ∀ i v, v ∈ UnitCube d →
        ContDiffOn ℝ 12 (fun t => q (Function.update v i t)) (Set.Icc (0:ℝ) 1) := by
      intro i v hv
      apply contDiffOn_twelveQuadrature_param
      intro j
      simpa only [Nat.cast_ofNat, ← Fin.cons_update] using
        hs i.succ (Fin.cons (twelveRuleNode m j) v)
          (cons_mem_unitCube (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm j)) hv)
    have hsl (i : Fin d) (v : Fin d → ℝ) (hv : v ∈ UnitCube d) :
        ∀ j : TwelveNodeIndex m, ContDiffOn ℝ 12
          (fun u => f (Fin.cons (twelveRuleNode m j) (Function.update v i u)))
            (Set.Icc (0:ℝ) 1) := by
      intro j
      simpa only [← Fin.cons_update] using
        hs i.succ (Fin.cons (twelveRuleNode m j) v)
          (cons_mem_unitCube (Set.Ioo_subset_Icc_self (twelveRuleNode_mem_unit hm j)) hv)
    have hMq : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
        |iteratedDerivWithin 12 (fun u => q (Function.update v i u))
          (Set.Icc (0:ℝ) 1) t| ≤ A*M := by
      intro i v hv t ht
      dsimp only [q]
      rw [iteratedDerivWithin_twelveQuadrature_param m 12 (uniqueDiffOn_Icc (by norm_num)) (hsl i v hv) ht]
      apply twelveQuadrature_local_abs_bound hm (c 0) R M hR hM
      · intro z hz
        simpa only [← Fin.cons_update] using
          hbound i.succ (Fin.cons z v) (cons_mem_unitCube hz hv) t ht
      · intro z hz hn
        have hn' : ¬ ∀ j, |Function.update (Fin.cons z v : Fin (d+1) → ℝ) i.succ t j-c j| ≤ R := by
          intro hh
          have h := hh 0
          simp only [← Fin.cons_update, Fin.cons_zero] at h
          linarith
        simpa only [← Fin.cons_update] using
          hDsupport i.succ (Fin.cons z v) (cons_mem_unitCube hz hv) t ht hn'
    have hqzero : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-c i.succ| ≤ R) → q v = 0 := by
      intro v hv hn
      apply twelveQuadrature_eq_zero_on hm
      intro z hz
      apply hsupport _ (cons_mem_unitCube hz hv)
      intro hh
      apply hn
      intro i
      simpa only [Fin.cons_succ] using hh i.succ
    have hDqzero : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
        (¬ ∀ j, |Function.update v i t j-c j.succ| ≤ R) →
        iteratedDerivWithin 12 (fun u => q (Function.update v i u))
          (Set.Icc (0:ℝ) 1) t = 0 := by
      intro i v hv t ht hn
      dsimp only [q]
      rw [iteratedDerivWithin_twelveQuadrature_param m 12 (uniqueDiffOn_Icc (by norm_num)) (hsl i v hv) ht]
      apply twelveQuadrature_eq_zero_on hm
      intro z hz
      have hn' : ¬ ∀ j, |Function.update (Fin.cons z v : Fin (d+1) → ℝ) i.succ t j-c j| ≤ R := by
        intro hh
        apply hn
        intro j
        simpa only [← Fin.cons_update, Fin.cons_succ] using hh j.succ
      simpa only [← Fin.cons_update] using
        hDsupport i.succ (Fin.cons z v) (cons_mem_unitCube hz hv) t ht hn'
    have hfirst := ih (fun i => c i.succ) (A*M) (mul_nonneg hA hM)
      hq hsq hMq hqzero hDqzero
    have hhead : ∀ v ∈ UnitCube d, |q v-a v| ≤ C*(2*R*M) := by
      intro v hv
      have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
      have hsf : ContDiffOn ℝ 12 (fun t => f (Fin.cons t v)) (Set.Icc (0:ℝ) 1) := by
        simpa only [Fin.update_cons_zero] using hs 0 (Fin.cons 0 v) (cons_mem_unitCube h0 hv)
      have hl := twelveQuadrature_twelfth_order_l1_bound_on hm hsf
      have hi : (∫ t in (0:ℝ)..1,
          |iteratedDerivWithin 12 (fun u => f (Fin.cons u v)) (Set.Icc (0:ℝ) 1) t|) ≤ 2*R*M := by
        apply (le_abs_self _).trans
        apply unitIntegral_local_abs_bound (c 0) R M hR hM
        · intro t ht
          rw [abs_abs]
          simpa only [Fin.update_cons_zero] using
            hbound 0 (Fin.cons 0 v) (cons_mem_unitCube h0 hv) t ht
        · intro t ht hn
          have hn' : ¬ ∀ j, |Function.update (Fin.cons 0 v : Fin (d+1) → ℝ) (0 : Fin (d+1)) t j-c j| ≤ R := by
            intro hh
            have h := hh 0
            simp only [Function.update_self] at h
            linarith
          have hz := hDsupport 0 (Fin.cons 0 v) (cons_mem_unitCube h0 hv) t ht hn'
          simpa only [Fin.update_cons_zero, hz, abs_zero] using congrArg abs hz
      exact hl.trans (mul_le_mul_of_nonneg_left hi hC)
    have hsecond : |cubeIntegral d q-cubeIntegral d a| ≤ C*A^(d+1)*M := by
      rw [← cubeIntegral_sub d q a hq ha]
      have hb : |cubeIntegral d (fun v => q v-a v)| ≤ (2*R)^d*(C*(2*R*M)) := by
        apply cubeIntegral_local_abs_bound d (fun i => c i.succ) R (C*(2*R*M)) hR (by positivity)
          (fun v => q v-a v) hhead
        intro v hv hn
        have hzq := hqzero v hv hn
        have hza : a v = 0 := by
          apply unitIntegral_eq_zero_on
          intro z hz
          apply hsupport _ (cons_mem_unitCube hz hv)
          intro hh
          apply hn
          intro i
          simpa only [Fin.cons_succ] using hh i.succ
        rw [hzq, hza, sub_self]
      calc
        _ ≤ (2*R)^d*(C*(2*R*M)) := hb
        _ = C*(2*R)^(d+1)*M := by rw [pow_succ]; ring
        _ ≤ C*A^(d+1)*M := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRA (d+1)) hC) hM
    change |twelveCubeQuadrature d m q-cubeIntegral d a| ≤ _
    calc
      _ ≤ |twelveCubeQuadrature d m q-cubeIntegral d q|+|cubeIntegral d q-cubeIntegral d a| := by
        rw [show twelveCubeQuadrature d m q-cubeIntegral d a =
          (twelveCubeQuadrature d m q-cubeIntegral d q)+(cubeIntegral d q-cubeIntegral d a) by ring]
        exact abs_add_le _ _
      _ ≤ C*(d:ℝ)*A^d*(A*M)+C*A^(d+1)*M := add_le_add hfirst hsecond
      _ = _ := by change _ = C*((d+1:ℕ):ℝ)*A^(d+1)*M; push_cast; rw [pow_succ]; ring


end SphericalRiesz.Boundary
