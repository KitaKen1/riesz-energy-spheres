import Riesz.NodeCounting
import Riesz.L1Quadrature

/-!
# Localized integration and quadrature on the original grid

The support assumptions below are about the actual function and its
actual slice derivatives. Cutoff construction for the Riesz kernel is
a separate obligation. These lemmas do not introduce new interior nodes.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SphericalRiesz.Boundary

theorem unitIntegral_local_abs_bound (c R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M)
    (hsupport : ∀ t ∈ Set.Icc (0:ℝ) 1, R < |t-c| → f t = 0) :
    |∫ t in (0:ℝ)..1, f t| ≤ 2*R*M := by
  let s := Set.Ioc (0:ℝ) 1 ∩ Set.Icc (c-R) (c+R)
  have hi : (∫ t in (0:ℝ)..1, f t) = ∫ t in s, f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc Set.inter_subset_left
    intro t ht
    apply hsupport t (Set.Ioc_subset_Icc_self ht.1)
    have hn : ¬ |t-c| ≤ R := by
      intro h
      have hh := abs_le.mp h
      exact ht.2 ⟨ht.1, by constructor <;> linarith⟩
    exact lt_of_not_ge hn
  have hsfin : volume s < ⊤ :=
    (measure_mono Set.inter_subset_right).trans_lt (measure_Icc_lt_top :
      volume (Set.Icc (c-R) (c+R)) < ⊤)
  have hvol : volume.real s ≤ 2*R := by
    calc
      _ ≤ volume.real (Set.Icc (c-R) (c+R)) := measureReal_mono Set.inter_subset_right
        (measure_Icc_lt_top : volume (Set.Icc (c-R) (c+R)) < ⊤).ne
      _ = 2*R := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [hi, ← Real.norm_eq_abs]
  calc
    _ ≤ M*volume.real s := norm_setIntegral_le_of_norm_le_const hsfin (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hbound t (Set.Ioc_subset_Icc_self ht.1))
    _ ≤ M*(2*R) := mul_le_mul_of_nonneg_left hvol hM
    _ = _ := by ring

theorem cubeIntegral_local_abs_bound (d : ℕ) (c : Fin d → ℝ)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (f : (Fin d → ℝ) → ℝ)
    (hbound : ∀ v ∈ UnitCube d, |f v| ≤ M)
    (hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-c i| ≤ R) → f v = 0) :
    |cubeIntegral d f| ≤ (2*R)^d*M := by
  induction d generalizing M with
  | zero => simpa [cubeIntegral] using hbound Fin.elim0 (fun i => Fin.elim0 i)
  | succ d ih =>
    have h : |cubeIntegral d (fun v => ∫ t in (0:ℝ)..1, f (Fin.cons t v))| ≤
        (2*R)^d*(2*R*M) := by
      apply ih (fun i => c i.succ) (2*R*M) (by positivity)
        (fun v => ∫ t in (0:ℝ)..1, f (Fin.cons t v))
      · intro v hv
        apply unitIntegral_local_abs_bound (c 0) R M hR hM
        · intro t ht
          exact hbound _ (cons_mem_unitCube ht hv)
        · intro t ht hn
          apply hsupport _ (cons_mem_unitCube ht hv)
          intro hh
          have h' := hh 0
          simp only [Fin.cons_zero] at h'
          linarith
      · intro v hv hn
        have hz : (fun t => f (Fin.cons t v)) =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] 0 := by
          apply ae_restrict_of_forall_mem measurableSet_Ioc
          intro t ht
          apply hsupport _ (cons_mem_unitCube (Set.Ioc_subset_Icc_self ht) hv)
          intro hh
          apply hn
          intro i
          simpa only [Fin.cons_succ] using hh i.succ
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact integral_eq_zero_of_ae hz
    simpa only [cubeIntegral, pow_succ, mul_assoc] using h

theorem quadrature_local_abs_bound {m : ℕ} (hm : 8 ≤ m)
    (c R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (f : ℝ → ℝ)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M)
    (hsupport : ∀ t ∈ Set.Icc (0:ℝ) 1, R < |t-c| → f t = 0) :
    |quadrature m f| ≤ (2*R+2/(m:ℝ))*M := by
  have h := cubeQuadrature_local_abs_bound 1 hm (fun _ => c) R M hR hM
    (fun v => f (v 0)) (fun v hv => hbound _ (hv 0)) (by
      intro v hv hn
      apply hsupport _ (hv 0)
      apply lt_of_not_ge
      intro hh
      apply hn
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hh)
  simpa only [cubeQuadrature, Fin.cons_zero, pow_one] using h

theorem quadrature_eq_zero_on {m : ℕ} (hm : 8 ≤ m) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, f t = 0) : quadrature m f = 0 := by
  apply abs_nonpos_iff.mp
  exact quadrature_abs_le hm (fun t ht => by rw [hf t ht]; norm_num)

theorem unitIntegral_eq_zero_on {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, f t = 0) : (∫ t in (0:ℝ)..1, f t) = 0 := by
  calc
    _ = ∫ _t in (0:ℝ)..1, (0:ℝ) := intervalIntegral.integral_congr (by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact hf t ht)
    _ = 0 := by simp

/-- Tensor localization from the actual pure sixth slice derivatives.
The function and those derivatives must vanish outside the stated box.
This is the input a smooth annular cutoff will have to satisfy. -/
theorem cubeQuadrature_local_sixth_order_bound (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (c : Fin d → ℝ) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (0:ℝ) 1))
    (hbound : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t| ≤ M)
    (hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-c i| ≤ R) → f v = 0)
    (hDsupport : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      (¬ ∀ j, |Function.update v i t j-c j| ≤ R) →
      iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t = 0) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤
      (64/(m:ℝ)^6)*(d:ℝ)*(2*R+2/(m:ℝ))^d*M := by
  let A := 2*R+2/(m:ℝ)
  let C := 64/(m:ℝ)^6
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hRA : 2*R ≤ A := by
    dsimp only [A]
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg m)]
  induction d generalizing M with
  | zero => simp [cubeQuadrature, cubeIntegral]
  | succ d ih =>
    let q : (Fin d → ℝ) → ℝ := fun v => quadrature m (fun t => f (Fin.cons t v))
    let a : (Fin d → ℝ) → ℝ := fun v => ∫ t in (0:ℝ)..1, f (Fin.cons t v)
    have hq : Continuous q := continuous_quadrature_param m (hf.comp (by fun_prop))
    have ha : Continuous a := continuous_unitIntegral_param (hf.comp (by fun_prop))
    have hsq : ∀ i v, v ∈ UnitCube d →
        ContDiffOn ℝ 6 (fun t => q (Function.update v i t)) (Set.Icc (0:ℝ) 1) := by
      intro i v hv
      apply contDiffOn_quadrature_param
      intro j
      simpa only [Nat.cast_ofNat, ← Fin.cons_update] using
        hs i.succ (Fin.cons (ruleNode m j) v)
          (cons_mem_unitCube (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm j)) hv)
    have hsl (i : Fin d) (v : Fin d → ℝ) (hv : v ∈ UnitCube d) :
        ∀ j : NodeIndex m, ContDiffOn ℝ 6
          (fun u => f (Fin.cons (ruleNode m j) (Function.update v i u)))
            (Set.Icc (0:ℝ) 1) := by
      intro j
      simpa only [← Fin.cons_update] using
        hs i.succ (Fin.cons (ruleNode m j) v)
          (cons_mem_unitCube (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm j)) hv)
    have hMq : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
        |iteratedDerivWithin 6 (fun u => q (Function.update v i u))
          (Set.Icc (0:ℝ) 1) t| ≤ A*M := by
      intro i v hv t ht
      dsimp only [q]
      rw [iteratedDerivWithin_quadrature_param m 6 (uniqueDiffOn_Icc (by norm_num)) (hsl i v hv) ht]
      apply quadrature_local_abs_bound hm (c 0) R M hR hM
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
      apply quadrature_eq_zero_on hm
      intro z hz
      apply hsupport _ (cons_mem_unitCube hz hv)
      intro hh
      apply hn
      intro i
      simpa only [Fin.cons_succ] using hh i.succ
    have hDqzero : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
        (¬ ∀ j, |Function.update v i t j-c j.succ| ≤ R) →
        iteratedDerivWithin 6 (fun u => q (Function.update v i u))
          (Set.Icc (0:ℝ) 1) t = 0 := by
      intro i v hv t ht hn
      dsimp only [q]
      rw [iteratedDerivWithin_quadrature_param m 6 (uniqueDiffOn_Icc (by norm_num)) (hsl i v hv) ht]
      apply quadrature_eq_zero_on hm
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
      have hsf : ContDiffOn ℝ 6 (fun t => f (Fin.cons t v)) (Set.Icc (0:ℝ) 1) := by
        simpa only [Fin.update_cons_zero] using hs 0 (Fin.cons 0 v) (cons_mem_unitCube h0 hv)
      have hl := quadrature_sixth_order_l1_bound_on hm hsf
      have hi : (∫ t in (0:ℝ)..1,
          |iteratedDerivWithin 6 (fun u => f (Fin.cons u v)) (Set.Icc (0:ℝ) 1) t|) ≤ 2*R*M := by
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
    change |cubeQuadrature d m q-cubeIntegral d a| ≤ _
    calc
      _ ≤ |cubeQuadrature d m q-cubeIntegral d q|+|cubeIntegral d q-cubeIntegral d a| := by
        rw [show cubeQuadrature d m q-cubeIntegral d a =
          (cubeQuadrature d m q-cubeIntegral d q)+(cubeIntegral d q-cubeIntegral d a) by ring]
        exact abs_add_le _ _
      _ ≤ C*(d:ℝ)*A^d*(A*M)+C*A^(d+1)*M := add_le_add hfirst hsecond
      _ = _ := by change _ = C*((d+1:ℕ):ℝ)*A^(d+1)*M; push_cast; rw [pow_succ]; ring

#print axioms unitIntegral_local_abs_bound
#print axioms cubeIntegral_local_abs_bound
#print axioms quadrature_local_abs_bound
#print axioms cubeQuadrature_local_sixth_order_bound

end SphericalRiesz.Boundary
