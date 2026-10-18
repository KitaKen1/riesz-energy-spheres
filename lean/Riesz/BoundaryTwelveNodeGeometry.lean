import Riesz.BoundaryTwelveTensor
import Riesz.NodeCounting
import Riesz.NodeSeparation

/-! Injective integer labels and localized counting for the actual sparse rule. -/
set_option autoImplicit false
noncomputable section
namespace SphericalRiesz.Boundary

theorem twelveStripNode_close_to_midpoint (i : Fin 37) :
    |twelveStripNode i-((i:ℝ)+1/2)| < 1/4 := by
  have h := twelveStripNode_bounds i
  rw [abs_lt]
  constructor <;> linarith

def twelveMidpointLabel (m : ℕ) : TwelveNodeIndex m → ℕ :=
  Sum.elim (fun i => i.val)
    (Sum.elim (fun j => 37+j.val) (fun i => m-1-i.val))

theorem twelveMidpointLabel_lt {m : ℕ} (hm : 74 ≤ m) (i : TwelveNodeIndex m) :
    twelveMidpointLabel m i < m := by
  rcases i with i | (i | i) <;> simp only [twelveMidpointLabel, Sum.elim_inl, Sum.elim_inr]
  all_goals have hi := i.isLt; omega

theorem twelveMidpointLabel_injective {m : ℕ} (hm : 74 ≤ m) :
    Function.Injective (twelveMidpointLabel m) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [twelveMidpointLabel, Sum.elim_inl, Sum.elim_inr] at h
  all_goals have hi := i.isLt; have hj := j.isLt
  all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals first | (apply Fin.ext; omega) | omega

theorem twelveUnscaledRuleNode_close_to_label {m : ℕ} (hm : 74 ≤ m) (i : TwelveNodeIndex m) :
    |twelveUnscaledRuleNode m i-((twelveMidpointLabel m i : ℝ)+1/2)| < 1/4 := by
  rcases i with i | (i | i)
  · exact twelveStripNode_close_to_midpoint i
  · have heq : twelveUnscaledRuleNode m (Sum.inr (Sum.inl i))-
        ((twelveMidpointLabel m (Sum.inr (Sum.inl i)) : ℝ)+1/2) = 0 := by
      simp only [twelveUnscaledRuleNode, twelveMidpointLabel, Sum.elim_inr, Sum.elim_inl, Nat.cast_add,
        Nat.cast_ofNat]
      ring
    rw [heq]
    norm_num
  · have hi : i.val ≤ m-1 := by have := i.isLt; omega
    have hm1 : 1 ≤ m := by omega
    simp only [twelveUnscaledRuleNode, twelveMidpointLabel, Sum.elim_inr,
      Nat.cast_sub hi, Nat.cast_sub hm1, Nat.cast_one]
    have heq : (m : ℝ)-twelveStripNode i-((m:ℝ)-1-(i:ℝ)+1/2) =
        -(twelveStripNode i-((i:ℝ)+1/2)) := by ring
    rw [heq, abs_neg]
    exact twelveStripNode_close_to_midpoint i

/-- Any interval of radius R contains at most 2 m R + 2 actual nodes. -/
theorem twelveRuleNode_local_card_bound {m : ℕ} (hm : 74 ≤ m) (c R : ℝ) (hR : 0 ≤ R)
    (s : Finset (TwelveNodeIndex m)) (hs : ∀ i ∈ s, |twelveRuleNode m i-c| ≤ R) :
    (s.card : ℝ) ≤ 2*(m:ℝ)*R+2 := by
  classical
  by_cases hne : s.Nonempty
  · let t := s.image (twelveMidpointLabel m)
    have ht : t.Nonempty := hne.image _
    have hc : t.card = s.card := Finset.card_image_of_injective s (twelveMidpointLabel_injective hm)
    have hl : t.min' ht ∈ t := t.min'_mem ht
    have hu : t.max' ht ∈ t := t.max'_mem ht
    obtain ⟨i, hi, hil⟩ := Finset.mem_image.mp hl
    obtain ⟨j, hj, hju⟩ := Finset.mem_image.mp hu
    have hspan := nat_finset_card_le_span t ht
    have hle : t.min' ht ≤ t.max' ht+1 := by have := t.min'_le_max' ht; omega
    have hspan' : (s.card : ℝ) ≤ (t.max' ht : ℝ)+1-(t.min' ht : ℝ) := by
      rw [hc] at hspan
      have hh : (s.card : ℝ) ≤ ((t.max' ht+1-t.min' ht : ℕ) : ℝ) := by exact_mod_cast hspan
      simpa only [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one] using hh
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hiR := abs_le.mp (hs i hi)
    have hjR := abs_le.mp (hs j hj)
    have hiD := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hm i)
    have hjD := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hm j)
    have hiN : (m:ℝ)*(c-R) ≤ twelveUnscaledRuleNode m i := by
      have h := hiR.1
      unfold twelveRuleNode at h
      have h' : c-R ≤ twelveUnscaledRuleNode m i/(m:ℝ) := by linarith
      have := (le_div_iff₀ hm0).mp h'
      nlinarith
    have hjN : twelveUnscaledRuleNode m j ≤ (m:ℝ)*(c+R) := by
      have h := hjR.2
      unfold twelveRuleNode at h
      have h' : twelveUnscaledRuleNode m j/(m:ℝ) ≤ c+R := by linarith
      have := (div_le_iff₀ hm0).mp h'
      nlinarith
    have hil' : (twelveMidpointLabel m i : ℝ) = t.min' ht := by exact_mod_cast hil
    have hju' : (twelveMidpointLabel m j : ℝ) = t.max' ht := by exact_mod_cast hju
    rw [← hil', ← hju'] at hspan'
    nlinarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty, Nat.cast_zero]
    positivity

def twelveCubeLocalNodeSet (d m : ℕ) (c : Fin d → ℝ) (R : ℝ) :
    Finset (Fin d → TwelveNodeIndex m) := by
  classical
  exact Finset.univ.filter (fun v => ∀ i, |twelveCubeNode d m v i-c i| ≤ R)

theorem twelveCubeNode_local_card_bound (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    (c : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ((twelveCubeLocalNodeSet d m c R).card : ℝ) ≤ (2*(m:ℝ)*R+2)^d := by
  classical
  let a (i : Fin d) := Finset.univ.filter (fun j : TwelveNodeIndex m => |twelveRuleNode m j-c i| ≤ R)
  let b := twelveCubeLocalNodeSet d m c R
  let f : b → (i : Fin d) → a i := fun v i =>
    ⟨v.val i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp v.property).2 i⟩⟩
  have hf : Function.Injective f := by
    intro v u h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hc : b.card ≤ ∏ i, (a i).card := by
    simpa only [Fintype.card_coe, Fintype.card_pi] using Fintype.card_le_of_injective f hf
  have hc' : (b.card : ℝ) ≤ ∏ i, ((a i).card : ℝ) := by exact_mod_cast hc
  have ha (i : Fin d) : ((a i).card : ℝ) ≤ 2*(m:ℝ)*R+2 :=
    twelveRuleNode_local_card_bound hm (c i) R hR (a i)
      (fun _ hj => (Finset.mem_filter.mp hj).2)
  calc
    _ ≤ ∏ i, ((a i).card : ℝ) := hc'
    _ ≤ ∏ _i : Fin d, (2*(m:ℝ)*R+2) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => ha i)
    _ = _ := by simp

/-- Localized stability uses the actual selected nodes, not a new cell rule. -/
theorem twelveCubeQuadrature_local_abs_bound (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    (c : Fin d → ℝ) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f : (Fin d → ℝ) → ℝ)
    (hbound : ∀ v ∈ UnitCube d, |f v| ≤ M)
    (hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-c i| ≤ R) → f v = 0) :
    |twelveCubeQuadrature d m f| ≤ (2*R+2/(m:ℝ))^d*M := by
  classical
  let s := twelveCubeLocalNodeSet d m c R
  have hsum : (∑ v : Fin d → TwelveNodeIndex m, f (twelveCubeNode d m v)) =
      ∑ v ∈ s, f (twelveCubeNode d m v) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro v _ hv
    apply hsupport _ (fun i => Set.Ioo_subset_Icc_self (twelveCubeNode_mem_open d m hm v i))
    intro h
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hs : |∑ v ∈ s, f (twelveCubeNode d m v)| ≤ (s.card:ℝ)*M := by
    calc
      _ ≤ ∑ v ∈ s, |f (twelveCubeNode d m v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ s, M := Finset.sum_le_sum (fun v _ =>
        hbound _ (fun i => Set.Ioo_subset_Icc_self (twelveCubeNode_mem_open d m hm v i)))
      _ = _ := by simp [nsmul_eq_mul]
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
  rw [twelveCubeQuadrature_as_node_sum, hsum, abs_div, abs_of_pos (pow_pos hm0 d)]
  calc
    _ ≤ ((s.card:ℝ)*M)/(m:ℝ)^d := div_le_div_of_nonneg_right hs (pow_pos hm0 d).le
    _ ≤ ((2*(m:ℝ)*R+2)^d*M)/(m:ℝ)^d :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (twelveCubeNode_local_card_bound d hm c R hR) hM)
        (pow_pos hm0 d).le
    _ = (2*R+2/(m:ℝ))^d*M := by
      rw [mul_div_right_comm, ← div_pow]
      congr 1
      congr 1
      field_simp

theorem twelveUnscaledRuleNode_sub_gt_half {m : ℕ} (hm : 74 ≤ m)
    (i j : TwelveNodeIndex m) (hij : twelveMidpointLabel m i < twelveMidpointLabel m j) :
    1/2 < twelveUnscaledRuleNode m j-twelveUnscaledRuleNode m i := by
  have hgap : (twelveMidpointLabel m i : ℝ)+1 ≤ twelveMidpointLabel m j := by
    exact_mod_cast (Nat.succ_le_of_lt hij)
  have hi := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hm i)
  have hj := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hm j)
  linarith

theorem twelveUnscaledRuleNode_separated {m : ℕ} (hm : 74 ≤ m)
    (i j : TwelveNodeIndex m) (hij : i ≠ j) :
    1/2 < |twelveUnscaledRuleNode m i-twelveUnscaledRuleNode m j| := by
  have hlabel : twelveMidpointLabel m i ≠ twelveMidpointLabel m j :=
    fun h => hij (twelveMidpointLabel_injective hm h)
  rcases lt_or_gt_of_ne hlabel with h | h
  · rw [abs_sub_comm]
    exact (twelveUnscaledRuleNode_sub_gt_half hm i j h).trans_le (le_abs_self _)
  · exact (twelveUnscaledRuleNode_sub_gt_half hm j i h).trans_le (le_abs_self _)

theorem twelveRuleNode_separated {m : ℕ} (hm : 74 ≤ m)
    (i j : TwelveNodeIndex m) (hij : i ≠ j) :
    1/(2*(m:ℝ)) < |twelveRuleNode m i-twelveRuleNode m j| := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := div_lt_div_of_pos_right (twelveUnscaledRuleNode_separated hm i j hij) hm0
  simpa only [twelveRuleNode, ← sub_div, abs_div, abs_of_pos hm0, div_div] using h

theorem twelveCubeNode_coordinate_separated (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    (v w : Fin d → TwelveNodeIndex m) (hvw : v ≠ w) :
    ∃ i : Fin d, 1/(2*(m:ℝ)) < |twelveCubeNode d m v i-twelveCubeNode d m w i| := by
  have h : ∃ i, v i ≠ w i := by
    by_contra hn
    exact hvw (funext (fun i => by simpa using (not_exists.mp hn i)))
  obtain ⟨i, hi⟩ := h
  exact ⟨i, twelveRuleNode_separated hm (v i) (w i) hi⟩

theorem twelveCubeNode_norm_separated (d : ℕ) {m : ℕ} (hm : 74 ≤ m)
    (v w : Fin d → TwelveNodeIndex m) (hvw : v ≠ w) :
    1/(2*(m:ℝ)) < ‖twelveCubeNode d m v-twelveCubeNode d m w‖ := by
  obtain ⟨i, hi⟩ := twelveCubeNode_coordinate_separated d hm v w hvw
  exact hi.trans_le (by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (twelveCubeNode d m v-twelveCubeNode d m w) i)


end SphericalRiesz.Boundary
