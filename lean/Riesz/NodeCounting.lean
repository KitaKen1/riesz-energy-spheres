import Riesz.CubeNodes
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-!
# Local counts for the original boundary-corrected nodes

Each node retains a distinct integer midpoint label, and moves by less
than one quarter of a cell. Counting labels between the extreme selected
labels avoids rounding functions and keeps the original interior grid.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz.Boundary

def midpointLabel (m : ℕ) : NodeIndex m → ℕ :=
  Sum.elim (fun i => i.val)
    (Sum.elim (fun j => 4+j.val) (fun i => m-1-i.val))

theorem midpointLabel_lt {m : ℕ} (hm : 8 ≤ m) (i : NodeIndex m) :
    midpointLabel m i < m := by
  rcases i with i | (i | i) <;> simp only [midpointLabel, Sum.elim_inl, Sum.elim_inr]
  all_goals have hi := i.isLt; omega

theorem midpointLabel_injective {m : ℕ} (hm : 8 ≤ m) :
    Function.Injective (midpointLabel m) := by
  intro i j h
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [midpointLabel, Sum.elim_inl, Sum.elim_inr] at h
  all_goals have hi := i.isLt; have hj := j.isLt
  all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals first | (apply Fin.ext; omega) | omega

theorem unscaledRuleNode_close_to_label {m : ℕ} (hm : 8 ≤ m) (i : NodeIndex m) :
    |unscaledRuleNode m i-((midpointLabel m i : ℝ)+1/2)| < 1/4 := by
  rcases i with i | (i | i)
  · exact node_close_to_midpoint i
  · have heq : unscaledRuleNode m (Sum.inr (Sum.inl i))-
        ((midpointLabel m (Sum.inr (Sum.inl i)) : ℝ)+1/2) = 0 := by
      simp only [unscaledRuleNode, midpointLabel, Sum.elim_inr, Sum.elim_inl, Nat.cast_add,
        Nat.cast_ofNat]
      ring
    rw [heq]
    norm_num
  · have hi : i.val ≤ m-1 := by have := i.isLt; omega
    have hm1 : 1 ≤ m := by omega
    simp only [unscaledRuleNode, midpointLabel, Sum.elim_inr,
      Nat.cast_sub hi, Nat.cast_sub hm1, Nat.cast_one]
    have heq : (m : ℝ)-node i-((m:ℝ)-1-(i:ℝ)+1/2) =
        -(node i-((i:ℝ)+1/2)) := by ring
    rw [heq, abs_neg]
    exact node_close_to_midpoint i

/-- A label span, rather than a floor/ceiling calculation. -/
theorem nat_finset_card_le_span (s : Finset ℕ) (hs : s.Nonempty) :
    s.card ≤ s.max' hs+1-s.min' hs := by
  calc
    s.card ≤ (Finset.Icc (s.min' hs) (s.max' hs)).card :=
      Finset.card_le_card (fun j hj => Finset.mem_Icc.mpr
        ⟨s.min'_le j hj, s.le_max' j hj⟩)
    _ = _ := Nat.card_Icc _ _

/-- Any interval of radius R contains at most 2 m R + 2 actual nodes. -/
theorem ruleNode_local_card_bound {m : ℕ} (hm : 8 ≤ m) (c R : ℝ) (hR : 0 ≤ R)
    (s : Finset (NodeIndex m)) (hs : ∀ i ∈ s, |ruleNode m i-c| ≤ R) :
    (s.card : ℝ) ≤ 2*(m:ℝ)*R+2 := by
  classical
  by_cases hne : s.Nonempty
  · let t := s.image (midpointLabel m)
    have ht : t.Nonempty := hne.image _
    have hc : t.card = s.card := Finset.card_image_of_injective s (midpointLabel_injective hm)
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
    have hiD := abs_lt.mp (unscaledRuleNode_close_to_label hm i)
    have hjD := abs_lt.mp (unscaledRuleNode_close_to_label hm j)
    have hiN : (m:ℝ)*(c-R) ≤ unscaledRuleNode m i := by
      have h := hiR.1
      unfold ruleNode at h
      have h' : c-R ≤ unscaledRuleNode m i/(m:ℝ) := by linarith
      have := (le_div_iff₀ hm0).mp h'
      nlinarith
    have hjN : unscaledRuleNode m j ≤ (m:ℝ)*(c+R) := by
      have h := hjR.2
      unfold ruleNode at h
      have h' : unscaledRuleNode m j/(m:ℝ) ≤ c+R := by linarith
      have := (div_le_iff₀ hm0).mp h'
      nlinarith
    have hil' : (midpointLabel m i : ℝ) = t.min' ht := by exact_mod_cast hil
    have hju' : (midpointLabel m j : ℝ) = t.max' ht := by exact_mod_cast hju
    rw [← hil', ← hju'] at hspan'
    nlinarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty, Nat.cast_zero]
    positivity

def cubeLocalNodeSet (d m : ℕ) (c : Fin d → ℝ) (R : ℝ) :
    Finset (Fin d → NodeIndex m) := by
  classical
  exact Finset.univ.filter (fun v => ∀ i, |cubeNode d m v i-c i| ≤ R)

theorem cubeNode_local_card_bound (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (c : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ((cubeLocalNodeSet d m c R).card : ℝ) ≤ (2*(m:ℝ)*R+2)^d := by
  classical
  let a (i : Fin d) := Finset.univ.filter (fun j : NodeIndex m => |ruleNode m j-c i| ≤ R)
  let b := cubeLocalNodeSet d m c R
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
    ruleNode_local_card_bound hm (c i) R hR (a i)
      (fun _ hj => (Finset.mem_filter.mp hj).2)
  calc
    _ ≤ ∏ i, ((a i).card : ℝ) := hc'
    _ ≤ ∏ _i : Fin d, (2*(m:ℝ)*R+2) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => ha i)
    _ = _ := by simp

/-- Localized stability uses the actual selected nodes, not a new cell rule. -/
theorem cubeQuadrature_local_abs_bound (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (c : Fin d → ℝ) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f : (Fin d → ℝ) → ℝ)
    (hbound : ∀ v ∈ UnitCube d, |f v| ≤ M)
    (hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-c i| ≤ R) → f v = 0) :
    |cubeQuadrature d m f| ≤ (2*R+2/(m:ℝ))^d*M := by
  classical
  let s := cubeLocalNodeSet d m c R
  have hsum : (∑ v : Fin d → NodeIndex m, f (cubeNode d m v)) =
      ∑ v ∈ s, f (cubeNode d m v) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro v _ hv
    apply hsupport _ (fun i => Set.Ioo_subset_Icc_self (cubeNode_mem_open d m hm v i))
    intro h
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hs : |∑ v ∈ s, f (cubeNode d m v)| ≤ (s.card:ℝ)*M := by
    calc
      _ ≤ ∑ v ∈ s, |f (cubeNode d m v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ s, M := Finset.sum_le_sum (fun v _ =>
        hbound _ (fun i => Set.Ioo_subset_Icc_self (cubeNode_mem_open d m hm v i)))
      _ = _ := by simp [nsmul_eq_mul]
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
  rw [cubeQuadrature_as_node_sum, hsum, abs_div, abs_of_pos (pow_pos hm0 d)]
  calc
    _ ≤ ((s.card:ℝ)*M)/(m:ℝ)^d := div_le_div_of_nonneg_right hs (pow_pos hm0 d).le
    _ ≤ ((2*(m:ℝ)*R+2)^d*M)/(m:ℝ)^d :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (cubeNode_local_card_bound d hm c R hR) hM)
        (pow_pos hm0 d).le
    _ = (2*R+2/(m:ℝ))^d*M := by
      rw [mul_div_right_comm, ← div_pow]
      congr 1
      congr 1
      field_simp

#print axioms midpointLabel_injective
#print axioms unscaledRuleNode_close_to_label
#print axioms ruleNode_local_card_bound
#print axioms cubeNode_local_card_bound
#print axioms cubeQuadrature_local_abs_bound

end SphericalRiesz.Boundary
