import Riesz.CenteredGrid

/-!
# Integer coordinates around every original interior node

The boundary correction is unchanged. A function whose support fits in
the interior padding has exactly the full integer-lattice node sum,
for every mesh and every interior center, with no parity restriction.
-/
set_option autoImplicit false
noncomputable section
namespace SphericalRiesz.Boundary

def interiorCenter (d m : ℕ) (j : Fin d → Fin (m-8)) : Fin d → ℝ :=
  fun i => ruleNode m (SphericalRiesz.interiorNodeIndex (j i))

def interiorRuleCoordinate (m : ℕ) (j : Fin (m-8)) (v : NodeIndex m) : ℝ :=
  (m : ℝ)*(ruleNode m v-ruleNode m (SphericalRiesz.interiorNodeIndex j))

def interiorCubeCoordinate (d m : ℕ) (j : Fin d → Fin (m-8))
    (v : Fin d → NodeIndex m) : Fin d → ℝ :=
  fun i => interiorRuleCoordinate m (j i) (v i)

def interiorIntegerLabel (d m : ℕ) (j w : Fin d → Fin (m-8)) : Fin d → ℤ :=
  fun i => (w i : ℤ)-(j i : ℤ)

def interiorIntegerBox (d m : ℕ) (j : Fin d → Fin (m-8)) : Finset (Fin d → ℤ) := by
  classical
  exact Finset.univ.image (interiorIntegerLabel d m j)

/-- The cutoff fits between the first and last unmodified interior nodes. -/
def InteriorPadding (d m : ℕ) (j : Fin d → Fin (m-8)) (R : ℝ) : Prop :=
  ∀ i, R ≤ (j i : ℝ) ∧ R ≤ (m : ℝ)-9-(j i : ℝ)

theorem interiorRuleCoordinate_eq (m : ℕ) (hm : 0 < m) (j : Fin (m-8))
    (v : NodeIndex m) :
    interiorRuleCoordinate m j v = unscaledRuleNode m v-((j : ℝ)+9/2) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold interiorRuleCoordinate
  rw [SphericalRiesz.interiorRuleNode]
  unfold ruleNode
  field_simp

theorem interiorRuleCoordinate_interior (m : ℕ) (hm : 0 < m)
    (j w : Fin (m-8)) :
    interiorRuleCoordinate m j (SphericalRiesz.interiorNodeIndex w) =
      ((w : ℤ)-(j : ℤ) : ℤ) := by
  rw [interiorRuleCoordinate_eq m hm]
  simp only [unscaledRuleNode, SphericalRiesz.interiorNodeIndex,
    Sum.elim_inr, Sum.elim_inl, Int.cast_sub, Int.cast_natCast]
  ring

theorem interiorCubeCoordinate_interior (d m : ℕ) (hm : 0 < m)
    (j w : Fin d → Fin (m-8)) :
    interiorCubeCoordinate d m j (fun i => SphericalRiesz.interiorNodeIndex (w i)) =
      fun i => (interiorIntegerLabel d m j w i : ℝ) := by
  funext i
  exact interiorRuleCoordinate_interior m hm (j i) (w i)

theorem interiorRuleCoordinate_boundary (m : ℕ) (hm : 0 < m) (j : Fin (m-8))
    (R : ℝ) (hleft : R ≤ (j : ℝ)) (hright : R ≤ (m : ℝ)-9-(j : ℝ))
    (v : NodeIndex m) (hv : ¬ ∃ k, SphericalRiesz.interiorNodeIndex k = v) :
    R < |interiorRuleCoordinate m j v| := by
  rw [interiorRuleCoordinate_eq m hm]
  rcases v with v | (v | v)
  · have hn := (node_between_zero_four v).2
    simp only [unscaledRuleNode, Sum.elim_inl]
    linarith [neg_le_abs (node v-((j : ℝ)+9/2))]
  · exact False.elim (hv ⟨v, rfl⟩)
  · have hn := (node_between_zero_four v).2
    simp only [unscaledRuleNode, Sum.elim_inr]
    linarith [le_abs_self ((m : ℝ)-node v-((j : ℝ)+9/2))]

theorem interiorIntegerLabel_injective (d m : ℕ) (j : Fin d → Fin (m-8)) :
    Function.Injective (interiorIntegerLabel d m j) := by
  intro w v h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change (w i : ℤ)-(j i : ℤ) = (v i : ℤ)-(j i : ℤ) at hi
  omega

theorem interiorIntegerBox_mem (d m : ℕ) (j : Fin d → Fin (m-8)) (z : Fin d → ℤ) :
    z ∈ interiorIntegerBox d m j ↔
      ∀ i, -(j i : ℤ) ≤ z i ∧ z i ≤ (m : ℤ)-9-(j i : ℤ) := by
  classical
  constructor
  · intro hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    intro i
    have hi := (w i).isLt
    simp only [interiorIntegerLabel]
    omega
  · intro hz
    let w : Fin d → Fin (m-8) := fun i =>
      ⟨(z i+(j i : ℤ)).toNat, by
        have hi := hz i
        have hn : 0 ≤ z i+(j i : ℤ) := by omega
        have he := Int.toNat_of_nonneg hn
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ _, ?_⟩
    funext i
    change (((z i+(j i : ℤ)).toNat : ℤ)-(j i : ℤ)) = z i
    rw [Int.toNat_of_nonneg (by have hi := hz i; omega)]
    omega

theorem interiorNodeSum_eq_integer_sum (d m : ℕ) (hm : 0 < m)
    (j : Fin d → Fin (m-8)) (R : ℝ) (hR : InteriorPadding d m j R)
    (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ y, (¬ ∀ i, |y i| ≤ R) → F y = 0) :
    (∑ v : Fin d → NodeIndex m, F (interiorCubeCoordinate d m j v)) =
      ∑ z ∈ interiorIntegerBox d m j, F (fun i => (z i : ℝ)) := by
  classical
  let e : (Fin d → Fin (m-8)) → (Fin d → NodeIndex m) :=
    fun w i => SphericalRiesz.interiorNodeIndex (w i)
  have he : Function.Injective e := by
    intro w v h
    funext i
    exact SphericalRiesz.interiorNodeIndex_injective _ (congrFun h i)
  let s := Finset.univ.image e
  have hz (v : Fin d → NodeIndex m) (hv : v ∉ s) :
      F (interiorCubeCoordinate d m j v) = 0 := by
    have hi : ∃ i, ¬ ∃ k, SphericalRiesz.interiorNodeIndex k = v i := by
      by_contra! hn
      obtain ⟨w, hw⟩ := Classical.skolem.mp hn
      apply hv
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, funext hw⟩
    obtain ⟨i, hi⟩ := hi
    apply hF
    intro hb
    have hh := interiorRuleCoordinate_boundary m hm (j i) R (hR i).1 (hR i).2 (v i) hi
    have hbi := hb i
    change |interiorRuleCoordinate m (j i) (v i)| ≤ R at hbi
    linarith
  calc
    _ = ∑ v ∈ s, F (interiorCubeCoordinate d m j v) :=
      (Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => hz v hv)).symm
    _ = ∑ w : Fin d → Fin (m-8), F (fun i => (interiorIntegerLabel d m j w i : ℝ)) := by
      dsimp only [s]
      rw [Finset.sum_image he.injOn]
      apply Finset.sum_congr rfl
      intro w _
      rw [show e w = (fun i => SphericalRiesz.interiorNodeIndex (w i)) by rfl,
        interiorCubeCoordinate_interior d m hm]
    _ = _ := by
      rw [interiorIntegerBox, Finset.sum_image (interiorIntegerLabel_injective d m j).injOn]

theorem interiorInteger_sum_eq_tsum (d m : ℕ) (j : Fin d → Fin (m-8))
    (R : ℝ) (hR : InteriorPadding d m j R)
    (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ y, (¬ ∀ i, |y i| ≤ R) → F y = 0) :
    (∑ z ∈ interiorIntegerBox d m j, F (fun i => (z i : ℝ))) =
      ∑' z : Fin d → ℤ, F (fun i => (z i : ℝ)) := by
  classical
  symm
  apply tsum_eq_sum
  intro z hz
  apply hF
  intro hb
  apply hz
  rw [interiorIntegerBox_mem]
  intro i
  have hi := abs_le.mp (hb i)
  constructor
  · exact_mod_cast (show -(j i : ℝ) ≤ (z i : ℝ) by linarith [(hR i).1])
  · exact_mod_cast (show (z i : ℝ) ≤ (m : ℝ)-9-(j i : ℝ) by linarith [(hR i).2])

theorem interiorNodeSum_eq_tsum (d m : ℕ) (hm : 0 < m)
    (j : Fin d → Fin (m-8)) (R : ℝ) (hR : InteriorPadding d m j R)
    (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ y, (¬ ∀ i, |y i| ≤ R) → F y = 0) :
    (∑ v : Fin d → NodeIndex m, F (interiorCubeCoordinate d m j v)) =
      ∑' z : Fin d → ℤ, F (fun i => (z i : ℝ)) := by
  rw [interiorNodeSum_eq_integer_sum d m hm j R hR F hF,
    interiorInteger_sum_eq_tsum d m j R hR F hF]

#print axioms interiorRuleCoordinate_eq
#print axioms interiorRuleCoordinate_interior
#print axioms interiorCubeCoordinate_interior
#print axioms interiorRuleCoordinate_boundary
#print axioms interiorIntegerLabel_injective
#print axioms interiorIntegerBox_mem
#print axioms interiorNodeSum_eq_integer_sum
#print axioms interiorInteger_sum_eq_tsum
#print axioms interiorNodeSum_eq_tsum

end SphericalRiesz.Boundary
