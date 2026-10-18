import Riesz.E8Grid

/-!
# Original corrected nodes centered on an integer grid

For m=2q+9 the original interior node q is exactly 1/2. Any function
supported in the coordinate box of radius q has zero contribution from
the unchanged boundary corrections. Its original finite node sum is
therefore the full finitely supported integer-lattice sum.
-/
set_option autoImplicit false
noncomputable section
namespace SphericalRiesz.Boundary

abbrev centeredMesh (q : ℕ) : ℕ := 2*q+9

def centeredInteriorIndex (q : ℕ) : Fin (centeredMesh q-8) := ⟨q, by simp only [centeredMesh]; omega⟩

def centeredRuleCoordinate (q : ℕ) (j : NodeIndex (centeredMesh q)) : ℝ :=
  (centeredMesh q : ℝ)*(ruleNode (centeredMesh q) j-1/2)

def centeredCubeCoordinate (d q : ℕ) (v : Fin d → NodeIndex (centeredMesh q)) : Fin d → ℝ :=
  fun i => centeredRuleCoordinate q (v i)

def centeredIntegerLabel (d q : ℕ) (w : Fin d → Fin (centeredMesh q-8)) : Fin d → ℤ :=
  fun i => (w i : ℤ)-(q : ℤ)

def centeredIntegerBox (d q : ℕ) : Finset (Fin d → ℤ) := by
  classical
  exact Finset.univ.image (centeredIntegerLabel d q)

theorem centeredRuleCoordinate_eq (q : ℕ) (j : NodeIndex (centeredMesh q)) :
    centeredRuleCoordinate q j = unscaledRuleNode (centeredMesh q) j-(centeredMesh q : ℝ)/2 := by
  have hm : (centeredMesh q : ℝ) ≠ 0 := by positivity
  unfold centeredRuleCoordinate ruleNode
  field_simp <;> ring

theorem centeredRuleNode (q : ℕ) :
    ruleNode (centeredMesh q) (SphericalRiesz.interiorNodeIndex (centeredInteriorIndex q)) = 1/2 := by
  rw [SphericalRiesz.interiorRuleNode]
  simp only [centeredInteriorIndex, centeredMesh, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp <;> ring

theorem centeredRuleCoordinate_interior (q : ℕ) (j : Fin (centeredMesh q-8)) :
    centeredRuleCoordinate q (SphericalRiesz.interiorNodeIndex j) =
      ((j : ℤ)-(q : ℤ) : ℤ) := by
  rw [centeredRuleCoordinate_eq]
  simp only [unscaledRuleNode, SphericalRiesz.interiorNodeIndex, Sum.elim_inr,
    Sum.elim_inl, centeredMesh, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Int.cast_sub, Int.cast_natCast]
  ring

theorem centeredCubeCoordinate_interior (d q : ℕ) (w : Fin d → Fin (centeredMesh q-8)) :
    centeredCubeCoordinate d q (fun i => SphericalRiesz.interiorNodeIndex (w i)) =
      fun i => (centeredIntegerLabel d q w i : ℝ) := by
  funext i
  exact centeredRuleCoordinate_interior q (w i)

theorem centeredRuleCoordinate_boundary (q : ℕ) (j : NodeIndex (centeredMesh q))
    (hj : ¬ ∃ k, SphericalRiesz.interiorNodeIndex k = j) :
    (q : ℝ)+1/2 < |centeredRuleCoordinate q j| := by
  rw [centeredRuleCoordinate_eq]
  rcases j with j | (j | j)
  · have hn := (node_between_zero_four j).2
    simp only [unscaledRuleNode, Sum.elim_inl, centeredMesh,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [neg_le_abs (node j-((2:ℝ)*q+9)/2)]
  · exact False.elim (hj ⟨j, rfl⟩)
  · have hn := (node_between_zero_four j).2
    simp only [unscaledRuleNode, Sum.elim_inr, centeredMesh,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [le_abs_self (((2:ℝ)*q+9)-node j-((2:ℝ)*q+9)/2)]

theorem centeredIntegerLabel_injective (d q : ℕ) :
    Function.Injective (centeredIntegerLabel d q) := by
  intro w v h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change (w i : ℤ)-(q : ℤ) = (v i : ℤ)-(q : ℤ) at hi
  omega

theorem centeredIntegerBox_mem (d q : ℕ) (z : Fin d → ℤ) :
    z ∈ centeredIntegerBox d q ↔ ∀ i, -(q : ℤ) ≤ z i ∧ z i ≤ q := by
  classical
  constructor
  · intro hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    intro i
    have hi := (w i).isLt
    simp only [centeredMesh] at hi
    simp only [centeredIntegerLabel]
    omega
  · intro hz
    let w : Fin d → Fin (centeredMesh q-8) := fun i =>
      ⟨(z i+(q : ℤ)).toNat, by
        have hi := hz i
        have hn : 0 ≤ z i+(q : ℤ) := by omega
        have he := Int.toNat_of_nonneg hn
        simp only [centeredMesh]
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ _, ?_⟩
    funext i
    change (((z i+(q : ℤ)).toNat : ℤ)-(q : ℤ)) = z i
    rw [Int.toNat_of_nonneg (by have hi := hz i; omega)]
    omega

theorem centeredIntegerBox_card (d q : ℕ) :
    (centeredIntegerBox d q).card = (2*q+1)^d := by
  classical
  rw [centeredIntegerBox, Finset.card_image_of_injective _ (centeredIntegerLabel_injective d q)]
  simp only [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]
  congr 1

theorem centeredNodeSum_eq_integer_sum (d q : ℕ) (R : ℝ) (hR : R ≤ q)
    (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ y, (¬ ∀ i, |y i| ≤ R) → F y = 0) :
    (∑ v : Fin d → NodeIndex (centeredMesh q), F (centeredCubeCoordinate d q v)) =
      ∑ z ∈ centeredIntegerBox d q, F (fun i => (z i : ℝ)) := by
  classical
  let e : (Fin d → Fin (centeredMesh q-8)) → (Fin d → NodeIndex (centeredMesh q)) :=
    fun w i => SphericalRiesz.interiorNodeIndex (w i)
  have he : Function.Injective e := by
    intro w v h
    funext i
    exact SphericalRiesz.interiorNodeIndex_injective _ (congrFun h i)
  let s := Finset.univ.image e
  have hz (v : Fin d → NodeIndex (centeredMesh q)) (hv : v ∉ s) :
      F (centeredCubeCoordinate d q v) = 0 := by
    have hi : ∃ i, ¬ ∃ k, SphericalRiesz.interiorNodeIndex k = v i := by
      by_contra! hn
      obtain ⟨w, hw⟩ := Classical.skolem.mp hn
      apply hv
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, funext hw⟩
    obtain ⟨i, hi⟩ := hi
    apply hF
    intro hb
    have hh := centeredRuleCoordinate_boundary q (v i) hi
    have hbi := hb i
    change |centeredRuleCoordinate q (v i)| ≤ R at hbi
    linarith
  calc
    _ = ∑ v ∈ s, F (centeredCubeCoordinate d q v) :=
      (Finset.sum_subset (Finset.subset_univ s) (fun v _ hv => hz v hv)).symm
    _ = ∑ w : Fin d → Fin (centeredMesh q-8), F (fun i => (centeredIntegerLabel d q w i : ℝ)) := by
      dsimp only [s]
      rw [Finset.sum_image he.injOn]
      apply Finset.sum_congr rfl
      intro w _
      rw [show e w = (fun i => SphericalRiesz.interiorNodeIndex (w i)) by rfl,
        centeredCubeCoordinate_interior]
    _ = _ := by
      rw [centeredIntegerBox, Finset.sum_image (centeredIntegerLabel_injective d q).injOn]

theorem centeredInteger_sum_eq_tsum (d q : ℕ) (R : ℝ) (hR : R ≤ q)
    (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ y, (¬ ∀ i, |y i| ≤ R) → F y = 0) :
    (∑ z ∈ centeredIntegerBox d q, F (fun i => (z i : ℝ))) =
      ∑' z : Fin d → ℤ, F (fun i => (z i : ℝ)) := by
  classical
  symm
  apply tsum_eq_sum
  intro z hz
  apply hF
  intro hb
  apply hz
  rw [centeredIntegerBox_mem]
  intro i
  have hi := abs_le.mp (hb i)
  constructor
  · exact_mod_cast (show -(q : ℝ) ≤ (z i : ℝ) by linarith)
  · exact_mod_cast (show (z i : ℝ) ≤ (q : ℝ) by linarith)

theorem centeredNodeSum_eq_tsum (d q : ℕ) (R : ℝ) (hR : R ≤ q)
    (F : (Fin d → ℝ) → ℝ)
    (hF : ∀ y, (¬ ∀ i, |y i| ≤ R) → F y = 0) :
    (∑ v : Fin d → NodeIndex (centeredMesh q), F (centeredCubeCoordinate d q v)) =
      ∑' z : Fin d → ℤ, F (fun i => (z i : ℝ)) := by
  rw [centeredNodeSum_eq_integer_sum d q R hR F hF,
    centeredInteger_sum_eq_tsum d q R hR F hF]

#print axioms centeredRuleCoordinate_eq
#print axioms centeredRuleNode
#print axioms centeredRuleCoordinate_interior
#print axioms centeredCubeCoordinate_interior
#print axioms centeredRuleCoordinate_boundary
#print axioms centeredIntegerLabel_injective
#print axioms centeredIntegerBox_mem
#print axioms centeredIntegerBox_card
#print axioms centeredNodeSum_eq_integer_sum
#print axioms centeredInteger_sum_eq_tsum
#print axioms centeredNodeSum_eq_tsum

end SphericalRiesz.Boundary
