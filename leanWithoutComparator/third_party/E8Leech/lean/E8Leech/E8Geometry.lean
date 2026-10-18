import E8Leech.E8Coordinates
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# E8 geometry from doubled-coordinate arithmetic

The minimum-norm proof separates the odd coset from the even coset. In the odd coset every
coordinate contributes a square at least one. In the even coset two nonzero coordinates
contribute at least four each, or a sole nonzero coordinate is divisible by four. No root
enumeration or classification of even unimodular lattices is used.
-/

noncomputable section

namespace E8Leech

open Set Finset

theorem halfCoordinates_injective : Function.Injective halfCoordinates := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Ambient 8 => x i) h
  change (z i : ℝ) / 2 = (w i : ℝ) / 2 at hi
  exact_mod_cast (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp hi

theorem e8Numerators_sub {z w : Fin 8 → ℤ} (hz : z ∈ e8Numerators)
    (hw : w ∈ e8Numerators) : z - w ∈ e8Numerators := by
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [Pi.sub_apply, sub_sub_sub_comm] using dvd_sub (hz.1 i) (hw.1 i)
  · simpa only [Pi.sub_apply, Finset.sum_sub_distrib] using dvd_sub hz.2 hw.2

theorem halfCoordinates_sub (z w : Fin 8 → ℤ) :
    halfCoordinates (z - w) = halfCoordinates z - halfCoordinates w := by
  ext i
  simp [halfCoordinates, sub_div]

theorem e8Set_sub {x y : Ambient 8} (hx : x ∈ e8Set) (hy : y ∈ e8Set) : x - y ∈ e8Set := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨z - w, e8Numerators_sub hz hw, halfCoordinates_sub z w⟩

private theorem int_square_ge_one {k : ℤ} (hk : k ≠ 0) : 1 ≤ k ^ 2 := by
  have h : k ≤ -1 ∨ 1 ≤ k := by omega
  rcases h with h | h <;> nlinarith [sq_nonneg (k + 1), sq_nonneg (k - 1)]

private theorem int_square_ge_dvd {k m : ℤ} (h : m ∣ k) (hk : k ≠ 0) : m ^ 2 ≤ k ^ 2 := by
  obtain ⟨a, rfl⟩ := h
  have ha : a ≠ 0 := by intro ha; simp [ha] at hk
  have hs := int_square_ge_one ha
  nlinarith [sq_nonneg m, sq_nonneg a]

theorem e8Numerators_square_sum_ge {z : Fin 8 → ℤ} (hz : z ∈ e8Numerators) (hne : z ≠ 0) :
    8 ≤ ∑ i, z i ^ 2 := by
  by_cases heven : (2 : ℤ) ∣ z 0
  · have hdiv : ∀ i, (2 : ℤ) ∣ z i := by
      intro i
      simpa using dvd_add (hz.1 i) heven
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      apply hne
      ext i
      simpa using not_exists.mp h i
    by_cases hother : ∃ j, j ≠ i ∧ z j ≠ 0
    · obtain ⟨j, hji, hj⟩ := hother
      have hi4 : 4 ≤ z i ^ 2 := by simpa using int_square_ge_dvd (hdiv i) hi
      have hj4 : 4 ≤ z j ^ 2 := by simpa using int_square_ge_dvd (hdiv j) hj
      have hsum : ∑ k ∈ ({i, j} : Finset (Fin 8)), z k ^ 2 ≤ ∑ k : Fin 8, z k ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => sq_nonneg (z k))
      simp only [Finset.sum_pair hji.symm] at hsum
      omega
    · have hsum : ∑ k, z k = z i := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          by_contra hj
          exact hother ⟨j, hji, hj⟩
        · simp
      have hfour : (4 : ℤ) ∣ z i := hsum ▸ hz.2
      have hi16 : 16 ≤ z i ^ 2 := by simpa using int_square_ge_dvd hfour hi
      have hbound : z i ^ 2 ≤ ∑ k : Fin 8, z k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ i)
      omega
  · have hnonzero : ∀ i, z i ≠ 0 := by
      intro i hi
      have hd : (2 : ℤ) ∣ z i := by simp [hi]
      have hh := dvd_sub hd (hz.1 i)
      apply heven
      have heq : z i - (z i - z 0) = z 0 := by ring
      rwa [heq] at hh
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin 8 => (1 : ℤ)) (g := fun i => z i ^ 2)
      (fun i _ => int_square_ge_one (hnonzero i))
    simpa using hsum

theorem halfCoordinates_norm_sq (z : Fin 8 → ℤ) :
    ‖halfCoordinates z‖ ^ 2 = (∑ i, (z i : ℝ) ^ 2) / 4 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [halfCoordinates, PiLp.toLp_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem e8Set_norm_sq_lower {x : Ambient 8} (hx : x ∈ e8Set) (hne : x ≠ 0) :
    2 ≤ ‖x‖ ^ 2 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hzne : z ≠ 0 := by intro h; subst z; apply hne; ext i; simp [halfCoordinates]
  have hs : (8 : ℝ) ≤ ∑ i, (z i : ℝ) ^ 2 := by exact_mod_cast e8Numerators_square_sum_ge hz hzne
  rw [halfCoordinates_norm_sq]
  linarith

theorem e8Set_separated {x y : Ambient 8} (hx : x ∈ e8Set) (hy : y ∈ e8Set) (hne : x ≠ y) :
    Real.sqrt 2 ≤ dist x y := by
  have hl := e8Set_norm_sq_lower (e8Set_sub hx hy) (sub_ne_zero.mpr hne)
  rw [dist_eq_norm]
  exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hl⟩

/-- A uniform distance lower bound suffices for local finiteness; no lattice classification. -/
theorem separated_inter_compact_finite {X : Type*} [MetricSpace X]
    {S K : Set X} {r : ℝ} (hr : 0 < r)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ dist x y) (hK : IsCompact K) :
    (S ∩ K).Finite := by
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (r / 3) (by positivity)
  have hf : ∀ b ∈ T, (S ∩ K ∩ Metric.ball b (r / 3)).Finite := by
    intro b _
    apply Set.Subsingleton.finite
    intro x hx y hy
    by_contra hne
    have hl := hS x hx.1.1 y hy.1.1 hne
    have hu : dist x y < r := by
      calc
        dist x y ≤ dist x b + dist b y := dist_triangle _ _ _
        _ < r / 3 + r / 3 := add_lt_add hx.2 (by simpa [dist_comm] using hy.2)
        _ < r := by linarith
    linarith
  apply (hT.biUnion hf).subset
  intro x hx
  obtain ⟨b, hb, hball⟩ := Set.mem_iUnion₂.mp (hcover hx.2)
  exact Set.mem_iUnion₂.mpr ⟨b, hb, hx, hball⟩

theorem e8Set_inter_compact_finite {K : Set (Ambient 8)} (hK : IsCompact K) :
    (e8Set ∩ K).Finite :=
  separated_inter_compact_finite (Real.sqrt_pos.mpr (by norm_num))
    (fun _ hx _ hy hne => e8Set_separated hx hy hne) hK

def e8Configuration : Configuration (Ambient 8) where
  support := e8Set
  finite_on_compacts _ hK := e8Set_inter_compact_finite hK

theorem simpleRoot_norm_sq (i : Fin 8) : ‖halfCoordinates (doubledRoots i)‖ ^ 2 = 2 := by
  rw [halfCoordinates_norm_sq]
  fin_cases i <;> norm_num [doubledRoots, Fin.sum_univ_succ]

theorem simpleRoot_norm (i : Fin 8) : ‖halfCoordinates (doubledRoots i)‖ = Real.sqrt 2 := by
  calc
    _ = Real.sqrt (‖halfCoordinates (doubledRoots i)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 2 := congrArg Real.sqrt (simpleRoot_norm_sq i)

theorem e8Set_minimum_attained : ∃ x ∈ e8Set, x ≠ 0 ∧ ‖x‖ = Real.sqrt 2 := by
  refine ⟨halfCoordinates (doubledRoots 0), simpleRoot_mem_e8 0, ?_, simpleRoot_norm 0⟩
  intro h
  have hs := simpleRoot_norm_sq 0
  rw [h] at hs
  norm_num at hs

end E8Leech
