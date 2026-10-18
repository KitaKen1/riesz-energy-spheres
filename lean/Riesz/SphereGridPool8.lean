import Riesz.CarryOverSlices
import Riesz.SphereAtomless8
import Riesz.SphereValue8
import Riesz.SphereRieszNegMellin8

/-! Pools of small mass split into exact-mass cells of coarse diameter (stage NEG, stratification).

* The level sets of the first coordinate are null for the sphere probability: the cone over
  `{x₀ = c}` lies in `{v₀ = c ‖v‖}`, whose sections over `(v₁,…,v₈) ≠ 0` have at most one
  point (Fubini).
* The ambient grid of side `H` cuts the sphere into `(2⌈1/H⌉+1)^9` measurable disjoint pieces of
  diameter at most `3H`.
* Pool partition: any measurable `P` splits into `n` cells of mass exactly `σ(P)/n` with
  `Σ_j d_j² ≤ n (3H)² + 4 (2⌈1/H⌉+1)^9` (carry-over slicing along the grid; at most one cell per
  grid piece straddles, with diameter at most 2). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Pointwise
namespace SphericalRiesz

theorem ambient_cone_level_null (c : ℝ) :
    (volume : Measure Ambient9) {v | v 0 = c*‖v‖} = 0 := by
  have hmeas : MeasurableSet {v : Ambient9 | v 0 = c*‖v‖} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  rw [← ambientCons9_measurePreserving.map_eq, Measure.map_apply ambientCons9.measurable hmeas]
  have hE : MeasurableSet (ambientCons9 ⁻¹' {v : Ambient9 | v 0 = c*‖v‖}) :=
    ambientCons9.measurable hmeas
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hE]
  have ht : ∀ᵐ w ∂(volume : Measure (Fin 8 → ℝ)), w ≠ 0 := by simp [ae_iff]
  have hzero : (fun w : Fin 8 → ℝ => (volume : Measure ℝ)
      ((fun a => (a, w)) ⁻¹' (ambientCons9 ⁻¹' {v : Ambient9 | v 0 = c*‖v‖}))) =ᵐ[volume] 0 := by
    filter_upwards [ht] with w hw
    simp only [Pi.zero_apply]
    apply Set.Subsingleton.measure_zero
    set s := ‖(WithLp.toLp 2 w : PoleTransverse8)‖^2 with hsdef
    have hs : 0 < s := by
      rw [hsdef]
      have : (WithLp.toLp 2 w : PoleTransverse8) ≠ 0 := by
        intro h
        apply hw
        have := congrArg WithLp.ofLp h
        simpa using this
      positivity
    have hsec : ∀ a, a ∈ (fun a => (a, w)) ⁻¹' (ambientCons9 ⁻¹' {v : Ambient9 | v 0 = c*‖v‖}) ↔
        a = c*Real.sqrt (a^2+s) := by
      intro a
      simp only [mem_preimage, mem_setOf_eq]
      rw [ambientCons9_norm]
      have h0 : (ambientCons9 (a, w)) 0 = a := by simp [ambientCons9_apply]
      rw [h0]
    intro a ha b hb
    rw [hsec] at ha hb
    have hA := Real.sqrt_pos.mpr (show 0 < a^2+s by positivity)
    have hB := Real.sqrt_pos.mpr (show 0 < b^2+s by positivity)
    have hA2 := Real.sq_sqrt (show 0 ≤ a^2+s by positivity)
    have hB2 := Real.sq_sqrt (show 0 ≤ b^2+s by positivity)
    by_cases hc : c = 0
    · rw [hc, zero_mul] at ha hb
      rw [ha, hb]
    have ha2 : a^2 = c^2*(a^2+s) := by
      rw [← hA2]
      nth_rewrite 1 [ha]
      ring
    have hb2 : b^2 = c^2*(b^2+s) := by
      rw [← hB2]
      nth_rewrite 1 [hb]
      ring
    have hc2 : c^2 ≠ 1 := by
      intro h1
      rw [h1] at ha2
      linarith
    have hsq : a^2 = b^2 := by
      have h1 : (a^2-b^2)*(1-c^2) = 0 := by linear_combination ha2-hb2
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact absurd (by linarith : c^2 = 1) hc2
    have hab : 0 < a*b := by
      rw [ha, hb]
      have : 0 < c^2 := by positivity
      nlinarith [mul_pos hA hB]
    have hfac : (a-b)*(a+b) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have : b = -a := by linarith
      rw [this] at hab
      nlinarith [sq_nonneg a]
  rw [lintegral_congr_ae hzero]
  simp

/-- The level sets of the first coordinate are null for the sphere probability. -/
theorem sphereProbability8_coord_level_null (c : ℝ) :
    sphereProbability8 {x : Sphere8 | (x:Ambient9) 0 = c} = 0 := by
  have hmeas : MeasurableSet {x : Sphere8 | (x:Ambient9) 0 = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hcone : Ioo (0:ℝ) 1 • (Subtype.val '' {x : Sphere8 | (x:Ambient9) 0 = c}) ⊆
      {v : Ambient9 | v 0 = c*‖v‖} := by
    rintro z ⟨r, hr, w, ⟨y, hy, rfl⟩, rfl⟩
    simp only [mem_setOf_eq] at hy ⊢
    have hy1 : ‖(y:Ambient9)‖ = 1 := by simpa using y.2
    have hsm : (r • (y:Ambient9)) 0 = r*(y:Ambient9) 0 := by simp
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hy1, hy]
    ring
  simp only [sphereProbability8, Measure.smul_apply, smul_eq_mul]
  unfold sphereArea8
  rw [Measure.toSphere_apply' _ hmeas, measure_mono_null hcone (ambient_cone_level_null c),
    mul_zero, mul_zero]

theorem sphere8_abs_coord_le_one (x : Sphere8) (i : Fin 9) : |(x:Ambient9) i| ≤ 1 := by
  have hx : ‖(x:Ambient9)‖ = 1 := by simpa using x.2
  have h1 : ((x:Ambient9) i)^2 ≤ ‖(x:Ambient9)‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun j => ((x:Ambient9) j)^2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  rw [hx, one_pow] at h1
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

/-- The cells of the ambient grid of side `H` met by the sphere. -/
def ambientGridCell8 (H : ℝ) (m : ℕ) (k : Fin 9 → Fin (2*m+1)) : Set Sphere8 :=
  {x | ∀ i, ⌊(x:Ambient9) i/H⌋+(m:ℤ) = ((k i : ℕ) : ℤ)}

theorem ambientGridCell8_measurable (H : ℝ) (m : ℕ) (k : Fin 9 → Fin (2*m+1)) :
    MeasurableSet (ambientGridCell8 H m k) := by
  have : ambientGridCell8 H m k = ⋂ i, {x : Sphere8 | ⌊(x:Ambient9) i/H⌋+(m:ℤ) = ((k i : ℕ) : ℤ)} := by
    ext x
    simp [ambientGridCell8]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun x : Sphere8 => ⌊(x:Ambient9) i/H⌋+(m:ℤ)) :=
    (Int.measurable_floor.comp (by fun_prop)).add_const _
  exact hm (measurableSet_singleton _)

theorem ambientGridCell8_disjoint (H : ℝ) (m : ℕ) :
    Pairwise (fun k k' : Fin 9 → Fin (2*m+1) =>
      Disjoint (ambientGridCell8 H m k) (ambientGridCell8 H m k')) := by
  intro k k' hkk
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hkk
  funext i
  have h1 := hx i
  have h2 := hx' i
  apply Fin.ext
  exact_mod_cast h1.symm.trans h2

theorem ambientGridCell8_cover {H : ℝ} (hH : 0 < H) (x : Sphere8) :
    ∃ k, x ∈ ambientGridCell8 H ⌈1/H⌉₊ k := by
  set m := ⌈1/H⌉₊ with hmdef
  have hmH : 1/H ≤ (m:ℝ) := Nat.le_ceil _
  have hb : ∀ i, 0 ≤ ⌊(x:Ambient9) i/H⌋+(m:ℤ) ∧ ⌊(x:Ambient9) i/H⌋+(m:ℤ) < 2*(m:ℤ)+1 := by
    intro i
    have hxi := abs_le.mp (sphere8_abs_coord_le_one x i)
    have hlo : -(1/H) ≤ (x:Ambient9) i/H := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hxi.1 hH.le
    have hhi : (x:Ambient9) i/H ≤ 1/H := div_le_div_of_nonneg_right hxi.2 hH.le
    have h1 : -((m:ℤ)) ≤ ⌊(x:Ambient9) i/H⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have h2 : ⌊(x:Ambient9) i/H⌋ ≤ (m:ℤ) := by
      have h3 : ((⌊(x:Ambient9) i/H⌋ : ℤ) : ℝ) ≤ (m:ℝ) := (Int.floor_le _).trans (hhi.trans hmH)
      exact_mod_cast h3
    constructor <;> omega
  refine ⟨fun i => ⟨(⌊(x:Ambient9) i/H⌋+(m:ℤ)).toNat, ?_⟩, ?_⟩
  · have := hb i
    omega
  · intro i
    have := hb i
    simp only
    rw [Int.toNat_of_nonneg this.1]

theorem ambientGridCell8_dist_le {H : ℝ} (hH : 0 < H) (m : ℕ) (k : Fin 9 → Fin (2*m+1))
    {x y : Sphere8} (hx : x ∈ ambientGridCell8 H m k) (hy : y ∈ ambientGridCell8 H m k) :
    dist x y ≤ 3*H := by
  have hi : ∀ i, |(x:Ambient9) i-(y:Ambient9) i| < H := by
    intro i
    have h := (hx i).trans (hy i).symm
    have hfl : ⌊(x:Ambient9) i/H⌋ = ⌊(y:Ambient9) i/H⌋ := by linarith
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    rw [← sub_div, abs_div, abs_of_pos hH, div_lt_one hH] at h1
    exact h1
  have hsq : dist x y^2 ≤ (3*H)^2 := by
    rw [Subtype.dist_eq, EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    calc ∑ i, dist ((x:Ambient9) i) ((y:Ambient9) i)^2 ≤ ∑ _i : Fin 9, H^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.dist_eq]
          have := hi i
          have h0 := abs_nonneg ((x:Ambient9) i-(y:Ambient9) i)
          nlinarith
      _ = (3*H)^2 := by simp; ring
  have h0 : 0 ≤ 3*H := by positivity
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Pool partition: exact-mass cells whose diameters are controlled by the grid scale, up to at
most `(2⌈1/H⌉+1)^9` straddling cells. -/
theorem sphere8_pool_partition {P : Set Sphere8} (hP : MeasurableSet P) {H : ℝ} (hH : 0 < H)
    {n : ℕ} (hn : 0 < n) :
    ∃ C : Fin n → Set Sphere8, ∃ dm : Fin n → ℝ, (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = P ∧
      (∀ j, sphereProbability8.real (C j) = sphereProbability8.real P/n) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
      ∑ j, (dm j)^2 ≤ n*(3*H)^2+4*(2*⌈1/H⌉₊+1)^9 := by
  classical
  set m := ⌈1/H⌉₊ with hmdef
  let e := Fintype.equivFin (Fin 9 → Fin (2*m+1))
  set M := Fintype.card (Fin 9 → Fin (2*m+1)) with hMdef
  have hMval : M = (2*m+1)^9 := by
    rw [hMdef, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  let Q : Fin M → Set Sphere8 := fun j => ambientGridCell8 H m (e.symm j)
  have hQm : ∀ j, MeasurableSet (Q j) := fun j => ambientGridCell8_measurable H m _
  have hQd : Pairwise (fun i j => Disjoint (Q i) (Q j)) := by
    intro i j hij
    exact ambientGridCell8_disjoint H m (fun h => hij (e.symm.injective h))
  have hPQ : P ⊆ ⋃ j, Q j := by
    intro x _
    obtain ⟨k, hk⟩ := ambientGridCell8_cover hH x
    exact mem_iUnion.mpr ⟨e k, by simp only [Q, e.symm_apply_apply]; exact hk⟩
  have hg : Measurable (fun x : Sphere8 => (x:Ambient9) 0) := by fun_prop
  have hgnull : ∀ c, sphereProbability8 ((fun x : Sphere8 => (x:Ambient9) 0) ⁻¹' {c} ∩ P) = 0 :=
    fun c => measure_mono_null inter_subset_left (sphereProbability8_coord_level_null c)
  obtain ⟨C, hCm, hCd, hCu, hCmass, T, hT, hTsub⟩ := exists_exact_mass_carry_slices
    sphereProbability8 hP Q hQm hQd hPQ hg (fun x => sphere8_abs_coord_le_one x 0) hgnull hn
  refine ⟨C, fun j => if j ∈ T then 2 else 3*H, hCm, hCd, hCu, hCmass, ?_, ?_⟩
  · intro j x hx y hy
    by_cases hj : j ∈ T
    · simp only [if_pos hj]
      exact sphere8_dist_le_two x y
    · simp only [if_neg hj]
      obtain ⟨k, hxk, hyk⟩ := hTsub j hj x hx y hy
      exact ambientGridCell8_dist_le hH m (e.symm k) hxk hyk
  · have hsplit : ∑ j, (if j ∈ T then (2:ℝ) else 3*H)^2 ≤ ∑ j : Fin n, ((3*H)^2+(if j ∈ T then 4 else 0)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ T
      · simp only [if_pos hj]
        nlinarith [sq_nonneg (3*H)]
      · simp only [if_neg hj]
        linarith
    have hcount : ∑ j : Fin n, (if j ∈ T then (4:ℝ) else 0) = 4*T.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hcount] at hsplit
    have hT' : T.card ≤ (2*m+1)^9 := hMval ▸ hT
    have hTM : (T.card:ℝ) ≤ (2*(m:ℝ)+1)^9 := by exact_mod_cast hT'
    nlinarith

#print axioms ambient_cone_level_null
#print axioms sphereProbability8_coord_level_null
#print axioms sphere8_abs_coord_le_one
#print axioms ambientGridCell8_measurable
#print axioms ambientGridCell8_disjoint
#print axioms ambientGridCell8_cover
#print axioms ambientGridCell8_dist_le
#print axioms sphere8_pool_partition

end SphericalRiesz
