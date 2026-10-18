import Riesz.SphereChartBiLip8

/-! Grid boxes in chart coordinates (stage NEG, stratification).

Half-open boxes `∏ [h z_i, h(z_i+1))` of side `h` tile `ℝ^8`: they are measurable, pairwise
disjoint, have volume `h^8` and Euclidean diameter at most `√8 h`, and every point lies in the
box of its floor index. Counting by volume: any finite family of distinct boxes inside a
measurable set `U` has at most `vol(U)/h^8` members; for the boxes meeting the boundary layer of
the cube `[-δ,δ]^8` this gives `O(h^(-7))`, the count behind the Minkowski estimate of chart
images of cube boundaries. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

def gridBox8 (h : ℝ) (z : Fin 8 → ℤ) : Set (Fin 8 → ℝ) :=
  Set.pi univ (fun i => Ico (h*(z i)) (h*((z i)+1)))

theorem gridBox8_measurable (h : ℝ) (z : Fin 8 → ℤ) : MeasurableSet (gridBox8 h z) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem gridBox8_volume {h : ℝ} (hh : 0 < h) (z : Fin 8 → ℤ) :
    (volume : Measure (Fin 8 → ℝ)) (gridBox8 h z) = ENNReal.ofReal (h^8) := by
  rw [gridBox8, volume_pi_pi]
  simp only [Real.volume_Ico]
  have he : ∀ i, h*((z i:ℝ)+1)-h*(z i) = h := fun i => by ring
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh.le]

theorem gridBox8_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (fun z z' : Fin 8 → ℤ => Disjoint (gridBox8 h z) (gridBox8 h z')) := by
  intro z z' hzz
  rw [Set.disjoint_left]
  intro p hp hp'
  apply hzz
  funext i
  have h1 := hp i (mem_univ i)
  have h2 := hp' i (mem_univ i)
  have a1 : (z i:ℝ) ≤ p i/h := by rw [le_div_iff₀ hh]; linarith [h1.1]
  have a2 : p i/h < (z i:ℝ)+1 := by rw [div_lt_iff₀ hh]; linarith [h1.2]
  have b1 : (z' i:ℝ) ≤ p i/h := by rw [le_div_iff₀ hh]; linarith [h2.1]
  have b2 : p i/h < (z' i:ℝ)+1 := by rw [div_lt_iff₀ hh]; linarith [h2.2]
  have c1 : (z i:ℝ) < (z' i:ℝ)+1 := lt_of_le_of_lt a1 b2
  have c2 : (z' i:ℝ) < (z i:ℝ)+1 := lt_of_le_of_lt b1 a2
  have d1 : z i < z' i+1 := by exact_mod_cast c1
  have d2 : z' i < z i+1 := by exact_mod_cast c2
  omega

/-- The floor index of a point. -/
def gridIndex8 (h : ℝ) (p : Fin 8 → ℝ) : Fin 8 → ℤ := fun i => ⌊p i/h⌋

theorem mem_gridBox8_gridIndex8 {h : ℝ} (hh : 0 < h) (p : Fin 8 → ℝ) :
    p ∈ gridBox8 h (gridIndex8 h p) := by
  intro i _
  simp only [gridIndex8]
  constructor
  · have := Int.floor_le (p i/h)
    rw [le_div_iff₀ hh] at this
    linarith
  · have := Int.lt_floor_add_one (p i/h)
    rw [div_lt_iff₀ hh] at this
    linarith

theorem gridBox8_abs_sub_lt {h : ℝ} {z : Fin 8 → ℤ} {p q : Fin 8 → ℝ}
    (hp : p ∈ gridBox8 h z) (hq : q ∈ gridBox8 h z) (i : Fin 8) : |p i-q i| < h := by
  have h1 := hp i (mem_univ i)
  have h2 := hq i (mem_univ i)
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Euclidean diameter of a grid box. -/
theorem gridBox8_dist_le {h : ℝ} (hh : 0 < h) {z : Fin 8 → ℤ} {p q : Fin 8 → ℝ}
    (hp : p ∈ gridBox8 h z) (hq : q ∈ gridBox8 h z) :
    dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q) ≤ Real.sqrt 8*h := by
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) i)
      ((WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 8)) i)^2 ≤ 8*h^2 := by
    calc ∑ i, dist ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) i)
          ((WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 8)) i)^2 ≤ ∑ _i : Fin 8, h^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.dist_eq]
          have := gridBox8_abs_sub_lt hp hq i
          have h0 := abs_nonneg (p i-q i)
          nlinarith
      _ = 8*h^2 := by simp
  calc Real.sqrt (∑ i, dist ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) i)
        ((WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 8)) i)^2) ≤ Real.sqrt (8*h^2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 8*h := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hh.le]

/-- Counting by volume: distinct grid boxes inside `U`. -/
theorem gridBox8_card_le {h : ℝ} (hh : 0 < h) (Z : Finset (Fin 8 → ℤ)) {U : Set (Fin 8 → ℝ)}
    (hU : ∀ z ∈ Z, gridBox8 h z ⊆ U) :
    (Z.card:ℝ≥0∞)*ENNReal.ofReal (h^8) ≤ (volume : Measure (Fin 8 → ℝ)) U := by
  have hdisj : Set.PairwiseDisjoint (↑Z) (gridBox8 h) :=
    fun z _ z' _ hzz => gridBox8_disjoint hh hzz
  have hm := measure_biUnion_finset hdisj (fun z _ => gridBox8_measurable h z)
    (μ := (volume : Measure (Fin 8 → ℝ)))
  have hsub : (⋃ z ∈ Z, gridBox8 h z) ⊆ U := iUnion₂_subset hU
  calc (Z.card:ℝ≥0∞)*ENNReal.ofReal (h^8) = ∑ z ∈ Z, (volume : Measure (Fin 8 → ℝ)) (gridBox8 h z) := by
        rw [Finset.sum_congr rfl (fun z _ => gridBox8_volume hh z), Finset.sum_const, nsmul_eq_mul]
    _ = (volume : Measure (Fin 8 → ℝ)) (⋃ z ∈ Z, gridBox8 h z) := hm.symm
    _ ≤ (volume : Measure (Fin 8 → ℝ)) U := measure_mono hsub

#print axioms gridBox8_measurable
#print axioms gridBox8_volume
#print axioms gridBox8_disjoint
#print axioms mem_gridBox8_gridIndex8
#print axioms gridBox8_abs_sub_lt
#print axioms gridBox8_dist_le
#print axioms gridBox8_card_le

end SphericalRiesz
