import Riesz.ChartGridBoxes8

/-! Minkowski estimate for chart images of cube boundaries (stage NEG, stratification).

Fix the chart cube `[-δ,δ]^8` with `δ = ρ_b/12`, where `ρ_b` is the radius on which the
equal-area chart is bi-Lipschitz with constants `1/2, 2`. Grid boxes of side `ρ` meeting the cube
boundary lie in the 16 boundary slabs, of total volume `16·2ρ·(2(δ+ρ))^7`, so there are at most
`32 (2(δ+ρ))^7/ρ^7` of them (counting by volume). Every point within `ρ` of a rotated chart image
of the boundary is within `(2√8+1)ρ` of the image of such a box corner, and spherical caps of
radius `R` have area at most `(4R)^8`: the neighbourhood has area `O(ρ)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

/-- The boundary of the chart cube `[-δ,δ]^8`. -/
def cubeBdry8 (δ : ℝ) : Set (Fin 8 → ℝ) := {w | (∀ i, |w i| ≤ δ) ∧ ∃ i, |w i| = δ}

/-- The boundary slab of the cube in direction `i` and sign `s`. -/
def cubeSlab8 (δ ρ : ℝ) (i : Fin 8) (s : Bool) : Set (Fin 8 → ℝ) :=
  Set.pi univ (fun j => if j = i then Icc ((if s then δ else -δ)-ρ) ((if s then δ else -δ)+ρ)
    else Icc (-(δ+ρ)) (δ+ρ))

theorem cubeSlab8_volume (δ ρ : ℝ) (i : Fin 8) (s : Bool) :
    (volume : Measure (Fin 8 → ℝ)) (cubeSlab8 δ ρ i s) =
      ENNReal.ofReal (2*ρ)*ENNReal.ofReal (2*(δ+ρ))^7 := by
  rw [cubeSlab8, volume_pi_pi]
  have hj : ∀ j, (volume : Measure ℝ) (if j = i then Icc ((if s then δ else -δ)-ρ)
      ((if s then δ else -δ)+ρ) else Icc (-(δ+ρ)) (δ+ρ)) =
      if j = i then ENNReal.ofReal (2*ρ) else ENNReal.ofReal (2*(δ+ρ)) := by
    intro j
    split_ifs <;> rw [Real.volume_Icc] <;> congr 1 <;> ring
  simp only [hj]
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [if_true]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => if_neg (by simpa using hj))]
  simp [Finset.card_compl]

theorem gridBox8_subset_slab {δ ρ : ℝ} {z : Fin 8 → ℤ}
    (hz : (gridBox8 ρ z ∩ cubeBdry8 δ).Nonempty) :
    ∃ i s, gridBox8 ρ z ⊆ cubeSlab8 δ ρ i s := by
  obtain ⟨w, hwb, hw, i, hi⟩ := hz
  have hs : w i = δ ∨ w i = -δ := by
    rcases le_or_gt 0 (w i) with h | h
    · left; rw [abs_of_nonneg h] at hi; exact hi
    · right; rw [abs_of_neg h] at hi; linarith
  refine ⟨i, decide (w i = δ), ?_⟩
  intro p hp j _
  have hpw := gridBox8_abs_sub_lt hp hwb j
  by_cases hji : j = i
  · subst hji
    simp only [if_true]
    rcases hs with h | h
    · have hd : decide (w j = δ) = true := decide_eq_true h
      simp only [hd, if_true]
      rw [abs_lt] at hpw
      constructor <;> linarith
    · by_cases hδ0 : w j = δ
      · have hd : decide (w j = δ) = true := decide_eq_true hδ0
        simp only [hd, if_true]
        rw [abs_lt] at hpw
        constructor <;> linarith
      · have hd : decide (w j = δ) = false := decide_eq_false hδ0
        simp only [hd]
        simp only [Bool.false_eq_true, if_false]
        rw [abs_lt] at hpw
        constructor <;> linarith
  · simp only [if_neg hji]
    have hwj := abs_le.mp (hw j)
    rw [abs_lt] at hpw
    constructor <;> linarith

theorem cubeBdry8_box_finite {δ ρ : ℝ} (hρ : 0 < ρ) :
    {z : Fin 8 → ℤ | (gridBox8 ρ z ∩ cubeBdry8 δ).Nonempty}.Finite := by
  set K : ℤ := ⌈|δ|/ρ⌉+1 with hK
  apply (Set.finite_Icc (fun _ : Fin 8 => -K) (fun _ => K)).subset
  intro z hz
  obtain ⟨w, hwb, hw, _⟩ := hz
  have hb : ∀ i, -K ≤ z i ∧ z i ≤ K := by
    intro i
    have h1 := (hwb i (mem_univ i)).1
    have h2 := (hwb i (mem_univ i)).2
    have hwi := abs_le.mp ((hw i).trans (le_abs_self δ))
    have hc := Int.le_ceil (|δ|/ρ)
    have hKr : (K:ℝ) = ((⌈|δ|/ρ⌉:ℤ):ℝ)+1 := by rw [hK]; push_cast; ring
    have hzu : (z i:ℝ) ≤ |δ|/ρ := by rw [le_div_iff₀ hρ]; linarith
    have h5 : (-|δ|)/ρ < (z i:ℝ)+1 := by rw [div_lt_iff₀ hρ]; linarith
    rw [neg_div] at h5
    have hl : (-(K:ℝ)) < (z i:ℝ) := by linarith
    have hu : (z i:ℝ) ≤ (K:ℝ) := by linarith
    have hl' : -K < z i := by exact_mod_cast hl
    have hu' : z i ≤ K := by exact_mod_cast hu
    exact ⟨hl'.le, hu'⟩
  exact ⟨fun i => (hb i).1, fun i => (hb i).2⟩


theorem toLp_norm_le_of_abs_le {p : Fin 8 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hp : ∀ i, |p i| ≤ a) :
    ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8))‖ ≤ Real.sqrt 8*a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) i‖^2 ≤ 8*a^2 := by
    calc ∑ i, ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) i‖^2 ≤ ∑ _i : Fin 8, a^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have := hp i
          have h0 := abs_nonneg (p i)
          nlinarith [sq_abs (p i)]
      _ = 8*a^2 := by simp
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) i‖^2) ≤ Real.sqrt (8*a^2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 8*a := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq ha]

/-- The chart parameters: a cube `[-2δ,2δ]^8` inside the chart domain on which the chart is
bi-Lipschitz, and the Minkowski estimate for rotated images of the boundary of `[-δ,δ]^8`. -/
theorem chart_boundary_minkowski8 :
    ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ ρ₁ > 0,
      (∀ p : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomain) ∧
      (∀ p q : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
        dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q) ≤
          2*dist (equalAreaPhi p) (equalAreaPhi q) ∧
        dist (equalAreaPhi p) (equalAreaPhi q) ≤
          2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q)) ∧
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
        sphereArea8 {x : Sphere8 | ∃ w ∈ cubeBdry8 δ, dist (x:Ambient9) (g (equalAreaPhi w)) ≤ ρ} ≤
          ENNReal.ofReal (C*ρ) := by
  obtain ⟨ρb, hρb, hρb8, hbi⟩ := equalAreaPhiEuclidean8_near_biLipschitz
  obtain ⟨R₀, hR₀, hcap⟩ := sphereArea8_ball_le
  set δ := ρb/12 with hδdef
  have hδ : 0 < δ := by positivity
  have hs8 : Real.sqrt 8 < 3 := by
    rw [show (3:ℝ) = Real.sqrt 9 by rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs80 : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
  have hball : ∀ p : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) →
      (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) ∈ ball (0 : EuclideanSpace ℝ (Fin 8)) ρb := by
    intro p hp
    rw [mem_ball, dist_zero_right]
    have := toLp_norm_le_of_abs_le (by positivity) hp
    nlinarith
  have hdom : ∀ p : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomain := by
    intro p hp
    have h1 := toLp_norm_le_of_abs_le (by positivity) hp
    have h2 : ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8))‖ ≤ 1/8 := by nlinarith
    simpa using equalAreaEuclidean8_small_norm_domain (WithLp.toLp 2 p) h2
  have hΦ : ∀ p : Fin 8 → ℝ, equalAreaPhi p = equalAreaPhiEuclidean8 (WithLp.toLp 2 p) := by
    intro p
    simp [equalAreaPhiEuclidean8]
  have hbi' : ∀ p q : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhi p) (equalAreaPhi q) ∧
      dist (equalAreaPhi p) (equalAreaPhi q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q) := by
    intro p q hp hq
    rw [hΦ p, hΦ q]
    exact hbi _ (hball p hp) _ (hball q hq)
  refine ⟨δ, hδ, 32*(32:ℝ)^8*(4*δ)^7, by positivity, min δ (R₀/8), lt_min hδ (by positivity),
    hdom, hbi', ?_⟩
  intro g ρ hρ hρ1
  have hρδ : ρ ≤ δ := hρ1.trans (min_le_left _ _)
  have hρR : 8*ρ ≤ R₀ := by have := hρ1.trans (min_le_right _ _); linarith
  set Z := (cubeBdry8_box_finite (δ := δ) hρ).toFinset with hZdef
  -- the number of boundary boxes
  have hcard : (Z.card:ℝ≥0∞)*ENNReal.ofReal (ρ^8) ≤ ENNReal.ofReal (32*ρ*(4*δ)^7) := by
    have hsub : ∀ z ∈ Z, gridBox8 ρ z ⊆ ⋃ (is : Fin 8 × Bool), cubeSlab8 δ ρ is.1 is.2 := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      obtain ⟨i, s, hi⟩ := gridBox8_subset_slab hz
      exact hi.trans (subset_iUnion_of_subset (i, s) subset_rfl)
    have h1 := gridBox8_card_le hρ Z hsub
    have h2 : (volume : Measure (Fin 8 → ℝ)) (⋃ (is : Fin 8 × Bool), cubeSlab8 δ ρ is.1 is.2) ≤
        ∑ is : Fin 8 × Bool, (volume : Measure (Fin 8 → ℝ)) (cubeSlab8 δ ρ is.1 is.2) :=
      measure_iUnion_fintype_le _ _
    have h3 : ∑ is : Fin 8 × Bool, (volume : Measure (Fin 8 → ℝ)) (cubeSlab8 δ ρ is.1 is.2) =
        16*(ENNReal.ofReal (2*ρ)*ENNReal.ofReal (2*(δ+ρ))^7) := by
      simp only [cubeSlab8_volume, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      norm_num
    have h4 : 16*(ENNReal.ofReal (2*ρ)*ENNReal.ofReal (2*(δ+ρ))^7) ≤
        ENNReal.ofReal (32*ρ*(4*δ)^7) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        show (16:ℝ≥0∞) = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have h5 : (2*(δ+ρ))^7 ≤ (4*δ)^7 := pow_le_pow_left₀ (by positivity) (by linarith) 7
      have h6 : 0 ≤ 2*ρ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h5 h6]
    exact h1.trans (h2.trans (h3.le.trans h4))
  -- the covering by caps
  have hpt : ∀ z : Fin 8 → ℤ, z ∈ Z → equalAreaPhi (fun i => ρ*(z i)) ∈ sphere (0:Ambient9) 1 := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    obtain ⟨w, hwb, hw, _⟩ := hz
    have hc : ∀ i, |ρ*(z i)| ≤ 2*δ := by
      intro i
      have h1 := (hwb i (mem_univ i)).1
      have h2 := (hwb i (mem_univ i)).2
      have hwi := abs_le.mp (hw i)
      rw [abs_le]
      constructor <;> nlinarith
    exact equalAreaPhi_mem_sphere _ (hdom _ hc).1
  let q : (Fin 8 → ℤ) → Sphere8 := fun z =>
    if hz : z ∈ Z then ⟨g (equalAreaPhi (fun i => ρ*(z i))), by
      have := hpt z hz
      simp only [mem_sphere_zero_iff_norm] at this ⊢
      rw [g.norm_map]; exact this⟩
    else northPole8
  have hcover : {x : Sphere8 | ∃ w ∈ cubeBdry8 δ, dist (x:Ambient9) (g (equalAreaPhi w)) ≤ ρ} ⊆
      ⋃ z ∈ Z, {x : Sphere8 | dist x (q z) < 8*ρ} := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hx
    set z := gridIndex8 ρ w with hzdef
    have hwz : w ∈ gridBox8 ρ z := mem_gridBox8_gridIndex8 hρ w
    have hzZ : z ∈ Z := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨w, hwz, hw⟩
    have hcz : (fun i => ρ*(z i)) ∈ gridBox8 ρ z := by
      intro i _
      constructor
      · exact le_rfl
      · nlinarith
    have hwabs : ∀ i, |w i| ≤ 2*δ := fun i => (hw.1 i).trans (by linarith)
    have hcabs : ∀ i, |ρ*(z i)| ≤ 2*δ := by
      intro i
      have h1 := (hwz i (mem_univ i)).1
      have h2 := (hwz i (mem_univ i)).2
      have hwi := abs_le.mp (hw.1 i)
      rw [abs_le]
      constructor <;> nlinarith
    have hd := gridBox8_dist_le hρ hwz hcz
    have hb := (hbi' w (fun i => ρ*(z i)) hwabs hcabs).2
    refine mem_iUnion₂.mpr ⟨z, hzZ, ?_⟩
    simp only [mem_setOf_eq, q, dif_pos hzZ]
    rw [Subtype.dist_eq]
    change dist (x:Ambient9) (g (equalAreaPhi (fun i => ρ*(z i)))) < 8*ρ
    have hrot : dist (g (equalAreaPhi w)) (g (equalAreaPhi (fun i => ρ*(z i)))) =
        dist (equalAreaPhi w) (equalAreaPhi (fun i => ρ*(z i))) := g.dist_map _ _
    calc dist (x:Ambient9) (g (equalAreaPhi (fun i => ρ*(z i))))
        ≤ dist (x:Ambient9) (g (equalAreaPhi w))+
          dist (g (equalAreaPhi w)) (g (equalAreaPhi (fun i => ρ*(z i)))) := dist_triangle _ _ _
      _ ≤ ρ+2*(Real.sqrt 8*ρ) := by rw [hrot]; nlinarith
      _ < 8*ρ := by nlinarith
  calc sphereArea8 {x : Sphere8 | ∃ w ∈ cubeBdry8 δ, dist (x:Ambient9) (g (equalAreaPhi w)) ≤ ρ}
      ≤ sphereArea8 (⋃ z ∈ Z, {x : Sphere8 | dist x (q z) < 8*ρ}) := measure_mono hcover
    _ ≤ ∑ z ∈ Z, sphereArea8 {x : Sphere8 | dist x (q z) < 8*ρ} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ Z, ENNReal.ofReal ((4*(8*ρ))^8) :=
        Finset.sum_le_sum fun z _ => hcap (q z) (8*ρ) (by positivity) hρR
    _ = (Z.card:ℝ≥0∞)*ENNReal.ofReal (ρ^8)*ENNReal.ofReal ((32:ℝ)^8) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (32*ρ*(4*δ)^7)*ENNReal.ofReal ((32:ℝ)^8) := by gcongr
    _ = ENNReal.ofReal (32*(32:ℝ)^8*(4*δ)^7*ρ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

#print axioms cubeSlab8_volume
#print axioms gridBox8_subset_slab
#print axioms cubeBdry8_box_finite
#print axioms toLp_norm_le_of_abs_le
#print axioms chart_boundary_minkowski8

end SphericalRiesz
