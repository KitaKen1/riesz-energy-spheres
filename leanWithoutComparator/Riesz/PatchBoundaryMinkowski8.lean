import Riesz.SphereChartPool8
import Riesz.NegAllN8
import Riesz.RationalResidualPoints8
import Riesz.CubeLebesgue

/-! Minkowski bounds for the frontiers of E8 cube patches (stage NEG, residual stratification).

If `F` is Lipschitz on the unit cube `[0,1]^8`, the `ρ`-neighbourhood on `S⁸` of the image of the
cube boundary has area `O(ρ)`: the boundary is covered by the `16 (m+1)^7` face grid points of
mesh `1/m ≤ ρ`, and each neighbourhood piece lies in a spherical cap of radius `O(ρ)`, of area
`O(ρ^8)`. Every small E8 cube patch map is `C^∞` on the closed cube, hence Lipschitz there; the
image of the open cube is open in the sphere, so the frontier of a patch lies in the image of the
cube boundary. Hence the frontier of the complement of any finite union of patches has a linear
Minkowski bound. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal ContDiff
namespace SphericalRiesz
open Boundary

/-- The boundary of the unit cube `[0,1]^8`. -/
def unitCubeBdry8 : Set (Fin 8 → ℝ) := {w | w ∈ UnitCube 8 ∧ ∃ i, w i = 0 ∨ w i = 1}

/-- The open unit cube `(0,1)^8`. -/
def unitCubeOpen8 : Set (Fin 8 → ℝ) := Set.pi univ (fun _ => Ioo (0:ℝ) 1)

theorem unitCubeOpen8_isOpen : IsOpen unitCubeOpen8 :=
  isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem unitCubeOpen8_subset : unitCubeOpen8 ⊆ UnitCube 8 := by
  intro w hw i
  have := hw i (mem_univ i)
  exact ⟨this.1.le, this.2.le⟩

/-- Grid points on the faces of the unit cube: coordinate `i` is `0` or `1`, the others are
multiples of `1/m`. -/
def cubeFacePoint8 (m : ℕ) (q : Fin 8 × Bool × (Fin 7 → Fin (m+1))) : Fin 8 → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) q.1 (if q.2.1 then (1:ℝ) else 0) (fun j => ((q.2.2 j : ℕ):ℝ)/m)

theorem cubeFacePoint8_mem {m : ℕ} (hm : 0 < m) (q : Fin 8 × Bool × (Fin 7 → Fin (m+1))) :
    cubeFacePoint8 m q ∈ UnitCube 8 := by
  intro j
  rcases Fin.eq_self_or_eq_succAbove q.1 j with h | ⟨j', rfl⟩
  · subst h
    simp only [cubeFacePoint8, Fin.insertNth_apply_same]
    split_ifs <;> norm_num
  · simp only [cubeFacePoint8, Fin.insertNth_apply_succAbove]
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hk : ((q.2.2 j' : ℕ):ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (q.2.2 j').isLt
    exact ⟨by positivity, (div_le_one hmR).mpr hk⟩

theorem exists_cubeFacePoint8_near {m : ℕ} (hm : 0 < m) {w : Fin 8 → ℝ} (hw : w ∈ unitCubeBdry8) :
    ∃ q : Fin 8 × Bool × (Fin 7 → Fin (m+1)), dist w (cubeFacePoint8 m q) ≤ 1/m := by
  obtain ⟨hwc, i, hi⟩ := hw
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hk : ∀ j : Fin 7, ⌊(m:ℝ)*w (i.succAbove j)⌋₊ < m+1 := by
    intro j
    have h1 : (m:ℝ)*w (i.succAbove j) ≤ m := by
      have := (hwc (i.succAbove j)).2
      nlinarith
    have := Nat.floor_le_floor (a := (m:ℝ)*w (i.succAbove j)) h1
    rw [Nat.floor_natCast] at this
    omega
  refine ⟨(i, decide (w i = 1), fun j => ⟨⌊(m:ℝ)*w (i.succAbove j)⌋₊, hk j⟩), ?_⟩
  rw [dist_pi_le_iff (by positivity)]
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨j', rfl⟩
  · subst h
    simp only [cubeFacePoint8, Fin.insertNth_apply_same]
    rcases hi with h0 | h1
    · have hd : decide (w j = 1) = false := decide_eq_false (by rw [h0]; norm_num)
      rw [hd, if_neg (by decide), h0, dist_self]
      positivity
    · have hd : decide (w j = 1) = true := decide_eq_true h1
      rw [hd, if_pos rfl, h1, dist_self]
      positivity
  · simp only [cubeFacePoint8, Fin.insertNth_apply_succAbove]
    rw [Real.dist_eq]
    have h0 : 0 ≤ (m:ℝ)*w (i.succAbove j') := by
      have := (hwc (i.succAbove j')).1
      positivity
    have hf1 := Nat.floor_le h0
    have hf2 := Nat.lt_floor_add_one ((m:ℝ)*w (i.succAbove j'))
    have e : w (i.succAbove j')-(⌊(m:ℝ)*w (i.succAbove j')⌋₊:ℝ)/m =
        ((m:ℝ)*w (i.succAbove j')-⌊(m:ℝ)*w (i.succAbove j')⌋₊)/m := by
      field_simp
    rw [e, abs_div, abs_of_pos hmR, div_le_div_iff_of_pos_right hmR, abs_le]
    constructor <;> linarith

/-- Minkowski bound for Lipschitz images of the boundary of the unit cube. -/
theorem lipschitz_cubeBdry_minkowski8 {F : (Fin 8 → ℝ) → Ambient9} {L : ℝ≥0}
    (hF : LipschitzOnWith L F (UnitCube 8)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      sphereArea8 {x : Sphere8 | ∃ w ∈ unitCubeBdry8, dist (x:Ambient9) (F w) ≤ ρ} ≤
        ENNReal.ofReal (C*ρ) := by
  classical
  obtain ⟨R₀, hR₀, hcap⟩ := sphereArea8_ball_le
  obtain ⟨L', hL'⟩ : ∃ L' : ℝ, L' = (L:ℝ)+1 := ⟨_, rfl⟩
  have hL'pos : 0 < L' := by rw [hL']; positivity
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = min 1 (R₀/(3*L')) := ⟨_, rfl⟩
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; exact lt_min one_pos (by positivity)
  have hρ₀1 : ρ₀ ≤ 1 := by rw [hρ₀]; exact min_le_left _ _
  have hρ₀R : 3*L'*ρ₀ ≤ R₀ := by
    have h := min_le_right 1 (R₀/(3*L'))
    rw [← hρ₀, le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = sphereArea8.real univ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact measureReal_nonneg
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 16*3^7*(12*L')^8 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  refine ⟨max C₁ (A/ρ₀), le_max_of_le_left hC₁0, fun ρ hρ => ?_⟩
  by_cases hbig : ρ₀ < ρ
  · calc sphereArea8 _ ≤ sphereArea8 univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal A := by rw [hA, ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (max C₁ (A/ρ₀)*ρ) := by
          apply ENNReal.ofReal_le_ofReal
          calc A = A/ρ₀*ρ₀ := by field_simp
            _ ≤ A/ρ₀*ρ := mul_le_mul_of_nonneg_left hbig.le (by positivity)
            _ ≤ max C₁ (A/ρ₀)*ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.le
  have hρρ₀ : ρ ≤ ρ₀ := not_lt.mp hbig
  have hρ1 : ρ ≤ 1 := hρρ₀.trans hρ₀1
  set m := ⌈1/ρ⌉₊ with hm
  have hmpos : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hmR : (0:ℝ) < m := by exact_mod_cast hmpos
  have hm1 : 1/(m:ℝ) ≤ ρ := (one_div_le hmR hρ).mpr (Nat.le_ceil _)
  have hm2 : ((m:ℝ)+1)*ρ ≤ 3 := by
    have h1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1/ρ by positivity)
    rw [← hm] at h1
    have h2 : (1/ρ)*ρ = 1 := by field_simp
    nlinarith
  -- the cover by caps around the images of face grid points
  let T : Fin 8 × Bool × (Fin 7 → Fin (m+1)) → Set Sphere8 := fun q =>
    {x : Sphere8 | dist (x:Ambient9) (F (cubeFacePoint8 m q)) ≤ L'*ρ}
  have hsub : {x : Sphere8 | ∃ w ∈ unitCubeBdry8, dist (x:Ambient9) (F w) ≤ ρ} ⊆ ⋃ q, T q := by
    rintro x ⟨w, hw, hxw⟩
    obtain ⟨q, hq⟩ := exists_cubeFacePoint8_near hmpos hw
    refine mem_iUnion.mpr ⟨q, ?_⟩
    show dist (x:Ambient9) (F (cubeFacePoint8 m q)) ≤ L'*ρ
    have hFw := hF.dist_le_mul w hw.1 (cubeFacePoint8 m q) (cubeFacePoint8_mem hmpos q)
    have hwq : dist w (cubeFacePoint8 m q) ≤ ρ := hq.trans hm1
    have hL0 : (0:ℝ) ≤ L := L.2
    have : (L:ℝ)*dist w (cubeFacePoint8 m q) ≤ L*ρ := mul_le_mul_of_nonneg_left hwq hL0
    calc dist (x:Ambient9) (F (cubeFacePoint8 m q)) ≤ dist (x:Ambient9) (F w)+
          dist (F w) (F (cubeFacePoint8 m q)) := dist_triangle _ _ _
      _ ≤ ρ+L*ρ := by linarith
      _ = L'*ρ := by rw [hL']; ring
  have hT : ∀ q, sphereArea8 (T q) ≤ ENNReal.ofReal ((12*L'*ρ)^8) := by
    intro q
    rcases (T q).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he, measure_empty]; exact zero_le
    · have hsub' : T q ⊆ {y : Sphere8 | dist y x₀ < 3*L'*ρ} := by
        intro y hy
        show dist y x₀ < 3*L'*ρ
        have h1 : dist (y:Ambient9) (F (cubeFacePoint8 m q)) ≤ L'*ρ := hy
        have h2 : dist (x₀:Ambient9) (F (cubeFacePoint8 m q)) ≤ L'*ρ := hx₀
        have h3 : dist (y:Ambient9) (x₀:Ambient9) ≤ dist (y:Ambient9) (F (cubeFacePoint8 m q))+
            dist (x₀:Ambient9) (F (cubeFacePoint8 m q)) := dist_triangle_right _ _ _
        have h4 : 0 < L'*ρ := by positivity
        rw [Subtype.dist_eq]
        linarith
      have h3R : 3*L'*ρ ≤ R₀ :=
        (mul_le_mul_of_nonneg_left hρρ₀ (by positivity)).trans hρ₀R
      calc sphereArea8 (T q) ≤ sphereArea8 {y : Sphere8 | dist y x₀ < 3*L'*ρ} := measure_mono hsub'
        _ ≤ ENNReal.ofReal ((4*(3*L'*ρ))^8) := hcap x₀ _ (by positivity) h3R
        _ = ENNReal.ofReal ((12*L'*ρ)^8) := by ring_nf
  have hcard : Fintype.card (Fin 8 × Bool × (Fin 7 → Fin (m+1))) = 16*(m+1)^7 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_fun]
    ring
  calc sphereArea8 {x : Sphere8 | ∃ w ∈ unitCubeBdry8, dist (x:Ambient9) (F w) ≤ ρ}
      ≤ sphereArea8 (⋃ q, T q) := measure_mono hsub
    _ ≤ ∑ q, sphereArea8 (T q) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : Fin 8 × Bool × (Fin 7 → Fin (m+1)), ENNReal.ofReal ((12*L'*ρ)^8) :=
        Finset.sum_le_sum fun q _ => hT q
    _ = ENNReal.ofReal ((16*((m:ℝ)+1)^7)*(12*L'*ρ)^8) := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal (max C₁ (A/ρ₀)*ρ) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (16*((m:ℝ)+1)^7)*(12*L'*ρ)^8 = 16*(12*L')^8*(((m:ℝ)+1)*ρ)^7*ρ := by ring
        rw [e]
        have h7 : (((m:ℝ)+1)*ρ)^7 ≤ 3^7 := pow_le_pow_left₀ (by positivity) hm2 7
        have h8 : 16*(12*L')^8*(((m:ℝ)+1)*ρ)^7 ≤ C₁ := by
          rw [hC₁]
          have : (0:ℝ) ≤ 16*(12*L')^8 := by positivity
          nlinarith
        calc 16*(12*L')^8*(((m:ℝ)+1)*ρ)^7*ρ ≤ C₁*ρ := mul_le_mul_of_nonneg_right h8 hρ.le
          _ ≤ max C₁ (A/ρ₀)*ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le

/-- Small E8 cube patch maps are Lipschitz on the closed unit cube. -/
theorem smallE8CubeMap8_lipschitz (p : SmallE8CubePatch8) :
    ∃ L : ℝ≥0, LipschitzOnWith L (smallE8CubeMap8 p) (UnitCube 8) := by
  have hloc : LocallyLipschitzOn (UnitCube 8) (smallE8CubeMap8 p) := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ :=
      ((smallE8CubeMap8_contDiffAt p x hx).of_le (by simp)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩
  exact hloc.exists_lipschitzOnWith_of_compact (unitCube_isCompact 8)

theorem smallE8CubeSet8_eq (p : SmallE8CubePatch8) :
    smallE8CubeSet8 p = {x : Sphere8 | ∃ w ∈ UnitCube 8, (x:Ambient9) = smallE8CubeMap8 p w} := by
  ext x
  simp only [smallE8CubeSet8, equalAreaE8SpherePatch8, mem_preimage, mem_image, mem_setOf_eq,
    smallE8CubeMap8]
  constructor
  · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, hx.symm⟩
  · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, hx.symm⟩

theorem equalAreaE8Affine8_isOpenMap (v c : Fin 8 → ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    IsOpenMap (equalAreaE8Affine8 v c ε) := by
  have he : IsOpenMap e8Map :=
    (e8Basis.equivFun.symm.toContinuousLinearEquiv : (Fin 8 → ℝ) ≃L[ℝ] (Fin 8 → ℝ)).isOpenMap
  have hcomp : equalAreaE8Affine8 v c ε =
      (fun y => v+y) ∘ (fun y => ε • y) ∘ e8Map ∘ (fun x => x-c) := by
    funext x; rfl
  rw [hcomp]
  exact (isOpenMap_add_left v).comp ((isOpenMap_smul₀ hε).comp (he.comp (isOpenMap_sub_right c)))

/-- The image of the open cube under a patch map is open in the sphere. -/
theorem smallE8_openImage_isOpen (p : SmallE8CubePatch8) :
    IsOpen {x : Sphere8 | ∃ w ∈ unitCubeOpen8, (x:Ambient9) = smallE8CubeMap8 p w} := by
  have hset : {x : Sphere8 | ∃ w ∈ unitCubeOpen8, (x:Ambient9) = smallE8CubeMap8 p w} =
      chartImage8 p.g (equalAreaE8Affine8 p.v p.c p.ε '' unitCubeOpen8) := by
    ext x
    simp only [mem_setOf_eq, chartImage8, mem_image]
    constructor
    · rintro ⟨w, hw, hx⟩; exact ⟨_, ⟨w, hw, rfl⟩, hx⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, hx⟩; exact ⟨w, hw, hx⟩
  rw [hset]
  apply chartImage8_isOpen
  · exact equalAreaE8Affine8_isOpenMap p.v p.c p.ε_pos.ne' _ unitCubeOpen8_isOpen
  · exact (image_mono unitCubeOpen8_subset).trans
      (equalAreaE8Affine8_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small)

/-- The frontier of a patch lies in the image of the cube boundary. -/
theorem smallE8CubeSet8_frontier (p : SmallE8CubePatch8) :
    frontier (smallE8CubeSet8 p) ⊆
      {x : Sphere8 | ∃ w ∈ unitCubeBdry8, (x:Ambient9) = smallE8CubeMap8 p w} := by
  intro x hx
  have hcl := (smallE8CubeSet8_isCompact p).isClosed
  rw [frontier, hcl.closure_eq] at hx
  obtain ⟨hxS, hxi⟩ := hx
  have hxS' := hxS
  rw [smallE8CubeSet8_eq] at hxS'
  obtain ⟨w, hw, hxw⟩ := hxS'
  refine ⟨w, ⟨hw, ?_⟩, hxw⟩
  by_contra hne
  have hwo : w ∈ unitCubeOpen8 := by
    intro i _
    have hi := hw i
    have h01 : ¬ (w i = 0 ∨ w i = 1) := fun h => hne ⟨i, h⟩
    rw [not_or] at h01
    exact ⟨lt_of_le_of_ne hi.1 (Ne.symm h01.1), lt_of_le_of_ne hi.2 h01.2⟩
  apply hxi
  rw [mem_interior]
  refine ⟨_, ?_, smallE8_openImage_isOpen p, ⟨w, hwo, hxw⟩⟩
  rw [smallE8CubeSet8_eq]
  rintro y ⟨w', hw', hy⟩
  exact ⟨w', unitCubeOpen8_subset hw', hy⟩

/-- Linear Minkowski bound for the frontier of the complement of finitely many patches. -/
theorem patchComplement_frontier_minkowski8 {K : ℕ} (P : Fin K → SmallE8CubePatch8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      sphereArea8 {x : Sphere8 | ∃ y ∈ frontier (⋃ i, smallE8CubeSet8 (P i))ᶜ, dist x y ≤ ρ} ≤
        ENNReal.ofReal (C*ρ) := by
  classical
  have hL : ∀ i, ∃ L : ℝ≥0, LipschitzOnWith L (smallE8CubeMap8 (P i)) (UnitCube 8) :=
    fun i => smallE8CubeMap8_lipschitz (P i)
  choose L hL using hL
  have hM : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      sphereArea8 {x : Sphere8 | ∃ w ∈ unitCubeBdry8,
        dist (x:Ambient9) (smallE8CubeMap8 (P i) w) ≤ ρ} ≤ ENNReal.ofReal (C*ρ) :=
    fun i => lipschitz_cubeBdry_minkowski8 (hL i)
  choose C hC0 hC using hM
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC0 i), fun ρ hρ => ?_⟩
  have hsub : {x : Sphere8 | ∃ y ∈ frontier (⋃ i, smallE8CubeSet8 (P i))ᶜ, dist x y ≤ ρ} ⊆
      ⋃ i, {x : Sphere8 | ∃ w ∈ unitCubeBdry8,
        dist (x:Ambient9) (smallE8CubeMap8 (P i) w) ≤ ρ} := by
    rintro x ⟨y, hy, hxy⟩
    rw [frontier_compl] at hy
    have hy' : y ∈ ⋃ i ∈ (Finset.univ : Finset (Fin K)), frontier (smallE8CubeSet8 (P i)) := by
      apply frontier_biUnion_closed_subset Finset.univ (fun i => smallE8CubeSet8 (P i))
        (fun i _ => (smallE8CubeSet8_isCompact (P i)).isClosed)
      simpa using hy
    obtain ⟨i, _, hyi⟩ := mem_iUnion₂.mp hy'
    obtain ⟨w, hw, hyw⟩ := smallE8CubeSet8_frontier (P i) hyi
    refine mem_iUnion.mpr ⟨i, w, hw, ?_⟩
    rw [← hyw]
    exact hxy
  calc sphereArea8 {x : Sphere8 | ∃ y ∈ frontier (⋃ i, smallE8CubeSet8 (P i))ᶜ, dist x y ≤ ρ}
      ≤ sphereArea8 (⋃ i, {x : Sphere8 | ∃ w ∈ unitCubeBdry8,
          dist (x:Ambient9) (smallE8CubeMap8 (P i) w) ≤ ρ}) := measure_mono hsub
    _ ≤ ∑ i, sphereArea8 {x : Sphere8 | ∃ w ∈ unitCubeBdry8,
          dist (x:Ambient9) (smallE8CubeMap8 (P i) w) ≤ ρ} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (C i*ρ) := Finset.sum_le_sum fun i _ => hC i ρ hρ
    _ = ENNReal.ofReal ((∑ i, C i)*ρ) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hC0 i) hρ.le)]

#print axioms unitCubeOpen8_isOpen
#print axioms unitCubeOpen8_subset
#print axioms cubeFacePoint8_mem
#print axioms exists_cubeFacePoint8_near
#print axioms lipschitz_cubeBdry_minkowski8
#print axioms smallE8CubeMap8_lipschitz
#print axioms smallE8CubeSet8_eq
#print axioms equalAreaE8Affine8_isOpenMap
#print axioms smallE8_openImage_isOpen
#print axioms smallE8CubeSet8_frontier
#print axioms patchComplement_frontier_minkowski8

end SphericalRiesz
