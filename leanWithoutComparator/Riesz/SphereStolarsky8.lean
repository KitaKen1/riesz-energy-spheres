import Riesz.SphereRieszNegUpper8

/-! Stolarsky's invariance principle on the actual unit S⁸ (stage DISC).

Caps are `C(z,t) = {x : t ≤ ⟪x, z⟫}` with centre `z` distributed by the actual sphere probability
and threshold `t ∈ [-1,1]` by Lebesgue measure. For fixed `z` the `t`-integral of
`1_C(x) 1_C(y)` is `min(⟪x,z⟫, ⟪y,z⟫) + 1`; averaging over `z` (the mean of `⟪v,z⟫` vanishes and
the mean of `|⟪v,z⟫|` is `m ‖v‖` by rotation invariance) gives the cap kernel
`K(x,y) = 1 - (m/2) |x - y|`, `m = ∫ |⟪e, z⟫| dσ(z)`. Expanding the square of the cap discrepancy
function `#(X ∩ C) - N σ(C)` and using that the distance potential is constant gives
`∫∫ (#(X ∩ C) - N σ(C))² = (m/2) (N² ∫∫|x-y| - Σ_{i,j} |x_i - x_j|)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace SphericalRiesz

/-- The real indicator of the closed cap `{x : t ≤ ⟪x, z⟫}`. -/
def capInd8 (z : Sphere8) (t : ℝ) (x : Sphere8) : ℝ :=
  if t ≤ ⟪(x:Ambient9), (z:Ambient9)⟫ then 1 else 0

theorem capInd8_nonneg (z : Sphere8) (t : ℝ) (x : Sphere8) : 0 ≤ capInd8 z t x := by
  unfold capInd8; split_ifs <;> norm_num

theorem capInd8_le_one (z : Sphere8) (t : ℝ) (x : Sphere8) : capInd8 z t x ≤ 1 := by
  unfold capInd8; split_ifs <;> norm_num

theorem capInd8_abs_le_one (z : Sphere8) (t : ℝ) (x : Sphere8) : |capInd8 z t x| ≤ 1 := by
  rw [abs_of_nonneg (capInd8_nonneg z t x)]; exact capInd8_le_one z t x

theorem capInd8_mul_abs_le_one (z : Sphere8) (t : ℝ) (x y : Sphere8) :
    |capInd8 z t x * capInd8 z t y| ≤ 1 := by
  rw [abs_mul]
  calc |capInd8 z t x| * |capInd8 z t y| ≤ 1 * 1 :=
        mul_le_mul (capInd8_abs_le_one z t x) (capInd8_abs_le_one z t y) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem capInd8_measurable :
    Measurable (fun p : (Sphere8 × ℝ) × Sphere8 => capInd8 p.1.1 p.1.2 p.2) := by
  unfold capInd8
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (by fun_prop)
    (Continuous.measurable (by fun_prop))

theorem inner_sphere8_mem_Icc (x z : Sphere8) :
    ⟪(x:Ambient9), (z:Ambient9)⟫ ∈ Icc (-1:ℝ) 1 := by
  have h := abs_real_inner_le_norm (x:Ambient9) (z:Ambient9)
  rw [norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere z, one_mul] at h
  exact abs_le.mp h

theorem capInd8_mul_eq (z x y : Sphere8) (t : ℝ) :
    capInd8 z t x * capInd8 z t y =
      (Iic (min ⟪(x:Ambient9), (z:Ambient9)⟫ ⟪(y:Ambient9), (z:Ambient9)⟫)).indicator 1 t := by
  unfold capInd8
  by_cases h1 : t ≤ ⟪(x:Ambient9), (z:Ambient9)⟫ <;>
    by_cases h2 : t ≤ ⟪(y:Ambient9), (z:Ambient9)⟫ <;>
    simp [h1, h2]

theorem capInd8_mul_integral (z x y : Sphere8) :
    (∫ t in Icc (-1:ℝ) 1, capInd8 z t x * capInd8 z t y) =
      min ⟪(x:Ambient9), (z:Ambient9)⟫ ⟪(y:Ambient9), (z:Ambient9)⟫ + 1 := by
  set m := min ⟪(x:Ambient9), (z:Ambient9)⟫ ⟪(y:Ambient9), (z:Ambient9)⟫ with hm
  have hx := inner_sphere8_mem_Icc x z
  have hy := inner_sphere8_mem_Icc y z
  have hm1 : -1 ≤ m := le_min hx.1 hy.1
  have hm2 : m ≤ 1 := (min_le_left _ _).trans hx.2
  have he : (fun t : ℝ => capInd8 z t x * capInd8 z t y) = (Iic m).indicator 1 := by
    funext t
    rw [capInd8_mul_eq]
  rw [he, integral_indicator_one measurableSet_Iic, Measure.real,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Iic m ∩ Icc (-1:ℝ) 1 = Icc (-1) m := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, h2.trans hm2⟩
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The pole of the actual sphere used to define the absolute first moment. -/
def spherePole8 : Sphere8 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The absolute first moment `m = ∫ |⟪e, z⟫| dσ(z)` of the actual sphere probability. -/
def sphereAbsMoment8 : ℝ :=
  ∫ z, |⟪(spherePole8:Ambient9), (z:Ambient9)⟫| ∂sphereProbability8

theorem sphere8_inner_integrable (v : Ambient9) :
    Integrable (fun z : Sphere8 => ⟪v, (z:Ambient9)⟫) sphereProbability8 := by
  refine (integrable_const ‖v‖).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have h := abs_real_inner_le_norm v (z:Ambient9)
  rwa [norm_eq_of_mem_sphere z, mul_one] at h

theorem sphere8_inner_integral_zero (v : Ambient9) :
    (∫ z, ⟪v, (z:Ambient9)⟫ ∂sphereProbability8) = 0 := by
  have h := sphereProbability8_integral_rotation (LinearIsometryEquiv.neg ℝ)
    (fun z : Sphere8 => ⟪v, (z:Ambient9)⟫)
  have hneg : ∀ z : Sphere8,
      ((sphereRotation8 (LinearIsometryEquiv.neg ℝ) z : Sphere8) : Ambient9) = -(z:Ambient9) :=
    fun z => rfl
  simp only [hneg, inner_neg_right, integral_neg] at h
  linarith

theorem sphere8_abs_inner_integral (v : Ambient9) :
    (∫ z, |⟪v, (z:Ambient9)⟫| ∂sphereProbability8) = ‖v‖*sphereAbsMoment8 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set u : Ambient9 := ‖v‖⁻¹ • v with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    let us : Sphere8 := ⟨u, by simpa using hu⟩
    obtain ⟨g, hg⟩ := sphereRotation8_transitive spherePole8 us
    have hgu : g (spherePole8:Ambient9) = u := congrArg Subtype.val hg
    have h1 : (∫ z, |⟪u, (z:Ambient9)⟫| ∂sphereProbability8) = sphereAbsMoment8 := by
      rw [← sphereProbability8_integral_rotation g (fun z : Sphere8 => |⟪u, (z:Ambient9)⟫|)]
      unfold sphereAbsMoment8
      congr 1
      funext z
      change |⟪u, g (z:Ambient9)⟫| = |⟪(spherePole8:Ambient9), (z:Ambient9)⟫|
      rw [← hgu, LinearIsometryEquiv.inner_map_map]
    have hv' : v = ‖v‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hpt : ∀ z : Sphere8, |⟪v, (z:Ambient9)⟫| = ‖v‖*|⟪u, (z:Ambient9)⟫| := by
      intro z
      conv_lhs => rw [hv']
      rw [real_inner_smul_left, abs_mul, abs_of_pos hn]
    simp_rw [hpt]
    rw [integral_const_mul, h1]

theorem sphere8_abs_inner_integrable (v : Ambient9) :
    Integrable (fun z : Sphere8 => |⟪v, (z:Ambient9)⟫|) sphereProbability8 :=
  (sphere8_inner_integrable v).abs

/-- The cap kernel averaged over thresholds and centres. -/
theorem capKernel8_iterated (x y : Sphere8) :
    (∫ z, (∫ t in Icc (-1:ℝ) 1, capInd8 z t x * capInd8 z t y) ∂sphereProbability8) =
      1-sphereAbsMoment8/2*dist x y := by
  have hpt : ∀ z : Sphere8, (∫ t in Icc (-1:ℝ) 1, capInd8 z t x * capInd8 z t y) =
      ⟪(x:Ambient9)+(y:Ambient9), (z:Ambient9)⟫/2-
        |⟪(x:Ambient9)-(y:Ambient9), (z:Ambient9)⟫|/2+1 := by
    intro z
    rw [capInd8_mul_integral, inner_add_left, inner_sub_left]
    rcases le_total ⟪(x:Ambient9), (z:Ambient9)⟫ ⟪(y:Ambient9), (z:Ambient9)⟫ with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  simp_rw [hpt]
  have i1 : Integrable (fun z : Sphere8 => ⟪(x:Ambient9)+(y:Ambient9), (z:Ambient9)⟫/2)
      sphereProbability8 := (sphere8_inner_integrable ((x:Ambient9)+(y:Ambient9))).div_const 2
  have i2 : Integrable (fun z : Sphere8 => |⟪(x:Ambient9)-(y:Ambient9), (z:Ambient9)⟫|/2)
      sphereProbability8 := (sphere8_abs_inner_integrable ((x:Ambient9)-(y:Ambient9))).div_const 2
  have i12 : Integrable (fun z : Sphere8 => ⟪(x:Ambient9)+(y:Ambient9), (z:Ambient9)⟫/2-
      |⟪(x:Ambient9)-(y:Ambient9), (z:Ambient9)⟫|/2) sphereProbability8 := i1.sub i2
  rw [integral_add i12 (integrable_const 1), integral_sub i1 i2, integral_div,
    integral_div, sphere8_inner_integral_zero, sphere8_abs_inner_integral]
  simp only [integral_const, smul_eq_mul]
  have h1 : sphereProbability8.real univ = 1 := by simp [Measure.real]
  rw [h1, Subtype.dist_eq, dist_eq_norm]
  ring

/-- The cap parameter measure: centre by the actual sphere probability, threshold by
Lebesgue measure on `[-1,1]`. -/
abbrev capMeasure8 : Measure (Sphere8 × ℝ) :=
  sphereProbability8.prod (volume.restrict (Icc (-1:ℝ) 1))

theorem capInd8_pair_measurable (x y : Sphere8) :
    Measurable (fun q : Sphere8 × ℝ => capInd8 q.1 q.2 x * capInd8 q.1 q.2 y) := by
  have h := capInd8_measurable
  exact (h.comp (measurable_id.prodMk measurable_const)).mul
    (h.comp (measurable_id.prodMk measurable_const))

theorem integrable_capMeasure8_of_bound {f : Sphere8 × ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ q, |f q| ≤ C) : Integrable f capMeasure8 :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun q => by rw [Real.norm_eq_abs]; exact hC q))

/-- The cap kernel `K(x,y) = ∫ 1_C(x) 1_C(y)` over the cap parameter measure. -/
def capKernel8 (x y : Sphere8) : ℝ :=
  ∫ q, capInd8 q.1 q.2 x * capInd8 q.1 q.2 y ∂capMeasure8

theorem capKernel8_eq (x y : Sphere8) : capKernel8 x y = 1-sphereAbsMoment8/2*dist x y := by
  unfold capKernel8
  rw [integral_prod _ (integrable_capMeasure8_of_bound (capInd8_pair_measurable x y) 1
    (fun q => capInd8_mul_abs_le_one _ _ _ _))]
  exact capKernel8_iterated x y

theorem capMass8_measurable :
    Measurable (fun q : Sphere8 × ℝ => ∫ y, capInd8 q.1 q.2 y ∂sphereProbability8) := by
  have h : StronglyMeasurable (fun p : (Sphere8 × ℝ) × Sphere8 => capInd8 p.1.1 p.1.2 p.2) :=
    capInd8_measurable.stronglyMeasurable
  exact (h.integral_prod_right' (ν := sphereProbability8)).measurable

theorem capMass8_abs_le_one (q : Sphere8 × ℝ) :
    |∫ y, capInd8 q.1 q.2 y ∂sphereProbability8| ≤ 1 := by
  have h0 : 0 ≤ ∫ y, capInd8 q.1 q.2 y ∂sphereProbability8 :=
    integral_nonneg (fun y => capInd8_nonneg _ _ _)
  rw [abs_of_nonneg h0]
  have h := integral_mono_of_nonneg (Eventually.of_forall (fun y => capInd8_nonneg q.1 q.2 y))
    (integrable_const (1:ℝ) (μ := sphereProbability8))
    (Eventually.of_forall (fun y => capInd8_le_one q.1 q.2 y))
  simpa using h

/-- Fubini for a bounded weight times the cap mass. -/
theorem capMeasure8_integral_mul_mass {F : Sphere8 × ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ q, |F q| ≤ C) :
    (∫ q, F q * (∫ y, capInd8 q.1 q.2 y ∂sphereProbability8) ∂capMeasure8) =
      ∫ y, (∫ q, F q * capInd8 q.1 q.2 y ∂capMeasure8) ∂sphereProbability8 := by
  have h1 : ∀ q : Sphere8 × ℝ, F q * (∫ y, capInd8 q.1 q.2 y ∂sphereProbability8) =
      ∫ y, F q * capInd8 q.1 q.2 y ∂sphereProbability8 :=
    fun q => (integral_const_mul _ _).symm
  simp_rw [h1]
  apply integral_integral_swap
  have hm : Measurable (Function.uncurry fun (q : Sphere8 × ℝ) (y : Sphere8) =>
      F q * capInd8 q.1 q.2 y) :=
    (hF.comp measurable_fst).mul capInd8_measurable
  refine (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  change ‖F p.1 * capInd8 p.1.1 p.1.2 p.2‖ ≤ C
  rw [Real.norm_eq_abs, abs_mul]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p.1)
  calc |F p.1| * |capInd8 p.1.1 p.1.2 p.2| ≤ C * 1 :=
        mul_le_mul (hC p.1) (capInd8_abs_le_one _ _ _) (abs_nonneg _) hC0
    _ = C := mul_one C

/-- The distance potential of the actual sphere probability. -/
def sphereDistPotential8 (x : Sphere8) : ℝ := ∫ y, dist x y ∂sphereProbability8

theorem sphere8_dist_integrable (x : Sphere8) :
    Integrable (fun y : Sphere8 => dist x y) sphereProbability8 :=
  (integrable_const (2:ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
      exact sphere8_dist_le_two x y)

theorem sphereDistPotential8_rotation (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (x : Sphere8) :
    sphereDistPotential8 (sphereRotation8 g x) = sphereDistPotential8 x := by
  unfold sphereDistPotential8
  rw [← sphereProbability8_integral_rotation g (fun y => dist (sphereRotation8 g x) y)]
  simp_rw [sphereRotation8_dist]

theorem sphereDistPotential8_constant (x y : Sphere8) :
    sphereDistPotential8 x = sphereDistPotential8 y := by
  obtain ⟨g, hg⟩ := sphereRotation8_transitive x y
  rw [← hg, sphereDistPotential8_rotation]

theorem sphereDistPotential8_eq_pair (x : Sphere8) :
    sphereDistPotential8 x =
      ∫ p : Sphere8 × Sphere8, dist p.1 p.2 ∂(sphereProbability8.prod sphereProbability8) := by
  have hint : Integrable (fun p : Sphere8 × Sphere8 => dist p.1 p.2)
      (sphereProbability8.prod sphereProbability8) :=
    (integrable_const (2:ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
        exact sphere8_dist_le_two p.1 p.2)
  rw [integral_prod _ hint]
  change sphereDistPotential8 x = ∫ y, sphereDistPotential8 y ∂sphereProbability8
  simp_rw [sphereDistPotential8_constant _ x]
  simp

/-- The cap discrepancy function `#(X ∩ C(z,t)) - N σ(C(z,t))`. -/
def capDiscrepancyFn8 {N : ℕ} (X : Configuration N) (q : Sphere8 × ℝ) : ℝ :=
  (∑ i : Fin N, capInd8 q.1 q.2 (X i)) - (N:ℝ) * ∫ y, capInd8 q.1 q.2 y ∂sphereProbability8

/-- The unnormalized squared spherical cap `L²` discrepancy. -/
def capDiscrepancySq8 {N : ℕ} (X : Configuration N) : ℝ :=
  ∫ q, (capDiscrepancyFn8 X q)^2 ∂capMeasure8

theorem capCount8_measurable {N : ℕ} (X : Configuration N) :
    Measurable (fun q : Sphere8 × ℝ => ∑ i : Fin N, capInd8 q.1 q.2 (X i)) :=
  Finset.measurable_sum _ (fun i _ => capInd8_measurable.comp (measurable_id.prodMk measurable_const))

theorem capCount8_abs_le {N : ℕ} (X : Configuration N) (q : Sphere8 × ℝ) :
    |∑ i : Fin N, capInd8 q.1 q.2 (X i)| ≤ N := by
  have h0 : 0 ≤ ∑ i : Fin N, capInd8 q.1 q.2 (X i) :=
    Finset.sum_nonneg (fun i _ => capInd8_nonneg _ _ _)
  rw [abs_of_nonneg h0]
  calc ∑ i : Fin N, capInd8 q.1 q.2 (X i) ≤ ∑ _i : Fin N, (1:ℝ) :=
        Finset.sum_le_sum (fun _ _ => capInd8_le_one _ _ _)
    _ = N := by simp

/-- Stolarsky's invariance principle on the actual unit S⁸. -/
theorem capDiscrepancySq8_stolarsky {N : ℕ} (X : Configuration N) :
    capDiscrepancySq8 X = sphereAbsMoment8/2*((N:ℝ)^2*
      (∫ p : Sphere8 × Sphere8, dist p.1 p.2 ∂(sphereProbability8.prod sphereProbability8)) -
        ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j)) := by
  set W := ∫ p : Sphere8 × Sphere8, dist p.1 p.2 ∂(sphereProbability8.prod sphereProbability8)
    with hW
  set m := sphereAbsMoment8 with hm
  set a : Sphere8 × ℝ → ℝ := fun q => ∑ i : Fin N, capInd8 q.1 q.2 (X i) with ha
  set b : Sphere8 × ℝ → ℝ := fun q => ∫ y, capInd8 q.1 q.2 y ∂sphereProbability8 with hb
  have ham : Measurable a := capCount8_measurable X
  have hbm : Measurable b := capMass8_measurable
  have hab : ∀ q, |a q| ≤ N := capCount8_abs_le X
  have hbb : ∀ q, |b q| ≤ 1 := capMass8_abs_le_one
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have iaa : Integrable (fun q => a q * a q) capMeasure8 :=
    integrable_capMeasure8_of_bound (ham.mul ham) ((N:ℝ)*N) (fun q => by
      rw [abs_mul]; exact mul_le_mul (hab q) (hab q) (abs_nonneg _) hN0)
  have iab : Integrable (fun q => a q * b q) capMeasure8 :=
    integrable_capMeasure8_of_bound (ham.mul hbm) ((N:ℝ)*1) (fun q => by
      rw [abs_mul]; exact mul_le_mul (hab q) (hbb q) (abs_nonneg _) hN0)
  have ibb : Integrable (fun q => b q * b q) capMeasure8 :=
    integrable_capMeasure8_of_bound (hbm.mul hbm) (1*1) (fun q => by
      rw [abs_mul]; exact mul_le_mul (hbb q) (hbb q) (abs_nonneg _) zero_le_one)
  -- the three terms
  have Taa : (∫ q, a q * a q ∂capMeasure8) =
      ∑ i : Fin N, ∑ j : Fin N, capKernel8 (X i) (X j) := by
    have hpt : ∀ q, a q * a q =
        ∑ i : Fin N, ∑ j : Fin N, capInd8 q.1 q.2 (X i) * capInd8 q.1 q.2 (X j) := by
      intro q
      simp only [ha]
      rw [Finset.sum_mul_sum]
    simp_rw [hpt]
    have hij : ∀ i j : Fin N, Integrable
        (fun q : Sphere8 × ℝ => capInd8 q.1 q.2 (X i) * capInd8 q.1 q.2 (X j)) capMeasure8 :=
      fun i j => integrable_capMeasure8_of_bound (capInd8_pair_measurable (X i) (X j)) 1
        (fun q => capInd8_mul_abs_le_one _ _ _ _)
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hij i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hij i j)]
    rfl
  have Tx : ∀ x : Sphere8, (∫ q, capInd8 q.1 q.2 x * b q ∂capMeasure8) =
      1-m/2*W := by
    intro x
    have h := capMeasure8_integral_mul_mass (F := fun q => capInd8 q.1 q.2 x)
      (capInd8_measurable.comp (measurable_id.prodMk measurable_const)) (C := 1)
      (fun q => capInd8_abs_le_one _ _ _)
    change (∫ q, capInd8 q.1 q.2 x * b q ∂capMeasure8) = _ at h
    rw [h]
    change (∫ y, capKernel8 x y ∂sphereProbability8) = _
    simp_rw [capKernel8_eq]
    rw [integral_sub (integrable_const 1) ((sphere8_dist_integrable x).const_mul (m/2)),
      integral_const_mul]
    change _ - m/2*sphereDistPotential8 x = _
    rw [sphereDistPotential8_eq_pair, ← hW]
    simp
  have Tab : (∫ q, a q * b q ∂capMeasure8) = (N:ℝ)*(1-m/2*W) := by
    have hpt : ∀ q, a q * b q = ∑ i : Fin N, capInd8 q.1 q.2 (X i) * b q := by
      intro q
      simp only [ha]
      rw [Finset.sum_mul]
    simp_rw [hpt]
    have hint : ∀ i : Fin N, Integrable (fun q : Sphere8 × ℝ => capInd8 q.1 q.2 (X i) * b q)
        capMeasure8 := by
      intro i
      have hmi : Measurable (fun q : Sphere8 × ℝ => capInd8 q.1 q.2 (X i)) :=
        capInd8_measurable.comp (measurable_id.prodMk measurable_const)
      refine integrable_capMeasure8_of_bound (hmi.mul hbm) 1 (fun q => ?_)
      rw [abs_mul]
      calc |capInd8 q.1 q.2 (X i)| * |b q| ≤ 1 * 1 :=
            mul_le_mul (capInd8_abs_le_one _ _ _) (hbb q) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [integral_finsetSum _ (fun i _ => hint i)]
    simp_rw [Tx]
    simp
    ring
  have Tbb : (∫ q, b q * b q ∂capMeasure8) = 1-m/2*W := by
    have h := capMeasure8_integral_mul_mass (F := b) hbm (C := 1) hbb
    change (∫ q, b q * b q ∂capMeasure8) = _ at h
    rw [h]
    have hy : ∀ y : Sphere8, (∫ q, b q * capInd8 q.1 q.2 y ∂capMeasure8) = 1-m/2*W := by
      intro y
      rw [← Tx y]
      congr 1
      funext q
      ring
    simp_rw [hy]
    simp
  -- expand the square
  have hsq : ∀ q, (capDiscrepancyFn8 X q)^2 =
      a q * a q - 2*(N:ℝ)*(a q * b q) + (N:ℝ)^2*(b q * b q) := by
    intro q
    unfold capDiscrepancyFn8
    simp only [ha, hb]
    ring
  unfold capDiscrepancySq8
  simp_rw [hsq]
  have i3 : Integrable (fun q => 2*(N:ℝ)*(a q * b q)) capMeasure8 := iab.const_mul _
  have i1 : Integrable (fun q => a q * a q - 2*(N:ℝ)*(a q * b q)) capMeasure8 := iaa.sub i3
  have i2 : Integrable (fun q => (N:ℝ)^2*(b q * b q)) capMeasure8 := ibb.const_mul _
  rw [integral_add i1 i2, integral_sub iaa i3, integral_const_mul, integral_const_mul, Taa, Tab,
    Tbb]
  simp_rw [capKernel8_eq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

#print axioms capInd8_nonneg
#print axioms capInd8_le_one
#print axioms capInd8_abs_le_one
#print axioms capInd8_mul_abs_le_one
#print axioms capInd8_measurable
#print axioms inner_sphere8_mem_Icc
#print axioms capInd8_mul_eq
#print axioms capInd8_mul_integral
#print axioms sphere8_inner_integrable
#print axioms sphere8_inner_integral_zero
#print axioms sphere8_abs_inner_integral
#print axioms sphere8_abs_inner_integrable
#print axioms capKernel8_iterated
#print axioms capInd8_pair_measurable
#print axioms integrable_capMeasure8_of_bound
#print axioms capKernel8_eq
#print axioms capMass8_measurable
#print axioms capMass8_abs_le_one
#print axioms capMeasure8_integral_mul_mass
#print axioms sphere8_dist_integrable
#print axioms sphereDistPotential8_rotation
#print axioms sphereDistPotential8_constant
#print axioms sphereDistPotential8_eq_pair
#print axioms capCount8_measurable
#print axioms capCount8_abs_le
#print axioms capDiscrepancySq8_stolarsky

end SphericalRiesz
