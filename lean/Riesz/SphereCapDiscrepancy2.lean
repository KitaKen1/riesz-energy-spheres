import Riesz.SphereRieszNeg2
import Riesz.HexNegSharp2
import Riesz.SphereAbsMoment8
import Riesz.HexGaussianBridge2

/-! Sharp L2 spherical cap discrepancy on the actual two-dimensional sphere.

Stolarsky invariance with Lebesgue threshold measure on [-1,1], the actual first absolute spherical moment 1/2 and coefficient 1/4, and unconditional sharp lower and attaining upper bounds at every sufficiently large size. The discrepancy normalization is N^(3/4). -/

section

/-! The spherical cap `L²` discrepancy on S² (stage DISC of the S² chain).

The module has five parts, dimension-2 ports of the corresponding S⁸ modules.

* `SphereStolarsky2`: Stolarsky's invariance principle on the actual unit S²,
  `∫∫ (#(X ∩ C) - N σ(C))² = (m/2) (N² ∫∫|x-y| - Σ_{i,j} |x_i - x_j|)`, with caps
  `C(z,t) = {x : t ≤ ⟪x, z⟫}`, centre by the sphere probability, threshold by Lebesgue measure on
  `[-1,1]`, and `m = ∫ |⟪e, z⟫| dσ(z)`.
* `SphereCapDiscrepancy2`: the normalized squared discrepancy and its sharp lower bound
  `N^(1+1/2) D² ≥ (m/2)(-A₂^(1/2) Re ζ_Λ(-1/2)) - η` for every configuration, from the upper
  bound for the sum of distances (`s = -1`).  Here `ζ_Λ` is the continued Epstein zeta function
  of the Hex lattice in the variable `s/2`.
* `SphereAbsMoment2`: `m = 1/2`, by the product and the polar decomposition of a
  Gaussian integral on `ℝ³`.
* `SphereCapDiscrepancySqrt2`: the square-root form `N^(1/2+1/4) D ≥ c₂ - η`.
* `SphereCapDiscrepancyUpper2`: configurations of every large size with
  `N^(1/2+1/4) D ≤ c₂ + η`, and the two-sided statement.

The lower bounds and the two-sided statement assume all-scale Hex contact certificates (stage
G2, not proved in this project).  The upper bounds use no hypothesis. -/

section

/-! Stolarsky's invariance principle on the actual unit S² (stage DISC; dimension-2 port of
`SphereStolarsky8`).

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
def capInd2 (z : SphereD 2) (t : ℝ) (x : SphereD 2) : ℝ :=
  if t ≤ ⟪(x : AmbientD 2), (z : AmbientD 2)⟫ then 1 else 0

theorem capInd2_nonneg (z : SphereD 2) (t : ℝ) (x : SphereD 2) : 0 ≤ capInd2 z t x := by
  unfold capInd2; split_ifs <;> norm_num

theorem capInd2_le_one (z : SphereD 2) (t : ℝ) (x : SphereD 2) : capInd2 z t x ≤ 1 := by
  unfold capInd2; split_ifs <;> norm_num

theorem capInd2_abs_le_one (z : SphereD 2) (t : ℝ) (x : SphereD 2) :
    |capInd2 z t x| ≤ 1 := by
  rw [abs_of_nonneg (capInd2_nonneg z t x)]; exact capInd2_le_one z t x

theorem capInd2_mul_abs_le_one (z : SphereD 2) (t : ℝ) (x y : SphereD 2) :
    |capInd2 z t x * capInd2 z t y| ≤ 1 := by
  rw [abs_mul]
  calc |capInd2 z t x| * |capInd2 z t y| ≤ 1 * 1 :=
        mul_le_mul (capInd2_abs_le_one z t x) (capInd2_abs_le_one z t y) (abs_nonneg _)
          zero_le_one
    _ = 1 := one_mul 1

theorem capInd2_measurable :
    Measurable (fun p : (SphereD 2 × ℝ) × SphereD 2 => capInd2 p.1.1 p.1.2 p.2) := by
  unfold capInd2
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (by fun_prop)
    (Continuous.measurable (by fun_prop))

theorem inner_sphere2_mem_Icc (x z : SphereD 2) :
    ⟪(x : AmbientD 2), (z : AmbientD 2)⟫ ∈ Icc (-1:ℝ) 1 := by
  have h := abs_real_inner_le_norm (x : AmbientD 2) (z : AmbientD 2)
  rw [norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere z, one_mul] at h
  exact abs_le.mp h

theorem capInd2_mul_eq (z x y : SphereD 2) (t : ℝ) :
    capInd2 z t x * capInd2 z t y =
      (Iic (min ⟪(x : AmbientD 2), (z : AmbientD 2)⟫
        ⟪(y : AmbientD 2), (z : AmbientD 2)⟫)).indicator 1 t := by
  unfold capInd2
  by_cases h1 : t ≤ ⟪(x : AmbientD 2), (z : AmbientD 2)⟫ <;>
    by_cases h2 : t ≤ ⟪(y : AmbientD 2), (z : AmbientD 2)⟫ <;>
    simp [h1, h2]

theorem capInd2_mul_integral (z x y : SphereD 2) :
    (∫ t in Icc (-1:ℝ) 1, capInd2 z t x * capInd2 z t y) =
      min ⟪(x : AmbientD 2), (z : AmbientD 2)⟫ ⟪(y : AmbientD 2), (z : AmbientD 2)⟫ + 1 := by
  set m := min ⟪(x : AmbientD 2), (z : AmbientD 2)⟫ ⟪(y : AmbientD 2), (z : AmbientD 2)⟫
    with hm
  have hx := inner_sphere2_mem_Icc x z
  have hy := inner_sphere2_mem_Icc y z
  have hm1 : -1 ≤ m := le_min hx.1 hy.1
  have hm2 : m ≤ 1 := (min_le_left _ _).trans hx.2
  have he : (fun t : ℝ => capInd2 z t x * capInd2 z t y) = (Iic m).indicator 1 := by
    funext t
    rw [capInd2_mul_eq]
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
def spherePole2 : SphereD 2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The absolute first moment `m = ∫ |⟪e, z⟫| dσ(z)` of the actual sphere probability. -/
def sphereAbsMoment2 : ℝ :=
  ∫ z, |⟪(spherePole2 : AmbientD 2), (z : AmbientD 2)⟫| ∂(sphereProbabilityD 2)

theorem sphere2_inner_integrable (v : AmbientD 2) :
    Integrable (fun z : SphereD 2 => ⟪v, (z : AmbientD 2)⟫) (sphereProbabilityD 2) := by
  refine (integrable_const ‖v‖).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have h := abs_real_inner_le_norm v (z : AmbientD 2)
  rwa [norm_eq_of_mem_sphere z, mul_one] at h

theorem sphere2_inner_integral_zero (v : AmbientD 2) :
    (∫ z, ⟪v, (z : AmbientD 2)⟫ ∂(sphereProbabilityD 2)) = 0 := by
  have h := sphereProbability2_integral_rotation (LinearIsometryEquiv.neg ℝ)
    (fun z : SphereD 2 => ⟪v, (z : AmbientD 2)⟫)
  have hneg : ∀ z : SphereD 2,
      ((sphereRotationD (d := 2) (LinearIsometryEquiv.neg ℝ) z : SphereD 2) : AmbientD 2) =
        -(z : AmbientD 2) :=
    fun z => rfl
  simp only [hneg, inner_neg_right, integral_neg] at h
  linarith

theorem sphere2_abs_inner_integral (v : AmbientD 2) :
    (∫ z, |⟪v, (z : AmbientD 2)⟫| ∂(sphereProbabilityD 2)) = ‖v‖*sphereAbsMoment2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set u : AmbientD 2 := ‖v‖⁻¹ • v with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    let us : SphereD 2 := ⟨u, by simpa using hu⟩
    obtain ⟨g, hg⟩ := sphereRotation2_transitive spherePole2 us
    have hgu : g (spherePole2 : AmbientD 2) = u := congrArg Subtype.val hg
    have h1 : (∫ z, |⟪u, (z : AmbientD 2)⟫| ∂(sphereProbabilityD 2)) = sphereAbsMoment2 := by
      rw [← sphereProbability2_integral_rotation g
        (fun z : SphereD 2 => |⟪u, (z : AmbientD 2)⟫|)]
      unfold sphereAbsMoment2
      congr 1
      funext z
      change |⟪u, g (z : AmbientD 2)⟫| =
        |⟪(spherePole2 : AmbientD 2), (z : AmbientD 2)⟫|
      rw [← hgu, LinearIsometryEquiv.inner_map_map]
    have hv' : v = ‖v‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hpt : ∀ z : SphereD 2,
        |⟪v, (z : AmbientD 2)⟫| = ‖v‖*|⟪u, (z : AmbientD 2)⟫| := by
      intro z
      conv_lhs => rw [hv']
      rw [real_inner_smul_left, abs_mul, abs_of_pos hn]
    simp_rw [hpt]
    rw [integral_const_mul, h1]

theorem sphere2_abs_inner_integrable (v : AmbientD 2) :
    Integrable (fun z : SphereD 2 => |⟪v, (z : AmbientD 2)⟫|) (sphereProbabilityD 2) :=
  (sphere2_inner_integrable v).abs

/-- The cap kernel averaged over thresholds and centres. -/
theorem capKernel2_iterated (x y : SphereD 2) :
    (∫ z, (∫ t in Icc (-1:ℝ) 1, capInd2 z t x * capInd2 z t y) ∂(sphereProbabilityD 2)) =
      1-sphereAbsMoment2/2*dist x y := by
  have hpt : ∀ z : SphereD 2, (∫ t in Icc (-1:ℝ) 1, capInd2 z t x * capInd2 z t y) =
      ⟪(x : AmbientD 2)+(y : AmbientD 2), (z : AmbientD 2)⟫/2-
        |⟪(x : AmbientD 2)-(y : AmbientD 2), (z : AmbientD 2)⟫|/2+1 := by
    intro z
    rw [capInd2_mul_integral, inner_add_left, inner_sub_left]
    rcases le_total ⟪(x : AmbientD 2), (z : AmbientD 2)⟫
      ⟪(y : AmbientD 2), (z : AmbientD 2)⟫ with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  simp_rw [hpt]
  have i1 : Integrable
      (fun z : SphereD 2 => ⟪(x : AmbientD 2)+(y : AmbientD 2), (z : AmbientD 2)⟫/2)
      (sphereProbabilityD 2) :=
    (sphere2_inner_integrable ((x : AmbientD 2)+(y : AmbientD 2))).div_const 2
  have i2 : Integrable
      (fun z : SphereD 2 => |⟪(x : AmbientD 2)-(y : AmbientD 2), (z : AmbientD 2)⟫|/2)
      (sphereProbabilityD 2) :=
    (sphere2_abs_inner_integrable ((x : AmbientD 2)-(y : AmbientD 2))).div_const 2
  have i12 : Integrable
      (fun z : SphereD 2 => ⟪(x : AmbientD 2)+(y : AmbientD 2), (z : AmbientD 2)⟫/2-
        |⟪(x : AmbientD 2)-(y : AmbientD 2), (z : AmbientD 2)⟫|/2)
      (sphereProbabilityD 2) := i1.sub i2
  rw [integral_add i12 (integrable_const 1), integral_sub i1 i2, integral_div,
    integral_div, sphere2_inner_integral_zero, sphere2_abs_inner_integral]
  simp only [integral_const, smul_eq_mul]
  have h1 : (sphereProbabilityD 2).real univ = 1 := by simp [Measure.real]
  rw [h1, Subtype.dist_eq, dist_eq_norm]
  ring

/-- The cap parameter measure: centre by the actual sphere probability, threshold by
Lebesgue measure on `[-1,1]`. -/
abbrev capMeasure2 : Measure (SphereD 2 × ℝ) :=
  (sphereProbabilityD 2).prod (volume.restrict (Icc (-1:ℝ) 1))

theorem capInd2_pair_measurable (x y : SphereD 2) :
    Measurable (fun q : SphereD 2 × ℝ => capInd2 q.1 q.2 x * capInd2 q.1 q.2 y) := by
  have h := capInd2_measurable
  exact (h.comp (measurable_id.prodMk measurable_const)).mul
    (h.comp (measurable_id.prodMk measurable_const))

theorem integrable_capMeasure2_of_bound {f : SphereD 2 × ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ q, |f q| ≤ C) : Integrable f capMeasure2 :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun q => by rw [Real.norm_eq_abs]; exact hC q))

/-- The cap kernel `K(x,y) = ∫ 1_C(x) 1_C(y)` over the cap parameter measure. -/
def capKernel2 (x y : SphereD 2) : ℝ :=
  ∫ q, capInd2 q.1 q.2 x * capInd2 q.1 q.2 y ∂capMeasure2

theorem capKernel2_eq (x y : SphereD 2) :
    capKernel2 x y = 1-sphereAbsMoment2/2*dist x y := by
  unfold capKernel2
  rw [integral_prod _ (integrable_capMeasure2_of_bound (capInd2_pair_measurable x y) 1
    (fun q => capInd2_mul_abs_le_one _ _ _ _))]
  exact capKernel2_iterated x y

theorem capMass2_measurable :
    Measurable (fun q : SphereD 2 × ℝ => ∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2)) := by
  have h : StronglyMeasurable
      (fun p : (SphereD 2 × ℝ) × SphereD 2 => capInd2 p.1.1 p.1.2 p.2) :=
    capInd2_measurable.stronglyMeasurable
  exact (h.integral_prod_right' (ν := sphereProbabilityD 2)).measurable

theorem capMass2_abs_le_one (q : SphereD 2 × ℝ) :
    |∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2)| ≤ 1 := by
  have h0 : 0 ≤ ∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2) :=
    integral_nonneg (fun y => capInd2_nonneg _ _ _)
  rw [abs_of_nonneg h0]
  have h := integral_mono_of_nonneg (Eventually.of_forall (fun y => capInd2_nonneg q.1 q.2 y))
    (integrable_const (1:ℝ) (μ := sphereProbabilityD 2))
    (Eventually.of_forall (fun y => capInd2_le_one q.1 q.2 y))
  simpa using h

/-- Fubini for a bounded weight times the cap mass. -/
theorem capMeasure2_integral_mul_mass {F : SphereD 2 × ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ q, |F q| ≤ C) :
    (∫ q, F q * (∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2)) ∂capMeasure2) =
      ∫ y, (∫ q, F q * capInd2 q.1 q.2 y ∂capMeasure2) ∂(sphereProbabilityD 2) := by
  have h1 : ∀ q : SphereD 2 × ℝ, F q * (∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2)) =
      ∫ y, F q * capInd2 q.1 q.2 y ∂(sphereProbabilityD 2) :=
    fun q => (integral_const_mul _ _).symm
  simp_rw [h1]
  apply integral_integral_swap
  have hm : Measurable (Function.uncurry fun (q : SphereD 2 × ℝ) (y : SphereD 2) =>
      F q * capInd2 q.1 q.2 y) :=
    (hF.comp measurable_fst).mul capInd2_measurable
  refine (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  change ‖F p.1 * capInd2 p.1.1 p.1.2 p.2‖ ≤ C
  rw [Real.norm_eq_abs, abs_mul]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p.1)
  calc |F p.1| * |capInd2 p.1.1 p.1.2 p.2| ≤ C * 1 :=
        mul_le_mul (hC p.1) (capInd2_abs_le_one _ _ _) (abs_nonneg _) hC0
    _ = C := mul_one C

/-- The distance potential of the actual sphere probability. -/
def sphereDistPotential2 (x : SphereD 2) : ℝ := ∫ y, dist x y ∂(sphereProbabilityD 2)

theorem sphere2_dist_integrable (x : SphereD 2) :
    Integrable (fun y : SphereD 2 => dist x y) (sphereProbabilityD 2) :=
  (integrable_const (2:ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
      exact sphere2_dist_le_two x y)

theorem sphereDistPotential2_rotation (g : AmbientD 2 ≃ₗᵢ[ℝ] AmbientD 2) (x : SphereD 2) :
    sphereDistPotential2 (sphereRotationD g x) = sphereDistPotential2 x := by
  unfold sphereDistPotential2
  rw [← sphereProbability2_integral_rotation g (fun y => dist (sphereRotationD g x) y)]
  simp_rw [sphereRotationD_dist]

theorem sphereDistPotential2_constant (x y : SphereD 2) :
    sphereDistPotential2 x = sphereDistPotential2 y := by
  obtain ⟨g, hg⟩ := sphereRotation2_transitive x y
  rw [← hg, sphereDistPotential2_rotation]

theorem sphereDistPotential2_eq_pair (x : SphereD 2) :
    sphereDistPotential2 x =
      ∫ p : SphereD 2 × SphereD 2, dist p.1 p.2
        ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  have hint : Integrable (fun p : SphereD 2 × SphereD 2 => dist p.1 p.2)
      ((sphereProbabilityD 2).prod (sphereProbabilityD 2)) :=
    (integrable_const (2:ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
        exact sphere2_dist_le_two p.1 p.2)
  rw [integral_prod _ hint]
  change sphereDistPotential2 x = ∫ y, sphereDistPotential2 y ∂(sphereProbabilityD 2)
  simp_rw [sphereDistPotential2_constant _ x]
  simp

/-- The cap discrepancy function `#(X ∩ C(z,t)) - N σ(C(z,t))`. -/
def capDiscrepancyFn2 {N : ℕ} (X : ConfigurationD 2 N) (q : SphereD 2 × ℝ) : ℝ :=
  (∑ i : Fin N, capInd2 q.1 q.2 (X i)) -
    (N:ℝ) * ∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2)

/-- The unnormalized squared spherical cap `L²` discrepancy. -/
def capDiscrepancySq2 {N : ℕ} (X : ConfigurationD 2 N) : ℝ :=
  ∫ q, (capDiscrepancyFn2 X q)^2 ∂capMeasure2

theorem capCount2_measurable {N : ℕ} (X : ConfigurationD 2 N) :
    Measurable (fun q : SphereD 2 × ℝ => ∑ i : Fin N, capInd2 q.1 q.2 (X i)) :=
  Finset.measurable_sum _
    (fun _ _ => capInd2_measurable.comp (measurable_id.prodMk measurable_const))

theorem capCount2_abs_le {N : ℕ} (X : ConfigurationD 2 N) (q : SphereD 2 × ℝ) :
    |∑ i : Fin N, capInd2 q.1 q.2 (X i)| ≤ N := by
  have h0 : 0 ≤ ∑ i : Fin N, capInd2 q.1 q.2 (X i) :=
    Finset.sum_nonneg (fun i _ => capInd2_nonneg _ _ _)
  rw [abs_of_nonneg h0]
  calc ∑ i : Fin N, capInd2 q.1 q.2 (X i) ≤ ∑ _i : Fin N, (1:ℝ) :=
        Finset.sum_le_sum (fun _ _ => capInd2_le_one _ _ _)
    _ = N := by simp

/-- Stolarsky's invariance principle on the actual unit S². -/
theorem capDiscrepancySq2_stolarsky {N : ℕ} (X : ConfigurationD 2 N) :
    capDiscrepancySq2 X = sphereAbsMoment2/2*((N:ℝ)^2*
      (∫ p : SphereD 2 × SphereD 2, dist p.1 p.2
        ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2))) -
        ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j)) := by
  set W := ∫ p : SphereD 2 × SphereD 2, dist p.1 p.2
    ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) with hW
  set m := sphereAbsMoment2 with hm
  set a : SphereD 2 × ℝ → ℝ := fun q => ∑ i : Fin N, capInd2 q.1 q.2 (X i) with ha
  set b : SphereD 2 × ℝ → ℝ :=
    fun q => ∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2) with hb
  have ham : Measurable a := capCount2_measurable X
  have hbm : Measurable b := capMass2_measurable
  have hab : ∀ q, |a q| ≤ N := capCount2_abs_le X
  have hbb : ∀ q, |b q| ≤ 1 := capMass2_abs_le_one
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have iaa : Integrable (fun q => a q * a q) capMeasure2 :=
    integrable_capMeasure2_of_bound (ham.mul ham) ((N:ℝ)*N) (fun q => by
      rw [abs_mul]; exact mul_le_mul (hab q) (hab q) (abs_nonneg _) hN0)
  have iab : Integrable (fun q => a q * b q) capMeasure2 :=
    integrable_capMeasure2_of_bound (ham.mul hbm) ((N:ℝ)*1) (fun q => by
      rw [abs_mul]; exact mul_le_mul (hab q) (hbb q) (abs_nonneg _) hN0)
  have ibb : Integrable (fun q => b q * b q) capMeasure2 :=
    integrable_capMeasure2_of_bound (hbm.mul hbm) (1*1) (fun q => by
      rw [abs_mul]; exact mul_le_mul (hbb q) (hbb q) (abs_nonneg _) zero_le_one)
  -- the three terms
  have Taa : (∫ q, a q * a q ∂capMeasure2) =
      ∑ i : Fin N, ∑ j : Fin N, capKernel2 (X i) (X j) := by
    have hpt : ∀ q, a q * a q =
        ∑ i : Fin N, ∑ j : Fin N, capInd2 q.1 q.2 (X i) * capInd2 q.1 q.2 (X j) := by
      intro q
      simp only [ha]
      rw [Finset.sum_mul_sum]
    simp_rw [hpt]
    have hij : ∀ i j : Fin N, Integrable
        (fun q : SphereD 2 × ℝ => capInd2 q.1 q.2 (X i) * capInd2 q.1 q.2 (X j))
        capMeasure2 :=
      fun i j => integrable_capMeasure2_of_bound (capInd2_pair_measurable (X i) (X j)) 1
        (fun q => capInd2_mul_abs_le_one _ _ _ _)
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hij i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hij i j)]
    rfl
  have Tx : ∀ x : SphereD 2, (∫ q, capInd2 q.1 q.2 x * b q ∂capMeasure2) =
      1-m/2*W := by
    intro x
    have h := capMeasure2_integral_mul_mass (F := fun q => capInd2 q.1 q.2 x)
      (capInd2_measurable.comp (measurable_id.prodMk measurable_const)) (C := 1)
      (fun q => capInd2_abs_le_one _ _ _)
    change (∫ q, capInd2 q.1 q.2 x * b q ∂capMeasure2) = _ at h
    rw [h]
    change (∫ y, capKernel2 x y ∂(sphereProbabilityD 2)) = _
    simp_rw [capKernel2_eq]
    rw [integral_sub (integrable_const 1) ((sphere2_dist_integrable x).const_mul (m/2)),
      integral_const_mul]
    change _ - m/2*sphereDistPotential2 x = _
    rw [sphereDistPotential2_eq_pair, ← hW]
    simp
  have Tab : (∫ q, a q * b q ∂capMeasure2) = (N:ℝ)*(1-m/2*W) := by
    have hpt : ∀ q, a q * b q = ∑ i : Fin N, capInd2 q.1 q.2 (X i) * b q := by
      intro q
      simp only [ha]
      rw [Finset.sum_mul]
    simp_rw [hpt]
    have hint : ∀ i : Fin N,
        Integrable (fun q : SphereD 2 × ℝ => capInd2 q.1 q.2 (X i) * b q) capMeasure2 := by
      intro i
      have hmi : Measurable (fun q : SphereD 2 × ℝ => capInd2 q.1 q.2 (X i)) :=
        capInd2_measurable.comp (measurable_id.prodMk measurable_const)
      refine integrable_capMeasure2_of_bound (hmi.mul hbm) 1 (fun q => ?_)
      rw [abs_mul]
      calc |capInd2 q.1 q.2 (X i)| * |b q| ≤ 1 * 1 :=
            mul_le_mul (capInd2_abs_le_one _ _ _) (hbb q) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [integral_finsetSum _ (fun i _ => hint i)]
    simp_rw [Tx]
    simp
    ring
  have Tbb : (∫ q, b q * b q ∂capMeasure2) = 1-m/2*W := by
    have h := capMeasure2_integral_mul_mass (F := b) hbm (C := 1) hbb
    change (∫ q, b q * b q ∂capMeasure2) = _ at h
    rw [h]
    have hy : ∀ y : SphereD 2, (∫ q, b q * capInd2 q.1 q.2 y ∂capMeasure2) = 1-m/2*W := by
      intro y
      rw [← Tx y]
      congr 1
      funext q
      ring
    simp_rw [hy]
    simp
  -- expand the square
  have hsq : ∀ q, (capDiscrepancyFn2 X q)^2 =
      a q * a q - 2*(N:ℝ)*(a q * b q) + (N:ℝ)^2*(b q * b q) := by
    intro q
    unfold capDiscrepancyFn2
    simp only [ha, hb]
    ring
  unfold capDiscrepancySq2
  simp_rw [hsq]
  have i3 : Integrable (fun q => 2*(N:ℝ)*(a q * b q)) capMeasure2 := iab.const_mul _
  have i1 : Integrable (fun q => a q * a q - 2*(N:ℝ)*(a q * b q)) capMeasure2 := iaa.sub i3
  have i2 : Integrable (fun q => (N:ℝ)^2*(b q * b q)) capMeasure2 := ibb.const_mul _
  rw [integral_add i1 i2, integral_sub iaa i3, integral_const_mul, integral_const_mul, Taa, Tab,
    Tbb]
  simp_rw [capKernel2_eq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

end SphericalRiesz
end
end

section

/-! The sharp spherical cap `L²` discrepancy lower bound on S² (stage DISC, one-sided;
dimension-2 port of `SphereCapDiscrepancy8`).

`D_{L²}(X)² = ∫∫ (#(X ∩ C(z,t))/N - σ(C(z,t)))² dσ(z) dt` (centre by the actual sphere
probability, threshold `t ∈ [-1,1]` by Lebesgue measure). By Stolarsky's principle
`N² D_{L²}(X)² = (m/2) (N² ∫∫|x-y| - Σ_{i,j} |x_i-x_j|)`, and the universal sharp bound for the
sum of distances (`s = -1`) gives, under all-scale Hex contact certificates (stage G2, not
proved in this project), for every `η > 0` and all large `N`,
`N^(1+1/2) D_{L²}(X)² ≥ (m/2) (-A₂^(1/2) Re ζ_Λ(-1)) - η` for every configuration, with
`ζ_Λ` the continued Epstein zeta function of the Hex lattice. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace SphericalRiesz

/-- The normalized squared spherical cap `L²` discrepancy. -/
def capDiscrepancyL2Sq2 {N : ℕ} (X : ConfigurationD 2 N) : ℝ :=
  ∫ q, ((∑ i : Fin N, capInd2 q.1 q.2 (X i))/(N:ℝ) -
    ∫ y, capInd2 q.1 q.2 y ∂(sphereProbabilityD 2))^2 ∂capMeasure2

theorem capDiscrepancyL2Sq2_eq {N : ℕ} (hN : 0 < N) (X : ConfigurationD 2 N) :
    capDiscrepancyL2Sq2 X = capDiscrepancySq2 X/(N:ℝ)^2 := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold capDiscrepancyL2Sq2 capDiscrepancySq2
  rw [← integral_div]
  congr 1
  funext q
  unfold capDiscrepancyFn2
  field_simp

theorem sphereAbsMoment2_nonneg : 0 ≤ sphereAbsMoment2 :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem energyRpowD_neg_one_eqS2 {d N : ℕ} (X : ConfigurationD d N) :
    energyRpowD (-1) X = ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j) := by
  rw [energyRpowD_eq_full_neg2 (by norm_num) X]
  simp only [neg_neg, Real.rpow_one]

theorem pair_integral_rpow_neg_one2 :
    (∫ p : SphereD 2 × SphereD 2, (dist p.1 p.2)^(-(-1:ℝ))
        ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2))) =
      ∫ p : SphereD 2 × SphereD 2, dist p.1 p.2
        ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  simp only [neg_neg, Real.rpow_one]

/-- Sharp one-sided cap discrepancy bound in conjecture form, under all-scale Hex contact
certificates (stage G2). -/
theorem sphere2_cap_discrepancy_lower_conjecture_form
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      sphereAbsMoment2/2*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
          (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re))-η ≤
        (N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X := by
  intro η hη
  set m := sphereAbsMoment2 with hm
  have hm0 : 0 ≤ m := sphereAbsMoment2_nonneg
  have hη' : 0 < η/(m/2+1) := div_pos hη (by linarith)
  obtain ⟨N₀, h⟩ := sphere2_riesz_neg_upper_conjecture_form hG2 (s := -1) (by norm_num)
    (by norm_num) (η/(m/2+1)) hη'
  refine ⟨max N₀ 1, fun N hN X => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hNpos : 0 < N := hN1
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hX := h N hN0 X
  rw [energyRpowD_neg_one_eqS2, pair_integral_rpow_neg_one2] at hX
  set W := ∫ p : SphereD 2 × SphereD 2, dist p.1 p.2
    ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) with hW
  set S := ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j) with hS
  set c := ((sphereAreaD 2).real univ)^(-((-1:ℝ)/2))*
    (hexEpsteinZeta (((-1:ℝ)/2:ℝ):ℂ)).re with hc
  have hc' : ((sphereAreaD 2).real univ)^((1:ℝ)/2)*(hexEpsteinZeta ((-1/2:ℝ):ℂ)).re =
      c := by
    rw [hc]
    norm_num
  rw [hc']
  have hp : (N:ℝ)^(1+(-1:ℝ)/2) = (N:ℝ)^((1:ℝ)/2) := by norm_num
  rw [hp] at hX
  have hP : 0 < (N:ℝ)^((1:ℝ)/2) := Real.rpow_pos_of_pos hNR _
  -- Stolarsky
  rw [capDiscrepancyL2Sq2_eq hNpos, capDiscrepancySq2_stolarsky X, ← hW, ← hm, ← hS]
  have hpow : (N:ℝ)^(1+(1:ℝ)/2)*((N:ℝ)^((1:ℝ)/2)) = (N:ℝ)^2 := by
    rw [← Real.rpow_add hNR]
    norm_num
  have hkey : (N:ℝ)^(1+(1:ℝ)/2)*(m/2*((N:ℝ)^2*W-S)/(N:ℝ)^2) =
      m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) := by
    rw [← hpow]
    field_simp
  rw [hkey]
  have hb : (S-W*(N:ℝ)^2)/(N:ℝ)^((1:ℝ)/2) ≤ c+η/(m/2+1) := hX
  have hb2 : -(c+η/(m/2+1)) ≤ ((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) := by
    have : ((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) = -((S-W*(N:ℝ)^2)/(N:ℝ)^((1:ℝ)/2)) := by
      rw [← neg_div]; congr 1; ring
    rw [this]; linarith
  have hb3 := mul_le_mul_of_nonneg_left hb2 (by linarith : 0 ≤ m/2)
  have hfrac : m/2*(η/(m/2+1)) ≤ η := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have he : m/2*(((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2)) =
      m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) := by
    ring
  rw [← he]
  nlinarith

end SphericalRiesz
end
end

section

/-! The absolute first moment of the actual S² probability and the Stolarsky constant (stage
DISC; dimension-2 port of `SphereAbsMoment8`).

By the product structure of Lebesgue measure,
`∫_{ℝ³} |x₀| e^(-|x|²) dx = π`. The polar decomposition identifies this with
`(∫_{S²} |u₀| dA(u)) ∫₀^∞ r³ e^(-r²) dr = (1/2) ∫_{S²} |u₀| dA(u)`.
The area `A₂ = 4π` therefore gives `m = (4π)⁻¹ (2π) = 1/2` and
Stolarsky's constant `m/2 = 1/4`. The two one-dimensional Gaussian integrals are those of
`SphereAbsMoment8`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace SphericalRiesz

theorem ambient3_abs_coord_gaussian_integral :
    (∫ x : AmbientD 2, |x 0| * Real.exp (-‖x‖^2)) = Real.pi^1 := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (2+1))
  set f : Fin (2+1) → ℝ → ℝ := fun i t => (if i = 0 then |t| else 1) * Real.exp (-t^2) with hf
  have hg : ∀ x : AmbientD 2, |x 0| * Real.exp (-‖x‖^2) =
      ∏ i, f i ((MeasurableEquiv.toLp 2 (Fin (2+1) → ℝ)).symm x i) := by
    intro x
    have hn : ‖x‖^2 = ∑ i : Fin (2+1), (x i)^2 := EuclideanSpace.real_norm_sq_eq x
    rw [MeasurableEquiv.coe_toLp_symm, hn, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [hf, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  simp_rw [hg]
  rw [hmp.integral_comp' (fun y : Fin (2+1) → ℝ => ∏ i, f i (y i)),
    integral_fintype_prod_volume_eq_prod, Fin.prod_univ_succ]
  have h0 : (∫ t : ℝ, f 0 t) = 1 := by
    simp only [hf, ite_true]
    exact real_abs_mul_gaussian_integral
  have hs : ∀ i : Fin 2, (∫ t : ℝ, f i.succ t) = Real.sqrt Real.pi := by
    intro i
    simp only [hf, Fin.succ_ne_zero, ite_false, one_mul]
    exact real_gaussian_integral_one
  rw [h0, Finset.prod_congr rfl (fun i _ => hs i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, one_mul]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  calc Real.sqrt Real.pi ^ 2 = (Real.sqrt Real.pi ^ 2)^1 := by ring
    _ = Real.pi^1 := by rw [hsq]

theorem volumeIoiPow2_integral (g : ℝ → ℝ) :
    (∫ r : Ioi (0:ℝ), g r ∂(Measure.volumeIoiPow 2)) = ∫ r in Ioi (0:ℝ), r^2 * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi (fun a => Real.toNNReal (a^2) • g a)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) _), smul_eq_mul]

theorem ambient3_abs_coord_gaussian_polar :
    (∫ x : AmbientD 2, |x 0| * Real.exp (-‖x‖^2)) =
      (∫ u : SphereD 2, |(u : AmbientD 2) 0| ∂(sphereAreaD 2)) * (1/2) := by
  set F : AmbientD 2 → ℝ := fun x => |x 0| * Real.exp (-‖x‖^2) with hF
  set G : SphereD 2 × Ioi (0:ℝ) → ℝ :=
    fun p => |(p.1 : AmbientD 2) 0| * ((p.2:ℝ) * Real.exp (-(p.2:ℝ)^2)) with hG
  have h1 : (∫ x : AmbientD 2, F x) =
      ∫ x : ({0}ᶜ : Set (AmbientD 2)), F x
        ∂((volume : Measure (AmbientD 2)).comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl F,
      restrict_compl_singleton]
  have hdim : Module.finrank ℝ (AmbientD 2) - 1 = 2 := by simp [AmbientD]
  have hmp := (volume : Measure (AmbientD 2)).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at hmp
  have h2 := hmp.integral_comp (Homeomorph.measurableEmbedding _) G
  have hpt : ∀ x : ({0}ᶜ : Set (AmbientD 2)),
      G (homeomorphUnitSphereProd (AmbientD 2) x) = F x := by
    intro x
    have hx : (x : AmbientD 2) ≠ 0 := x.2
    have hn : 0 < ‖(x : AmbientD 2)‖ := norm_pos_iff.mpr hx
    have hfst : (((homeomorphUnitSphereProd (AmbientD 2) x).1 : SphereD 2) : AmbientD 2) =
        ‖(x : AmbientD 2)‖⁻¹ • (x : AmbientD 2) := sphereDirectionD_coe 2 x
    simp only [hG, hF, hfst, homeomorphUnitSphereProd_apply_snd_coe]
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_norm]
    field_simp
  simp_rw [hpt] at h2
  rw [h1, h2]
  change (∫ p, |(p.1 : AmbientD 2) 0| * ((p.2:ℝ) * Real.exp (-(p.2:ℝ)^2))
    ∂((sphereAreaD 2).prod (Measure.volumeIoiPow 2))) = _
  rw [integral_prod_mul (fun u : SphereD 2 => |(u : AmbientD 2) 0|)
    (fun r : Ioi (0:ℝ) => (r:ℝ) * Real.exp (-(r:ℝ)^2)),
    volumeIoiPow2_integral (fun r => r * Real.exp (-r^2))]
  congr 1
  have h5 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1) (by norm_num)
    (by norm_num) (by norm_num)
  have he : (∫ r in Ioi (0:ℝ), r^2 * (r * Real.exp (-r^2))) =
      ∫ x in Ioi (0:ℝ), x^(3:ℝ) * Real.exp (-1 * x^(2:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [show (x:ℝ)^(2:ℝ) = x^2 by norm_cast, show (x:ℝ)^(3:ℝ) = x^3 by norm_cast, neg_mul,
      one_mul]
    ring
  rw [he, h5, Real.one_rpow, show ((3:ℝ)+1)/2 = 2 by norm_num]
  have hΓ : Real.Gamma 2 = 1 := by
    rw [show (2:ℝ) = (1:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hΓ]
  norm_num

/-- The absolute first moment of the actual sphere probability is
`m = 1/2`. -/
theorem sphereAbsMoment2_eq : sphereAbsMoment2 = 1/2 := by
  have hA : (sphereAreaD 2).real univ = 2^2*Real.pi^1/1 := by
    norm_num only [pow_one,div_one] at *
    exact sphereArea2_univ_real
  have hpole : ∀ z : SphereD 2,
      |⟪(spherePole2 : AmbientD 2), (z : AmbientD 2)⟫| = |(z : AmbientD 2) 0| := by
    intro z
    simp [spherePole2, EuclideanSpace.inner_single_left]
  have harea : (∫ u : SphereD 2, |(u : AmbientD 2) 0| ∂(sphereAreaD 2)) =
      Real.pi^1/(1/2) := by
    have h := ambient3_abs_coord_gaussian_polar
    rw [ambient3_abs_coord_gaussian_integral] at h
    exact eq_div_of_mul_eq (by norm_num) h.symm
  have hP : Real.pi^1 ≠ 0 := pow_ne_zero 1 Real.pi_ne_zero
  unfold sphereAbsMoment2
  simp_rw [hpole]
  rw [sphereProbabilityD, integral_smul_measure, harea, ENNReal.toReal_inv]
  change ((sphereAreaD 2).real univ)⁻¹ • (Real.pi^1/(1/2)) = _
  rw [hA, smul_eq_mul]
  calc (2^2*Real.pi^1/1)⁻¹*(Real.pi^1/(1/2))
      = 1/2*((Real.pi^1)⁻¹*Real.pi^1) := by ring
    _ = 1/2 := by rw [inv_mul_cancel₀ hP, mul_one]

/-- Stolarsky's constant for S²: `m/2 = 1/4`. -/
theorem sphereStolarskyConst2_eq : sphereAbsMoment2/2 = 1/4 := by
  rw [sphereAbsMoment2_eq]
  norm_num

/-- The sharp one-sided cap discrepancy bound with the explicit Stolarsky constant
`1/4`. -/
theorem sphere2_cap_discrepancy_lower_explicit
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (1/4:ℝ)*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
          (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re))-η ≤
        (N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X := by
  rw [← sphereStolarskyConst2_eq]
  exact sphere2_cap_discrepancy_lower_conjecture_form hG2

end SphericalRiesz
end
end

section

/-! The cap discrepancy bound on S² in the Bilyk–Brauchart form (stage DISC; dimension-2 port
of `SphereCapDiscrepancySqrt8`).

`D_{L²}(X) ≥ (c₂ - η) N^(-1/2-1/4)` for all large `N` and every configuration, with
`c₂ = √((1/4)(-A₂^(1/2) Re ζ_Λ(-1)))`, under all-scale Hex contact certificates
(stage G2, proved by the triangular Gaussian bridge). Square root of the explicit squared bound. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The sharp cap discrepancy constant
`c₂ = √((1/4)(-A₂^(1/2) Re ζ_Λ(-1)))`. -/
def sphereCapDiscrepancyConst2 : ℝ :=
  Real.sqrt ((1/4:ℝ)*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
    (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re)))

theorem capDiscrepancyL2Sq2_nonneg {N : ℕ} (X : ConfigurationD 2 N) :
    0 ≤ capDiscrepancyL2Sq2 X :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- `N^(1/2+1/4) D_{L²}(X) ≥ c₂ - η` for all large `N` and every configuration. -/
theorem sphere2_cap_discrepancy_sqrt_lower
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      sphereCapDiscrepancyConst2-η ≤
        (N:ℝ)^((1:ℝ)/2+1/4)*Real.sqrt (capDiscrepancyL2Sq2 X) := by
  intro η hη
  set K := (1/4:ℝ)*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
    (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re)) with hK
  obtain ⟨N₀, h⟩ := sphere2_cap_discrepancy_lower_explicit hG2 (η^2) (by positivity)
  refine ⟨N₀, fun N hN X => ?_⟩
  have hX := h N hN X
  rw [← hK] at hX
  have hD0 := capDiscrepancyL2Sq2_nonneg X
  have hNR : (0:ℝ) ≤ N := Nat.cast_nonneg N
  set P := (N:ℝ)^((1:ℝ)/2+1/4) with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNR _
  have hPsq : P^2 = (N:ℝ)^(1+(1:ℝ)/2) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hNR]
    norm_num
  have hrhs : P*Real.sqrt (capDiscrepancyL2Sq2 X) =
      Real.sqrt ((N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X) := by
    rw [← hPsq, Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP0]
  rw [hrhs]
  unfold sphereCapDiscrepancyConst2
  rw [← hK]
  by_cases hsmall : Real.sqrt K ≤ η
  · have := Real.sqrt_nonneg ((N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X)
    linarith
  · replace hsmall : η < Real.sqrt K := lt_of_not_ge hsmall
    have hK0 : 0 ≤ K := by
      by_contra hneg
      have hneg' : K < 0 := lt_of_not_ge hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg'.le] at hsmall
      linarith
    have hη2 : η^2 ≤ K := by
      have h1 : η^2 ≤ (Real.sqrt K)^2 := pow_le_pow_left₀ hη.le hsmall.le 2
      rwa [Real.sq_sqrt hK0] at h1
    have hmono : Real.sqrt (K-η^2) ≤
        Real.sqrt ((N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X) :=
      Real.sqrt_le_sqrt hX
    have hsplit : Real.sqrt K ≤ Real.sqrt (K-η^2)+η := by
      rw [Real.sqrt_le_left]
      · have h1 : 0 ≤ Real.sqrt (K-η^2) := Real.sqrt_nonneg _
        have h2 := Real.sq_sqrt (by linarith : 0 ≤ K-η^2)
        nlinarith
      · positivity
    linarith

end SphericalRiesz
end
end

section

/-! The sharp spherical cap `L²` discrepancy on S², two-sided (stage DISC; dimension-2 port of
`SphereCapDiscrepancyUpper8`).

By Stolarsky's invariance principle on `S²`,
`N^(1+1/2) D_{L²}(X)² = (1/4)(N² W - Σ|x_i-x_j|)/N^(1/2)` with `W = ∫∫|x-y|`, so
the sharp lower bound for the `s = -1` energy along every large `N` (some configuration,
`sphere2_riesz_neg_lower_conjecture_form`, which needs no hypothesis) gives configurations with
`N^(1+1/2) D_{L²}² ≤ (1/4)(-A₂^(1/2) Re ζ_Λ(-1)) + η`, the matching upper bound of
the one-sided bound already proved. Hence the optimal cap discrepancy satisfies
`N^(1/2+1/4) D_{L²} → c₂`; the upper half is unconditional, the lower half and the two-sided
statement are under all-scale Hex contact certificates (stage G2, not proved in this
project). -/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
namespace SphericalRiesz
open Boundary

/-- Configurations with sharp cap discrepancy for every large `N`.  No hypothesis is used. -/
theorem sphere2_cap_discrepancy_upper_conjecture_form :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ConfigurationD 2 N,
      (N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X ≤
        sphereAbsMoment2/2*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
          (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re))+η := by
  intro η hη
  set m := sphereAbsMoment2 with hm
  have hm0 : 0 ≤ m := sphereAbsMoment2_nonneg
  have hη' : 0 < η/(m/2+1) := div_pos hη (by linarith)
  obtain ⟨N₀, h⟩ := sphere2_riesz_neg_lower_conjecture_form (s := -1)
    (by norm_num) (by norm_num) (η/(m/2+1)) hη'
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hNpos : 0 < N := hN1
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨X, hX⟩ := h N hN0
  refine ⟨X, ?_⟩
  rw [energyRpowD_neg_one_eqS2, pair_integral_rpow_neg_one2] at hX
  set W := ∫ p : SphereD 2 × SphereD 2, dist p.1 p.2
    ∂((sphereProbabilityD 2).prod (sphereProbabilityD 2)) with hW
  set S := ∑ i : Fin N, ∑ j : Fin N, dist (X i) (X j) with hS
  set c := ((sphereAreaD 2).real univ)^(-((-1:ℝ)/2))*
    (hexEpsteinZeta (((-1:ℝ)/2:ℝ):ℂ)).re with hc
  have hc' : ((sphereAreaD 2).real univ)^((1:ℝ)/2)*(hexEpsteinZeta ((-1/2:ℝ):ℂ)).re =
      c := by
    rw [hc]
    norm_num
  rw [hc']
  have hp : (N:ℝ)^(1+(-1:ℝ)/2) = (N:ℝ)^((1:ℝ)/2) := by norm_num
  rw [hp] at hX
  have hP : 0 < (N:ℝ)^((1:ℝ)/2) := Real.rpow_pos_of_pos hNR _
  rw [capDiscrepancyL2Sq2_eq hNpos, capDiscrepancySq2_stolarsky X, ← hW, ← hm, ← hS]
  have hpow : (N:ℝ)^(1+(1:ℝ)/2)*((N:ℝ)^((1:ℝ)/2)) = (N:ℝ)^2 := by
    rw [← Real.rpow_add hNR]
    norm_num
  have hkey : (N:ℝ)^(1+(1:ℝ)/2)*(m/2*((N:ℝ)^2*W-S)/(N:ℝ)^2) =
      m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) := by
    rw [← hpow]
    field_simp
  rw [hkey]
  have hb : c-η/(m/2+1) ≤ (S-W*(N:ℝ)^2)/(N:ℝ)^((1:ℝ)/2) := hX
  have hb2 : ((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) ≤ -c+η/(m/2+1) := by
    have : ((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) = -((S-W*(N:ℝ)^2)/(N:ℝ)^((1:ℝ)/2)) := by
      rw [← neg_div]; congr 1; ring
    rw [this]; linarith
  have hb3 := mul_le_mul_of_nonneg_left hb2 (by linarith : 0 ≤ m/2)
  have hfrac : m/2*(η/(m/2+1)) ≤ η := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have he : m/2*(((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2)) =
      m/2*((N:ℝ)^2*W-S)/(N:ℝ)^((1:ℝ)/2) := by
    ring
  rw [← he]
  nlinarith

/-- `N^(1/2+1/4) D_{L²}(X) ≤ c₂ + η` for some configuration, for every large `N`.  No
hypothesis is used. -/
theorem sphere2_cap_discrepancy_sqrt_upper :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ConfigurationD 2 N,
      (N:ℝ)^((1:ℝ)/2+1/4)*Real.sqrt (capDiscrepancyL2Sq2 X) ≤
        sphereCapDiscrepancyConst2+η := by
  intro η hη
  set K := (1/4:ℝ)*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
    (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re)) with hK
  obtain ⟨N₀, h⟩ := sphere2_cap_discrepancy_upper_conjecture_form (η^2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨X, hX⟩ := h N hN
  rw [sphereStolarskyConst2_eq, ← hK] at hX
  refine ⟨X, ?_⟩
  have hD0 := capDiscrepancyL2Sq2_nonneg X
  have hNR : (0:ℝ) ≤ N := Nat.cast_nonneg N
  set P := (N:ℝ)^((1:ℝ)/2+1/4) with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hNR _
  have hPsq : P^2 = (N:ℝ)^(1+(1:ℝ)/2) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hNR]
    norm_num
  have hrhs : P*Real.sqrt (capDiscrepancyL2Sq2 X) =
      Real.sqrt ((N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X) := by
    rw [← hPsq, Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP0]
  rw [hrhs]
  unfold sphereCapDiscrepancyConst2
  rw [← hK]
  have hmono : Real.sqrt ((N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X) ≤ Real.sqrt (K+η^2) :=
    Real.sqrt_le_sqrt hX
  have hsplit : Real.sqrt (K+η^2) ≤ Real.sqrt K+η := by
    rw [Real.sqrt_le_left]
    · rcases le_or_gt 0 K with hK0 | hK0
      · have h2 := Real.sq_sqrt hK0
        have h1 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
        nlinarith
      · rw [Real.sqrt_eq_zero_of_nonpos hK0.le]
        nlinarith
    · positivity
  linarith

/-- The optimal spherical cap `L²` discrepancy on `S²` is asymptotic to `c₂ N^(-1/2-1/4)`
(two-sided), under all-scale Hex contact certificates (stage G2) as the only hypothesis. -/
theorem sphere2_cap_discrepancy_sharp
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ X : ConfigurationD 2 N, sphereCapDiscrepancyConst2-η ≤
        (N:ℝ)^((1:ℝ)/2+1/4)*Real.sqrt (capDiscrepancyL2Sq2 X)) ∧
      ∃ X : ConfigurationD 2 N,
        (N:ℝ)^((1:ℝ)/2+1/4)*Real.sqrt (capDiscrepancyL2Sq2 X) ≤
          sphereCapDiscrepancyConst2+η := by
  intro η hη
  obtain ⟨N₁, h1⟩ := sphere2_cap_discrepancy_sqrt_lower hG2 η hη
  obtain ⟨N₂, h2⟩ := sphere2_cap_discrepancy_sqrt_upper η hη
  exact ⟨max N₁ N₂, fun N hN => ⟨h1 N (le_of_max_le_left hN), h2 N (le_of_max_le_right hN)⟩⟩

theorem sphere2_cap_discrepancy_lower_explicit_unconditional :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 2 N,
      (1/4:ℝ)*(-(((sphereAreaD 2).real univ)^((1:ℝ)/2)*
          (hexEpsteinZeta ((-1/2:ℝ):ℂ)).re))-η ≤
        (N:ℝ)^(1+(1:ℝ)/2)*capDiscrepancyL2Sq2 X :=
  sphere2_cap_discrepancy_lower_explicit hexGaussianContact_all

theorem sphere2_cap_discrepancy_sharp_unconditional :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ X : ConfigurationD 2 N, sphereCapDiscrepancyConst2-η ≤
        (N:ℝ)^((1:ℝ)/2+1/4)*Real.sqrt (capDiscrepancyL2Sq2 X)) ∧
      ∃ X : ConfigurationD 2 N,
        (N:ℝ)^((1:ℝ)/2+1/4)*Real.sqrt (capDiscrepancyL2Sq2 X) ≤
          sphereCapDiscrepancyConst2+η :=
  sphere2_cap_discrepancy_sharp hexGaussianContact_all

end SphericalRiesz
end
end
end
