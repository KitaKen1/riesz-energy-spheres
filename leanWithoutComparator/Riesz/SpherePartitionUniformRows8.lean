import Riesz.SpherePartitionCoordinateProfiles8
import Riesz.CompactUniformApproximateIdentity

/-!
The original finite localized Schwartz kernel on the actual Sphere8 probability
measure. Exact weighted coordinate transport and dilation identify each row
with a compact approximate identity. Uniform control of all Euclidean centers
and the actual identity sum eta_i^2=1 give uniform sphere rows and the original
double background limit. No Gaussian minorant or sharp profile is assumed or
constructed here. The weights need continuity, not global smoothness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
namespace SphericalRiesz

theorem compactDilationRow_eq_approximateRow {d : ℕ}
    (q k : EuclideanSpace ℝ (Fin d) → ℝ) {a : ℝ} (ha : 0 < a)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ v, q v*k (a • (u-v))) = (a^d)⁻¹*compactApproximateRow q k a u := by
  calc
    _ = ∫ w, q (u-w)*k (a • w) := by
      have h := integral_sub_left_eq_self
        (fun v => q v*k (a • (u-v))) (volume : Measure (EuclideanSpace ℝ (Fin d))) u
      simpa only [sub_sub_cancel] using h.symm
    _ = _ := by
      have h := Measure.integral_comp_smul_of_nonneg
        (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (fun z => q (u-a⁻¹ • z)*k z) a (hR := ha.le)
      simpa only [compactApproximateRow, smul_smul, inv_mul_cancel₀ ha.ne',
        one_smul, smul_eq_mul, finrank_euclideanSpace_fin] using h

def spherePartitionSchwartzComponent8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K)
    (x y : Sphere8) : ℝ :=
  sphereFiniteCutoffWeight8 ρ hρ g i x*sphereFiniteCutoffWeight8 ρ hρ g i y*
    (f (a • (rotatedSphereEqualAreaCoordinates8 (g i) x-
      rotatedSphereEqualAreaCoordinates8 (g i) y))).re

def spherePartitionSchwartzKernel8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (x y : Sphere8) : ℝ :=
  ∑ i, spherePartitionSchwartzComponent8 ρ hρ g f a i x y

def spherePartitionSchwartzRow8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (x : Sphere8) : ℝ :=
  ∫ y, spherePartitionSchwartzKernel8 ρ hρ g f a x y ∂sphereProbability8

def spherePartitionSchwartzBackground8 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) : ℝ :=
  ∫ x, ∫ y, spherePartitionSchwartzKernel8 ρ hρ g f a x y
    ∂sphereProbability8 ∂sphereProbability8

theorem rotatedSphereEqualAreaCoordinates8_measurable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    Measurable (rotatedSphereEqualAreaCoordinates8 g) :=
  sphereEqualAreaCoordinates8_measurable.comp (sphereRotation8 g.symm).measurable

theorem spherePartitionSchwartzComponent8_measurable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) :
    Measurable (fun p : Sphere8 × Sphere8 => spherePartitionSchwartzComponent8 ρ hρ g f a i p.1 p.2) := by
  have hw := (sphereFiniteCutoffWeight8_continuous ρ hρ g hc hpos i).measurable
  have hu := rotatedSphereEqualAreaCoordinates8_measurable (g i)
  have hfu : Continuous (fun z : EuclideanSpace ℝ (Fin 8) => (f (a • z)).re) := by fun_prop
  exact ((hw.comp measurable_fst).mul (hw.comp measurable_snd)).mul
    (hfu.measurable.comp ((hu.comp measurable_fst).sub (hu.comp measurable_snd)))

theorem spherePartitionSchwartzComponent8_norm_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) (x y : Sphere8) :
    ‖spherePartitionSchwartzComponent8 ρ hρ g f a i x y‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
  have hx0 := sphereFiniteCutoffWeight8_nonneg ρ hρ g i x
  have hy0 := sphereFiniteCutoffWeight8_nonneg ρ hρ g i y
  have hx1 := sphereFiniteCutoffWeight8_le_one ρ hρ g hpos i x
  have hy1 := sphereFiniteCutoffWeight8_le_one ρ hρ g hpos i y
  have hw : sphereFiniteCutoffWeight8 ρ hρ g i x*sphereFiniteCutoffWeight8 ρ hρ g i y ≤ 1 := by
    simpa using mul_le_mul hx1 hy1 hy0 zero_le_one
  have hf : |(f (a • (rotatedSphereEqualAreaCoordinates8 (g i) x-
      rotatedSphereEqualAreaCoordinates8 (g i) y))).re| ≤ SchwartzMap.seminorm ℝ 0 0 f :=
    (Complex.abs_re_le_norm _).trans (SchwartzMap.norm_le_seminorm ℝ f _)
  simp only [spherePartitionSchwartzComponent8, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hx0, abs_of_nonneg hy0]
  simpa using mul_le_mul hw hf (abs_nonneg _) zero_le_one

theorem spherePartitionSchwartzComponent8_row_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) (x : Sphere8) :
    Integrable (spherePartitionSchwartzComponent8 ρ hρ g f a i x) sphereProbability8 := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    ((spherePartitionSchwartzComponent8_measurable ρ hρ g hc hpos f a i).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (spherePartitionSchwartzComponent8_norm_le ρ hρ g hpos f a i x)

theorem spherePartitionSchwartzComponent8_product_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) :
    Integrable (fun p : Sphere8 × Sphere8 => spherePartitionSchwartzComponent8 ρ hρ g f a i p.1 p.2)
      (sphereProbability8.prod sphereProbability8) := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (spherePartitionSchwartzComponent8_measurable ρ hρ g hc hpos f a i).aestronglyMeasurable
  exact Eventually.of_forall fun p => spherePartitionSchwartzComponent8_norm_le ρ hρ g hpos f a i p.1 p.2

theorem spherePartitionSchwartzKernel8_product_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    Integrable (fun p : Sphere8 × Sphere8 => spherePartitionSchwartzKernel8 ρ hρ g f a p.1 p.2)
      (sphereProbability8.prod sphereProbability8) := by
  classical
  exact integrable_finsetSum _ fun i _ =>
    spherePartitionSchwartzComponent8_product_integrable ρ hρ g hc hpos f a i

theorem spherePartitionSchwartzRow8_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    Integrable (spherePartitionSchwartzRow8 ρ hρ g f a) sphereProbability8 :=
  (spherePartitionSchwartzKernel8_product_integrable ρ hρ g hc hpos f a).integral_prod_left

theorem spherePartitionSchwartzRow8_eq_sum {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (x : Sphere8) :
    spherePartitionSchwartzRow8 ρ hρ g f a x =
      ∑ i, ∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i x y ∂sphereProbability8 := by
  classical
  exact integral_finsetSum _ fun i _ =>
    spherePartitionSchwartzComponent8_row_integrable ρ hρ g hc hpos f a i x

theorem spherePartitionSchwartzComponent8_row_transport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) (x : Sphere8) :
    (∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i x y ∂sphereProbability8) =
      sphereFiniteCutoffWeight8 ρ hρ g i x*(sphereArea8.real univ)⁻¹*
        ∫ v, sphereFiniteCutoffProfile8 ρ hρ g i v*
          (f (a • (rotatedSphereEqualAreaCoordinates8 (g i) x-v))).re := by
  simp only [spherePartitionSchwartzComponent8, mul_assoc]
  rw [integral_const_mul, sphereFiniteCutoffWeight8_probability_integral ρ hρ g hpos i
    (fun v => (f (a • (rotatedSphereEqualAreaCoordinates8 (g i) x-v))).re)]

theorem spherePartitionSchwartzComponent8_scaled_row {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) {a : ℝ} (ha : 0 < a) (i : Fin K) (x : Sphere8) :
    a^8*sphereArea8.real univ*
      (∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i x y ∂sphereProbability8) =
      sphereFiniteCutoffWeight8 ρ hρ g i x*
        compactApproximateRow (sphereFiniteCutoffProfile8 ρ hρ g i) (fun h => (f h).re) a
          (rotatedSphereEqualAreaCoordinates8 (g i) x) := by
  have hA : sphereArea8.real univ ≠ 0 := by rw [sphereArea8_mass_real]; positivity
  rw [spherePartitionSchwartzComponent8_row_transport ρ hρ g hpos,
    compactDilationRow_eq_approximateRow (sphereFiniteCutoffProfile8 ρ hρ g i)
      (fun h => (f h).re) ha (rotatedSphereEqualAreaCoordinates8 (g i) x)]
  have ha8 : a^8 ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp

theorem spherePartitionSchwartzComponent8_scaled_row_error {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) {a : ℝ} (ha : 0 < a) (i : Fin K) (x : Sphere8) :
    a^8*sphereArea8.real univ*
      (∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i x y ∂sphereProbability8)-
      (sphereFiniteCutoffWeight8 ρ hρ g i x)^2*((𝓕 f) 0).re =
      sphereFiniteCutoffWeight8 ρ hρ g i x*
        (compactApproximateRow (sphereFiniteCutoffProfile8 ρ hρ g i) (fun h => (f h).re) a
          (rotatedSphereEqualAreaCoordinates8 (g i) x)-
          sphereFiniteCutoffProfile8 ρ hρ g i (rotatedSphereEqualAreaCoordinates8 (g i) x)*((𝓕 f) 0).re) := by
  rw [spherePartitionSchwartzComponent8_scaled_row ρ hρ g hpos f ha,
    mul_sub, ← mul_assoc, sphereFiniteCutoffWeight8_times_profile_eq_square ρ hρ g hpos]

theorem spherePartitionSchwartzRow8_uniform {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(a n)^8*sphereArea8.real univ*spherePartitionSchwartzRow8 ρ hρ g f (a n) x-((𝓕 f) 0).re| < ε := by
  classical
  intro ε hε
  let δ : ℝ := ε/((K : ℝ)+1)
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : ∀ᶠ n in atTop, ∀ i : Fin K, ∀ u,
      |compactApproximateRow (sphereFiniteCutoffProfile8 ρ hρ g i) (fun h => (f h).re) (a n) u-
        sphereFiniteCutoffProfile8 ρ hρ g i u*((𝓕 f) 0).re| < δ := by
    apply eventually_all.mpr
    intro i
    exact compactSchwartzApproximateRow_uniform _
      (sphereFiniteCutoffProfile8_continuous ρ hρ hr g hc hpos i)
      (sphereFiniteCutoffProfile8_compactSupport ρ hρ g i) f ha δ hδ
  filter_upwards [hsmall] with n hn
  intro x
  have heq : (a n)^8*sphereArea8.real univ*spherePartitionSchwartzRow8 ρ hρ g f (a n) x-((𝓕 f) 0).re =
      ∑ i, ((a n)^8*sphereArea8.real univ*
        (∫ y, spherePartitionSchwartzComponent8 ρ hρ g f (a n) i x y ∂sphereProbability8)-
        (sphereFiniteCutoffWeight8 ρ hρ g i x)^2*((𝓕 f) 0).re) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      sphereFiniteCutoffWeight8_sum_square ρ hρ g hpos, one_mul,
      spherePartitionSchwartzRow8_eq_sum ρ hρ g hc hpos]
  rw [heq]
  calc
    _ ≤ ∑ i, |(a n)^8*sphereArea8.real univ*
        (∫ y, spherePartitionSchwartzComponent8 ρ hρ g f (a n) i x y ∂sphereProbability8)-
        (sphereFiniteCutoffWeight8 ρ hρ g i x)^2*((𝓕 f) 0).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin K, δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [spherePartitionSchwartzComponent8_scaled_row_error ρ hρ g hpos f (ha0 n), abs_mul,
        abs_of_nonneg (sphereFiniteCutoffWeight8_nonneg ρ hρ g i x)]
      calc
        _ ≤ sphereFiniteCutoffWeight8 ρ hρ g i x*δ :=
          mul_le_mul_of_nonneg_left (hn i _).le (sphereFiniteCutoffWeight8_nonneg ρ hρ g i x)
        _ ≤ δ := by
          simpa using mul_le_mul_of_nonneg_right (sphereFiniteCutoffWeight8_le_one ρ hρ g hpos i x) hδ.le
    _ = (K : ℝ)*δ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (show 0 < (K : ℝ)+1 by positivity)]
      nlinarith

theorem spherePartitionSchwartzBackground8_scaled_tendsto {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^8*sphereArea8.real univ*spherePartitionSchwartzBackground8 ρ hρ g f (a n))
      atTop (𝓝 ((𝓕 f) 0).re) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := spherePartitionSchwartzRow8_uniform ρ hρ hr g hc hpos f ha ha0 (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hi := spherePartitionSchwartzRow8_integrable ρ hρ g hc hpos f (a n)
  have hdiff : (a n)^8*sphereArea8.real univ*spherePartitionSchwartzBackground8 ρ hρ g f (a n)-((𝓕 f) 0).re =
      ∫ x, (a n)^8*sphereArea8.real univ*spherePartitionSchwartzRow8 ρ hρ g f (a n) x-((𝓕 f) 0).re ∂sphereProbability8 := by
    rw [integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul]
    simp [spherePartitionSchwartzBackground8, spherePartitionSchwartzRow8]
  rw [Real.dist_eq, hdiff]
  have hb := norm_integral_le_of_norm_le_const (μ := sphereProbability8)
    (f := fun x => (a n)^8*sphereArea8.real univ*spherePartitionSchwartzRow8 ρ hρ g f (a n) x-((𝓕 f) 0).re)
    (C := ε/2)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hN n hn x).le)
  have hb' : |∫ x, (a n)^8*sphereArea8.real univ*spherePartitionSchwartzRow8 ρ hρ g f (a n) x-((𝓕 f) 0).re ∂sphereProbability8| ≤ ε/2 := by
    simpa only [Real.norm_eq_abs, measureReal_def, sphereProbability8_mass, ENNReal.toReal_one, mul_one] using hb
  exact hb'.trans_lt (by linarith)

end SphericalRiesz
