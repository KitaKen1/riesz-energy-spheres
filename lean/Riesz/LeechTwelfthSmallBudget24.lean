import Riesz.AmbientBumpSquare25
import Riesz.BoundaryTwelveTensor
import Riesz.EqualAreaMovingHigherBounds24
import Riesz.SmallPatchBumpError24
import Riesz.LeechGaussianBudget24

/-! Connections for constructing a common small-alpha budget from actual
physical bump errors.  The majorant of the global attaining sequence still
has to be built; no existence of a uniform budget is postulated here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def sphereBumpError25 {N : ℕ} (t M : ℝ) (X : ConfigurationD 24 N) (z : AmbientD 24) : ℝ :=
  (∑ i : Fin N, ambientBump25 t (X i : AmbientD 24) z) -
    M*bumpField25 t ambientSphereProbability24 z

theorem sphereGaussianDefect24_eq_bump_sq {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : ConfigurationD 24 N) :
    sphereGaussianDefect24 t M X = (4*t/Real.pi)^((25:ℝ)/2)*
      ∫ z : AmbientD 24, (sphereBumpError25 t M X z)^2 := by
  rw [sphereGaussianDefect24_eq_diffuse ht.le,diffuseGaussianDefect_eq_measureDefect ht.le,
    gaussianMeasureDefect_eq_bump_sq25 ht]
  simp only [sphereBumpError25,bumpField25,finitePointMeasure_integral]

theorem sphereGaussianDefect24_le_of_bump {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : ConfigurationD 24 N) {W : AmbientD 24 → ℝ}
    (hW : Integrable (fun z => W z^2))
    (hle : ∀ z, |sphereBumpError25 t M X z| ≤ W z) :
    sphereGaussianDefect24 t M X ≤ (4*t/Real.pi)^((25:ℝ)/2)*∫ z, W z^2 := by
  rw [sphereGaussianDefect24_eq_diffuse ht.le,diffuseGaussianDefect_eq_measureDefect ht.le]
  apply gaussianMeasureDefect_le_of_bump25 ht M _ _ hW
  simpa only [sphereBumpError25,bumpField25,finitePointMeasure_integral] using hle

/-- An actual profile envelope is integrated with its explicit constant. -/
theorem sphereGaussianSmallBudget24_le_of_profile {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq12 : q < 12) (X : ConfigurationD 24 N) (C : ℝ)
    (hC : ∀ α ∈ Ioc (0:ℝ) 4, sphereGaussianCenteredScaled24 α X+1 ≤ C) :
    sphereGaussianSmallBudget24 q X ≤ C*(4^q/q) := by
  have hi := sphereGaussianSmallBudget24_integrable hN hq hq12 X
  have hw : IntegrableOn (fun α : ℝ => α^(q-1)*C) (Ioc 0 4) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)
      (a:=0) (b:=4)).1).mul_const C
  have hv : (∫ α in Ioc (0:ℝ) 4, α^(q-1)) = 4^q/q := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 4),
      integral_rpow (Or.inl (by linarith))]
    rw [show q-1+1=q by ring, Real.zero_rpow hq.ne']
    ring
  unfold sphereGaussianSmallBudget24
  calc
    _ ≤ ∫ α in Ioc (0:ℝ) 4, α^(q-1)*C := by
      apply setIntegral_mono_on hi hw measurableSet_Ioc
      intro α hα
      exact mul_le_mul_of_nonneg_left (hC α hα) (Real.rpow_nonneg hα.1.le _)
    _ = C*(4^q/q) := by rw [integral_mul_const,hv]; ring

/-- Sufficient bound in physical R25, expressed as the real bump error, not a budget assumption. -/
theorem sphereGaussianSmallBudget24_le_of_bump {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq12 : q < 12) (X : ConfigurationD 24 N) (C : ℝ)
    (W : ℝ → AmbientD 24 → ℝ)
    (hW : ∀ α ∈ Ioc (0:ℝ) 4, Integrable (fun z => W α z^2))
    (hle : ∀ α ∈ Ioc (0:ℝ) 4, ∀ z,
      |sphereBumpError25 (sphereGaussianScale24 N α) (N:ℝ) X z| ≤ W α z)
    (hL2 : ∀ α ∈ Ioc (0:ℝ) 4,
      (4*sphereGaussianScale24 N α/Real.pi)^((25:ℝ)/2)*(∫ z,W α z^2) ≤ C*(N:ℝ)) :
    sphereGaussianSmallBudget24 q X ≤ C*(4^q/q) := by
  apply sphereGaussianSmallBudget24_le_of_profile hN hq hq12 X C
  intro α hα
  have ht : 0 < sphereGaussianScale24 N α := by
    rw [sphereGaussianScale24_eq_factor]
    exact mul_pos (sphereGaussianDensityFactor24_pos hN) hα.1
  have h := (sphereGaussianDefect24_le_of_bump ht (N:ℝ) X (hW α hα) (hle α hα)).trans (hL2 α hα)
  rw [sphereGaussianCenteredScaled24_add_one hN hα.1.le]
  exact (div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mpr h

/-- The twelfth-order tensor error cancels the n^24 point count when squared. -/
theorem twelveCubeQuadrature_squared_density_bound24 {n : ℕ} (hn : 74 ≤ n)
    {f : (Fin 24 → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube 24))
    (hs : ∀ i v, v ∈ UnitCube 24 →
      ContDiffOn ℝ 12 (fun t => f (Function.update v i t)) (Icc (0:ℝ) 1))
    (M : Fin 24 → ℝ) (hM0 : ∀ i, 0 ≤ M i)
    (hM : ∀ i v, v ∈ UnitCube 24 → ∀ t ∈ Icc (0:ℝ) 1,
      |iteratedDerivWithin 12 (fun u => f (Function.update v i u)) (Icc (0:ℝ) 1) t| ≤ M i) :
    (n:ℝ)^24*(twelveCubeQuadrature 24 n f-cubeIntegral 24 f)^2 ≤
      ((10:ℝ)^24*(∑ i,M i))^2 := by
  have h := twelveCubeQuadrature_twelfth_order_bound_on 24 hn hf hs M hM
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 ≤ ∑ i,M i := Finset.sum_nonneg (fun i _ => hM0 i)
  have he : (n:ℝ)^12*|twelveCubeQuadrature 24 n f-cubeIntegral 24 f| ≤ (10:ℝ)^24*(∑ i,M i) := by
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (n:ℝ)^12)
    calc
      _ ≤ (n:ℝ)^12*((10^24/(n:ℝ)^12)*(∑ i,M i)) := h'
      _ = _ := by field_simp
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ)^12*|twelveCubeQuadrature 24 n f-cubeIntegral 24 f|) he 2
  simpa only [mul_pow,← pow_mul,sq_abs] using hh

/-- A common positive allocation radius can satisfy the small-alpha mesh condition. -/
theorem exists_twelfth_small_alpha_radius24 {R C₀ : ℝ} (hR : 0 < R) :
    ∃ r > 0, r ≤ R ∧ sphereGaussianDensityFactor24 1*r^2*C₀^2 ≤ 48 := by
  let c : ℝ := sphereGaussianDensityFactor24 1*C₀^2
  have hc : 0 ≤ c := by
    have h := sphereGaussianDensityFactor24_pos (N:=1) (by norm_num)
    dsimp [c]; positivity
  let r : ℝ := min R (1/(c+1))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,hr,min_le_left _ _,?_⟩
  have h2 := pow_le_pow_left₀ hr.le (min_le_right R (1/(c+1))) 2
  have h3 : c*(1/(c+1))^2 ≤ 48 := by
    rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg c]
  calc
    sphereGaussianDensityFactor24 1*r^2*C₀^2 = c*r^2 := by dsimp [c]; ring
    _ ≤ c*(1/(c+1))^2 := mul_le_mul_of_nonneg_left h2 hc
    _ ≤ 48 := h3

/-- The actual density scale makes one mesh condition valid for every alpha in (0,4]. -/
theorem sphereGaussian_rational_twelfth_mesh24 (a d m : ℕ) (hd : 0 < d)
    (r ε C₀ : ℝ) (hratio : ε*(d:ℝ)=r*(a:ℝ))
    (hscale : sphereGaussianDensityFactor24 1*r^2*C₀^2 ≤ 48)
    {α : ℝ} (hα : α ∈ Ioc (0:ℝ) 4) :
    2*sphereGaussianScale24 ((d*m)^24) α*ε^2*C₀^2/384 ≤ ((a*m:ℕ):ℝ)^2 := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ε = r*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR).mpr hratio
  have hc : 0 ≤ sphereGaussianDensityFactor24 1*r^2*C₀^2 := by
    have h := sphereGaussianDensityFactor24_pos (N:=1) (by norm_num)
    positivity
  have hα4 := mul_le_mul_of_nonneg_left hα.2 hc
  have hf : 2*sphereGaussianDensityFactor24 1*α*r^2*C₀^2/384 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ)<384)]
    nlinarith
  have heq : 2*sphereGaussianScale24 ((d*m)^24) α*ε^2*C₀^2/384 =
      ((a*m:ℕ):ℝ)^2*(2*sphereGaussianDensityFactor24 1*α*r^2*C₀^2/384) := by
    rw [sphereGaussianScale24_eq_factor,sphereGaussianDensityFactor24_pow_twentyFour,he]
    push_cast
    field_simp <;> ring
  rw [heq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (sq_nonneg ((a*m:ℕ):ℝ))

/-- The actual patch bump envelope holds on all of (0,4] at rational allocation,
with one common radius and no refinement-dependent mesh premise. -/
theorem smallLeechPatch_bump_rational_small_alpha24 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallLeechCubePatch24,
      ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (r : ℝ), sphereGaussianDensityFactor24 1*r^2*patchChartLower24^2 ≤ 48 →
      ∀ (a d m : ℕ), 0 < d → 0 < m → p.ε*(d:ℝ)=r*(a:ℝ) → 74 ≤ a*m →
      ∀ α ∈ Ioc (0:ℝ) 4, ∀ z : AmbientD 24,
      |twelveCubeQuadrature 24 (a*m)
          (fun x => ambientBump25 (sphereGaussianScale24 ((d*m)^24) α) (smallLeechCubeMap24 p x) z)-
        cubeIntegral 24
          (fun x => ambientBump25 (sphereGaussianScale24 ((d*m)^24) α) (smallLeechCubeMap24 p x) z)| ≤
      bumpErrorConst24 patchChartUpper24 patchChartLower24/((a*m:ℕ):ℝ)^12*
        (1+(2*sphereGaussianScale24 ((d*m)^24) α*p.ε^2)^6)*
        cubeIntegral 24 (fun x => Real.exp
          (-(sphereGaussianScale24 ((d*m)^24) α/4*‖smallLeechCubeMap24 p x-z‖^2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_bump_quadrature12
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε r hscale a d m hd hm hratio hn α hα z
  have ht : 0 < sphereGaussianScale24 ((d*m)^24) α := by
    rw [sphereGaussianScale24_eq_factor]
    exact mul_pos (sphereGaussianDensityFactor24_pos (by positivity)) hα.1
  exact hb p hv hε (a*m) hn _ ht
    (sphereGaussian_rational_twelfth_mesh24 a d m hd r p.ε patchChartLower24 hratio hscale hα) z

/-- Radius fixed by exact sphere-probability mass, rather than chosen arbitrarily. -/
def leechUnitDensityRadius24 : ℝ := ((sphereAreaD 24).real univ)^((1:ℝ)/24)

theorem leechUnitDensityRadius24_pos : 0 < leechUnitDensityRadius24 :=
  Real.rpow_pos_of_pos (sphereAreaD_univ_pos 24) _

theorem leechUnitDensityRadius24_pow : leechUnitDensityRadius24^24 = (sphereAreaD 24).real univ := by
  unfold leechUnitDensityRadius24
  rw [←Real.rpow_natCast,←Real.rpow_mul (sphereAreaD_univ_pos 24).le]
  norm_num

theorem sphereGaussianDensityFactor24_unit_radius :
    sphereGaussianDensityFactor24 1*leechUnitDensityRadius24^2 = Real.pi := by
  have hA := sphereAreaD_univ_pos 24
  have hr : leechUnitDensityRadius24^2 = ((sphereAreaD 24).real univ)^((1:ℝ)/12) := by
    unfold leechUnitDensityRadius24
    rw [←Real.rpow_natCast,←Real.rpow_mul hA.le]
    norm_num
  rw [hr]
  unfold sphereGaussianDensityFactor24 sphereGaussianScale24
  norm_num only [Nat.cast_one,mul_one]
  rw [mul_assoc,←Real.mul_rpow (by positivity) hA.le,one_div_mul_cancel hA.ne',Real.one_rpow,mul_one]

theorem leechUnitDensityRadius24_twelfth_mesh_bound :
    sphereGaussianDensityFactor24 1*leechUnitDensityRadius24^2*patchChartLower24^2 ≤ 48 := by
  rw [sphereGaussianDensityFactor24_unit_radius]
  have hl : patchChartLower24 ≤ 1/2 := by
    unfold patchChartLower24
    rw [div_le_iff₀ (by positivity)]
    linarith [norm_nonneg leechInverseMap]
  have hs := pow_le_pow_left₀ patchChartLower24_pos.le hl 2
  calc
    Real.pi*patchChartLower24^2 ≤ Real.pi*(1/2)^2 := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    _ ≤ 48 := by linarith [Real.pi_lt_four]

/-- Actual patch probability equals its exact n^24/N allocation at every refinement. -/
theorem leechTwelfth_rational_exact_patch_mass24 (a d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (ε : ℝ) (hratio : ε*(d:ℝ)=leechUnitDensityRadius24*(a:ℝ)) :
    equalAreaLeechPatchProbabilityDensity24 ε = ((a*m:ℕ):ℝ)^24/((d*m:ℕ):ℝ)^24 := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hA := (sphereAreaD_univ_pos 24).ne'
  have he : ε = leechUnitDensityRadius24*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR).mpr hratio
  rw [equalAreaLeechPatchProbabilityDensity24,he,div_pow,mul_pow,leechUnitDensityRadius24_pow]
  push_cast
  field_simp

theorem sphereGaussian_exact_mass_twelfth_mesh24 (a d m : ℕ) (hd : 0 < d)
    (ε : ℝ) (hratio : ε*(d:ℝ)=leechUnitDensityRadius24*(a:ℝ))
    {α : ℝ} (hα : α ∈ Ioc (0:ℝ) 4) :
    2*sphereGaussianScale24 ((d*m)^24) α*ε^2*patchChartLower24^2/384 ≤ ((a*m:ℕ):ℝ)^2 :=
  sphereGaussian_rational_twelfth_mesh24 a d m hd leechUnitDensityRadius24 ε patchChartLower24
    hratio leechUnitDensityRadius24_twelfth_mesh_bound hα

/-- Exact mass allocation also fixes the dimensionless bump scale. -/
theorem sphereGaussian_exact_mass_bump_scale24 (a d m : ℕ) (hd : 0 < d)
    (ε α : ℝ) (hratio : ε*(d:ℝ)=leechUnitDensityRadius24*(a:ℝ)) :
    2*sphereGaussianScale24 ((d*m)^24) α*ε^2 = 2*Real.pi*((a*m:ℕ):ℝ)^2*α := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ε = leechUnitDensityRadius24*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR).mpr hratio
  have heq : sphereGaussianScale24 ((d*m)^24) α*ε^2 =
      (sphereGaussianDensityFactor24 1*leechUnitDensityRadius24^2)*((a*m:ℕ):ℝ)^2*α := by
    rw [sphereGaussianScale24_eq_factor,sphereGaussianDensityFactor24_pow_twentyFour,he]
    push_cast
    field_simp <;> ring
  rw [show 2*sphereGaussianScale24 ((d*m)^24) α*ε^2 =
    2*(sphereGaussianScale24 ((d*m)^24) α*ε^2) by ring,heq,
    sphereGaussianDensityFactor24_unit_radius]
  ring

end SphericalRiesz
