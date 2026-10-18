import Riesz.AffineGridCube8
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order

/-! Normalize the common physical side length by the eighth root of actual
sphere area. A positive rational normalized length gives exact rational patch
probabilities. Shrinking about the cube midpoint preserves physical inclusion;
no new covering or separation theorem is required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

def sphereAreaRoot8 : ℝ := (sphereArea8.real univ)^((8 : ℝ)⁻¹)

def equalAreaE8NormalizedScale8 (t : ℝ) : ℝ := sphereAreaRoot8*t

def centeredCubeRescale8 (t : ℝ) (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  cubeMidpoint8+t • (x-cubeMidpoint8)

theorem sphereAreaRoot8_pos : 0 < sphereAreaRoot8 := by
  unfold sphereAreaRoot8
  apply Real.rpow_pos_of_pos
  rw [sphereArea8_mass_real]
  positivity

theorem sphereAreaRoot8_pow : sphereAreaRoot8^8 = sphereArea8.real univ := by
  unfold sphereAreaRoot8
  exact Real.rpow_inv_natCast_pow (by rw [sphereArea8_mass_real]; positivity) (by decide)

theorem equalAreaE8NormalizedScale8_density (t : ℝ) :
    (equalAreaE8NormalizedScale8 t)^8/sphereArea8.real univ = t^8 := by
  have hA : sphereArea8.real univ ≠ 0 := by rw [sphereArea8_mass_real]; positivity
  rw [equalAreaE8NormalizedScale8,mul_pow,sphereAreaRoot8_pow,mul_div_cancel_left₀ _ hA]

theorem exists_positive_nat_fraction_btwn (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ a < (p : ℝ)/q ∧ (p : ℝ)/q < b := by
  obtain ⟨r,hrl,hru⟩ := exists_rat_btwn hab
  have hr : 0 < r := by exact_mod_cast (ha.trans hrl)
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have heq : (r : ℝ) = (r.num.natAbs : ℝ)/r.den := by
    rw [Rat.cast_def,← Int.natAbs_of_nonneg hn.le]
    simp
  exact ⟨r.num.natAbs,r.den,Int.natAbs_pos.mpr hn.ne',r.den_pos,
    by simpa only [heq] using hrl,by simpa only [heq] using hru⟩

theorem centeredCubeRescale8_mem_unitCube (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) : centeredCubeRescale8 t x ∈ UnitCube 8 := by
  intro i
  change 0 ≤ 1/2+t*(x i-1/2) ∧ 1/2+t*(x i-1/2) ≤ 1
  have hlo := mul_nonneg ht (hx i).1
  have hhi := mul_nonneg ht (sub_nonneg.mpr (hx i).2)
  constructor <;> nlinarith

theorem equalAreaE8Patch_smaller_scale_identity
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v : Fin 8 → ℝ)
    (ε ℓ : ℝ) (hε : ε ≠ 0) (x : Fin 8 → ℝ) :
    equalAreaE8Patch g v cubeMidpoint8 ε (centeredCubeRescale8 (ℓ/ε) x) =
      equalAreaE8Patch g v cubeMidpoint8 ℓ x := by
  have hx : centeredCubeRescale8 (ℓ/ε) x-cubeMidpoint8 =
      (ℓ/ε) • (x-cubeMidpoint8) := by simp [centeredCubeRescale8]
  simp only [equalAreaE8Patch,equalAreaMovingE8Chart,hx,map_smul,smul_smul]
  rw [mul_div_cancel₀ ℓ hε]

theorem equalAreaE8SphereCube8_scale_mono
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v : Fin 8 → ℝ)
    (ε ℓ : ℝ) (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hle : ℓ ≤ ε) :
    equalAreaE8SpherePatch8 g v cubeMidpoint8 ℓ (UnitCube 8) ⊆
      equalAreaE8SpherePatch8 g v cubeMidpoint8 ε (UnitCube 8) := by
  rintro y ⟨x,hx,hxy⟩
  refine ⟨centeredCubeRescale8 (ℓ/ε) x,
    centeredCubeRescale8_mem_unitCube _ (div_nonneg hℓ hε.le)
      ((div_le_one hε).mpr hle) x hx,?_⟩
  rw [equalAreaE8Patch_smaller_scale_identity g v ε ℓ hε.ne']
  exact hxy

theorem normalizedCubeMass8_integer_budget (K p q : ℕ) (hq : 0 < q)
    (hm : (K : ℝ)*((p : ℝ)/q)^8 < 1) : K*p^8 < q^8 := by
  have hq8 : 0 < (q : ℝ)^8 := by positivity
  have h : (K : ℝ)*(p : ℝ)^8 < (q : ℝ)^8 := by
    apply (div_lt_one hq8).mp
    simpa only [div_pow,mul_div_assoc] using hm
  exact_mod_cast h

theorem equalAreaE8SphereCube8_normalized_probability_real
    (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v : Fin 8 → ℝ) (t : ℝ) (ht : 0 < t)
    (hsmall : ‖v‖+equalAreaE8NormalizedScale8 t*equalAreaScaleRadius ≤ 1/8) :
    sphereProbability8.real
      (equalAreaE8SpherePatch8 g v cubeMidpoint8 (equalAreaE8NormalizedScale8 t) (UnitCube 8)) = t^8 := by
  have he : 0 < equalAreaE8NormalizedScale8 t := mul_pos sphereAreaRoot8_pos ht
  rw [equalAreaE8SpherePatch8_probability_real g v cubeMidpoint8 _ he _
    (unitCube_measurableSet 8)
    (equalAreaE8Affine8_cube_domain v cubeMidpoint8 _ he cubeMidpoint8_mem_unitCube hsmall)]
  rw [Measure.real,unitCube_volume,ENNReal.toReal_one,mul_one]
  exact equalAreaE8NormalizedScale8_density t

end SphericalRiesz
