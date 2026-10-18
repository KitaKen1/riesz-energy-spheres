import Riesz.RationalNodeBudget8

/-! Construct the rationally normalized common-scale family, retaining actual
near-full sphere probability, uniform smallness and the original physical gap.
The exact original quadrature-index budget is included. No residual physical
points, global injective configuration or global energy bound is asserted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

theorem sphere8_near_full_rational_affine_cubes (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ v : Fin K → Fin 8 → ℝ, ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ∃ ℓ > 0, ℓ = equalAreaE8NormalizedScale8 ((p : ℝ)/q) ∧
      ℓ*equalAreaScaleRadius ≤ ρ ∧
      (∀ i, ‖v i‖ ≤ ρ ∧ ‖v i‖+ℓ*equalAreaScaleRadius ≤ 1/8 ∧
        IsCompact (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))
        (equalAreaE8SpherePatch8 (g j) (v j) cubeMidpoint8 ℓ (UnitCube 8))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8),
        ∀ y ∈ equalAreaE8SpherePatch8 (g j) (v j) cubeMidpoint8 ℓ (UnitCube 8), δ < dist x y) ∧
      1-b < sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) ∧
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) < 1 ∧
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) =
        (K : ℝ)*((p : ℝ)/q)^8 ∧
      (∀ i, sphereProbability8.real
        (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) = ((p : ℝ)/q)^8) ∧
      K*p^8 < q^8 ∧
      (∀ m : ℕ, 8 ≤ m →
        Fintype.card (rationalCubeNodeIndex8 K p q m) = (q*m)^8 ∧
        Fintype.card (Fin 8 → NodeIndex (p*m)) = (p*m)^8 ∧
        0 < (q^8-K*p^8)*m^8 ∧
        (((p*m)^8 : ℕ) : ℝ)/(((q*m)^8 : ℕ) : ℝ) = ((p : ℝ)/q)^8 ∧
        ((((q^8-K*p^8)*m^8 : ℕ) : ℝ)/(((q*m)^8 : ℕ) : ℝ)) =
          1-(K : ℝ)*((p : ℝ)/q)^8) := by
  obtain ⟨K,g,v,ε,hε,hscale,hcell,hd,hgap,hl,hu,heq⟩ :=
    sphere8_near_full_small_affine_cubes ρ (min (b/4) (1/4)) hρ
      (lt_min (by positivity) (by norm_num))
  let H := ⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8)
  let w := sphereProbability8.real H
  have hw : w = (K : ℝ)*(ε^8/sphereArea8.real univ) := heq
  obtain ⟨γ,hγ,hγ1,hkeep,_⟩ := shrinkMass8_loss_budget b w hb
    measureReal_nonneg hu.le hl
  have hR := sphereAreaRoot8_pos
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hlow : 0 < (1-γ)*ε/sphereAreaRoot8 := by positivity
  have hinterval : (1-γ)*ε/sphereAreaRoot8 < ε/sphereAreaRoot8 := by
    apply div_lt_div_of_pos_right _ hR
    nlinarith
  obtain ⟨p,q,hp,hq,hrl,hru⟩ := exists_positive_nat_fraction_btwn _ _ hlow hinterval
  let ℓ := equalAreaE8NormalizedScale8 ((p : ℝ)/q)
  have ht : 0 < (p : ℝ)/q := by positivity
  have hℓ : 0 < ℓ := mul_pos hR ht
  have hℓε : ℓ < ε := by
    simpa only [ℓ,equalAreaE8NormalizedScale8,mul_comm] using (lt_div_iff₀ hR).mp hru
  have hℓlo : (1-γ)*ε < ℓ := by
    simpa only [ℓ,equalAreaE8NormalizedScale8,mul_comm] using (div_lt_iff₀ hR).mp hrl
  have hsmall : ∀ i, ‖v i‖+ℓ*equalAreaScaleRadius ≤ 1/8 := by
    intro i
    have he := mul_le_mul_of_nonneg_right hℓε.le equalAreaScaleRadius_pos.le
    linarith [(hcell i).2.1]
  have hsub : ∀ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8) ⊆
      equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ε (UnitCube 8) := fun i =>
    equalAreaE8SphereCube8_scale_mono (g i) (v i) ε ℓ hε hℓ.le hℓε.le
  have hd' : Pairwise (fun i j => Disjoint
      (equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8))
      (equalAreaE8SpherePatch8 (g j) (v j) cubeMidpoint8 ℓ (UnitCube 8))) :=
    fun i j hij => (hd hij).mono (hsub i) (hsub j)
  have hmass := equalAreaE8CubeUnion8_probability_real g v (fun _ => cubeMidpoint8) ℓ hℓ
    (fun _ => cubeMidpoint8_mem_unitCube) hsmall hd'
  have hmass' : sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) =
      (K : ℝ)*((p : ℝ)/q)^8 := by
    rw [hmass]
    change (K : ℝ)*((equalAreaE8NormalizedScale8 ((p : ℝ)/q))^8/sphereArea8.real univ) = _
    rw [equalAreaE8NormalizedScale8_density]
  have hupper : sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) < 1 :=
    (measureReal_mono (iUnion_mono hsub) (measure_ne_top _ _)).trans_lt hu
  have hlower : 1-b < sphereProbability8.real
      (⋃ i, equalAreaE8SpherePatch8 (g i) (v i) cubeMidpoint8 ℓ (UnitCube 8)) := by
    apply hkeep.trans_le
    calc
      (1-γ)^8*w = (K : ℝ)*(((1-γ)*ε)^8/sphereArea8.real univ) := by
        rw [hw,mul_pow]
        ring
      _ ≤ (K : ℝ)*(ℓ^8/sphereArea8.real univ) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hℓlo.le 8) hA.le) (Nat.cast_nonneg _)
      _ = _ := hmass.symm
  have hbudget : K*p^8 < q^8 := normalizedCubeMass8_integer_budget K p q hq
    (by simpa only [hmass'] using hupper)
  refine ⟨K,g,v,p,q,hp,hq,ℓ,hℓ,rfl,
    (mul_le_mul_of_nonneg_right hℓε.le equalAreaScaleRadius_pos.le).trans hscale,
    ?_,hd',?_,hlower,hupper,hmass',?_,hbudget,?_⟩
  · intro i
    exact ⟨(hcell i).1,hsmall i,
      equalAreaE8SpherePatch8_cube_isCompact (g i) (v i) cubeMidpoint8 ℓ hℓ
        cubeMidpoint8_mem_unitCube (hsmall i)⟩
  · obtain ⟨δ,hδ,hsep⟩ := hgap
    exact ⟨δ,hδ,fun i j hij x hx y hy => hsep i j hij x (hsub i hx) y (hsub j hy)⟩
  · intro i
    exact equalAreaE8SphereCube8_normalized_probability_real (g i) (v i) _ ht (hsmall i)
  · intro m hm
    have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
    exact ⟨rationalCubeNodeIndex8_card K p q m hp hm hbudget.le,
      rationalPatchNodeIndex8_card p m hp hm,
      rationalCubeNodeBudget8_positive K p q m hbudget hm0,
      rationalCubeNodeBudget8_patch_ratio p q m hm0,
      rationalCubeNodeBudget8_residual_ratio K p q m hq hm0 hbudget.le⟩

end SphericalRiesz
