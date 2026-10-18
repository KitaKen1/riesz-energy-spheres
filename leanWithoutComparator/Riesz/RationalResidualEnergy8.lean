import Riesz.SphereResidualAssembly8
import Riesz.RationalResidualPoints8

/-! A physical energy upper bound for the checked exact-size rational
configuration. The right side is still the actual fixed-patch union block;
its decomposition into local and cross blocks is the next obligation. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz
open Boundary

theorem rationalCubeFamily8_residual_mass_matching {K : ℕ}
    (P : Fin K → SmallE8CubePatch8) (a d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hbudget : K*a^8 ≤ d^8)
    (hmass : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) =
      (K:ℝ)*((a:ℝ)/d)^8) :
    (((d^8-K*a^8)*m^8:ℕ):ℝ) = (((d*m)^8:ℕ):ℝ)*
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i))ᶜ := by
  have hS : MeasurableSet (⋃ i, smallE8CubeSet8 (P i)) := MeasurableSet.iUnion
    (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
  have he := rationalCubeNodeBudget8_residual_ratio K a d m hd hm hbudget
  have hM : (((d*m)^8:ℕ):ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 8 (Nat.mul_pos hd hm).ne')
  have hc : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i))ᶜ =
      1-(K:ℝ)*((a:ℝ)/d)^8 := by
    rw [measureReal_compl hS,probReal_univ,hmass]
  rw [← hc] at he
  have h := (div_eq_iff hM).mp he
  simpa only [mul_comm] using h

theorem rationalCubeFamily8_exists_energy_upper {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hbudget : K*a^8 ≤ d^8)
    (hmass : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) =
      (K:ℝ)*((a:ℝ)/d)^8) :
    ∃ Y : Configuration ((d*m)^8),
      (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
        ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
      energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2 ≤
        sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
          (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ) := by
  classical
  let S := ⋃ i, smallE8CubeSet8 (P i)
  let nodes := rationalCubePatchNodes8 P a m ha hm
  let e0 := Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))
  let X := nodes ∘ e0.symm
  let r := (d^8-K*a^8)*m^8
  let M : ℝ := (((d*m)^8:ℕ):ℝ)
  obtain ⟨Z,_,_,_,_,hres,e,Y,hY⟩ :=
    rationalCubeFamily8_exists_configuration P hdis hu a d m ha hm hbudget
  have hS : MeasurableSet S := MeasurableSet.iUnion
    (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
  have hA := sphere8_complement_mass_ne_zero S hS hu
  have hr : (r:ℝ) = M*sphereProbability8.real Sᶜ :=
    rationalCubeFamily8_residual_mass_matching P a d m hd (by omega) hbudget hmass
  have hYfun : Y ∘ e = Sum.elim nodes Z := funext hY
  have hYe := sphereFiniteBlock4_reindex e Y univ M
  rw [hYfun] at hYe
  let e1 := e0.sumCongr (Equiv.refl (Fin r))
  have he1 : (Sum.elim X Z) ∘ e1 = Sum.elim nodes Z := by
    funext u
    cases u with
    | inl t =>
      change nodes (e0.symm (e0 t)) = nodes t
      rw [e0.symm_apply_apply]
    | inr j => rfl
  have hjoin := sphereFiniteBlock4_reindex e1 (Sum.elim X Z) univ M
  rw [he1] at hjoin
  refine ⟨Y,⟨e,fun t => hY (Sum.inl t)⟩,?_⟩
  calc
    _ = sphereFiniteBlock4 Y univ M := (sphereFiniteBlock4_eq_energy4 Y).symm
    _ = sphereFiniteBlock4 (Sum.elim nodes Z) univ M := hYe.symm
    _ = sphereFiniteBlock4 (Sum.elim X Z) univ M := hjoin
    _ ≤ sphereFiniteBlock4 X S M := sphereFiniteBlock4_residual_le X Z S hS hA M hr hres
    _ = _ := sphereFiniteBlock4_reindex e0.symm nodes S M

theorem sphere8_near_full_rational_energy_upper (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ K : ℕ, ∃ P : Fin K → SmallE8CubePatch8, ∃ a d : ℕ,
      ∃ ha : 0 < a, 0 < d ∧
      (∀ i, (P i).ε = equalAreaE8NormalizedScale8 ((a:ℝ)/d) ∧
        ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ ∧
        smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) ∧
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) ∧
      1-b < sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) ∧
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1 ∧
      sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8 ∧
      K*a^8 < d^8 ∧
      Filter.Tendsto (fun m : ℕ => (∑ i, ∑ j ∈ Finset.univ.erase i,
        smallE8CrossPhysicalBlock8 (P i) (P j) (a*m))/((d*m:ℕ):ℝ)^12)
        Filter.atTop (nhds 0) ∧
      (∀ m : ℕ, ∀ hm : 8 ≤ m, ∃ Y : Configuration ((d*m)^8),
        (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
          ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
        energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2 ≤
          sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
            (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)) := by
  obtain ⟨K,P,a,d,ha,hd,hdata,hdis,hl,hu,hmass,hbudget,_,hcross⟩ :=
    sphere8_near_full_rational_cubes_cross_zero ρ b hρ hb
  refine ⟨K,P,a,d,ha,hd,hdata,hdis,hl,hu,hmass,hbudget,hcross,?_⟩
  intro m hm
  exact rationalCubeFamily8_exists_energy_upper P hdis hu a d m ha hd hm hbudget.le hmass

end SphericalRiesz
