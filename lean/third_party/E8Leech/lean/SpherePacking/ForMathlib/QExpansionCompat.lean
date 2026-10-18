-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
/-
Added for the E8Leach port (2026-10-10). Apache License 2.0, as the surrounding library.
-/
module
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Compatibility names for the earlier `ModularFormClass` `q`-expansion API

Pinned Mathlib moved these statements to `UpperHalfPlane` with explicit analyticity and
periodicity hypotheses. The lemmas below restore the earlier names and hypotheses, proved from
the current API, so that ported call sites need no change.
-/

open UpperHalfPlane SlashInvariantFormClass

namespace ModularFormClass

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)

public theorem cuspFunction_apply_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : cuspFunction h f 0 = valueAtInfty f :=
  UpperHalfPlane.cuspFunction_apply_zero hh (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (periodic_comp_ofComplex f hΓ)

public theorem qExpansion_coeff_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : (qExpansion h f).coeff 0 = valueAtInfty f :=
  UpperHalfPlane.qExpansion_coeff_zero hh (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (periodic_comp_ofComplex f hΓ)

public theorem hasFPowerSeries_cuspFunction [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.hasFPowerSeries_cuspFunction f hh
    (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (fun τ => τ.hasSum_qExpansion hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f))

public theorem hasSum_qExpansion_of_norm_lt [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.hasSum_qExpansion_of_norm_lt hh (periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) hq

end ModularFormClass
