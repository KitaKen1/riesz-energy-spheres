/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in licenses/TauCeti-Apache-2.0.txt.
Authors: The Tau Ceti contributors; adapted for this project by Codex

The doubled-root table and its finite certificate pattern are adapted from
TauCetiProject/TauCeti, commit 98962476aaba1de05b4a883df5af0562247cb501,
TauCeti/LinearAlgebra/RootSystem/E8Coordinates.lean. The local version avoids depending on
the newer Dynkin-type library. The coordinate model is Bourbaki, Plate VII.
-/
import E8Leech.StationaryProcess
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Concrete covolume-one E8 coordinate model and finite certificates

`e8Set` is the usual integer / half-integer model, expressed using doubled coordinates.
These finite certificates do not alone prove covolume or a span identification. E8Lattice
separately identifies this set with the integer span of an explicit triangular basis and
proves covolume one. Identification with the doubled Bourbaki root-span is not used.
-/

noncomputable section

namespace E8Leech

open Matrix

def e8Numerators : Set (Fin 8 → ℤ) :=
  {z | (∀ i, (2 : ℤ) ∣ z i - z 0) ∧ (4 : ℤ) ∣ ∑ i, z i}

def halfCoordinates (z : Fin 8 → ℤ) : Ambient 8 :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / 2)

/-- The concrete E8 set; even coordinate sum in both integer and half-integer cosets. -/
def e8Set : Set (Ambient 8) := halfCoordinates '' e8Numerators

def doubledRoots : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, -1, -1, -1, -1, -1, -1, 1;
     2, 2, 0, 0, 0, 0, 0, 0;
     -2, 2, 0, 0, 0, 0, 0, 0;
     0, -2, 2, 0, 0, 0, 0, 0;
     0, 0, -2, 2, 0, 0, 0, 0;
     0, 0, 0, -2, 2, 0, 0, 0;
     0, 0, 0, 0, -2, 2, 0, 0;
     0, 0, 0, 0, 0, -2, 2, 0]

def e8Gram : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0, 0;
     0, 2, 0, -1, 0, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0, 0;
     0, -1, -1, 2, -1, 0, 0, 0;
     0, 0, 0, -1, 2, -1, 0, 0;
     0, 0, 0, 0, -1, 2, -1, 0;
     0, 0, 0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, 0, 0, -1, 2]

/-- A kernel-checked finite arithmetic certificate, without `native_decide`. -/
theorem doubledRoots_gram : doubledRoots * doubledRootsᵀ = (4 : ℤ) • e8Gram := by
  decide

private theorem doubledRoots_parity :
    ∀ i j : Fin 8, (doubledRoots i j - doubledRoots i 0) % 2 = 0 := by decide

private theorem doubledRoots_sum :
    ∀ i : Fin 8, (∑ j, doubledRoots i j) % 4 = 0 := by decide

theorem doubledRoots_mem (i : Fin 8) : doubledRoots i ∈ e8Numerators := by
  exact ⟨fun j => Int.dvd_of_emod_eq_zero (doubledRoots_parity i j),
    Int.dvd_of_emod_eq_zero (doubledRoots_sum i)⟩

theorem simpleRoot_mem_e8 (i : Fin 8) : halfCoordinates (doubledRoots i) ∈ e8Set :=
  ⟨doubledRoots i, doubledRoots_mem i, rfl⟩

theorem zero_mem_e8 : (0 : Ambient 8) ∈ e8Set := by
  refine ⟨0, ?_, ?_⟩
  · simp [e8Numerators]
  · ext i
    simp [halfCoordinates]

end E8Leech
