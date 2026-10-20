/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulExterior
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-! # The Koszul chain complex of a finite input family

The exterior-degree maps form a Mathlib chain complex. A unit combination
of the inputs gives equality of kernels and images in every positive degree.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulExterior
variable {R I : Type*} [CommRing R] [Fintype I]
open CategoryTheory
open scoped BigOperators

noncomputable def complex (p : I → R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R (ExteriorAlgebra.exteriorPower R k (I → R)))
    (fun k => ModuleCat.ofHom (gradedDifferential p k)) (fun k => by
      apply ModuleCat.hom_ext
      exact gradedDifferential_comp p k)

theorem complex_d (p : I → R) (k : ℕ) :
    (complex p).d (k + 1) k = ModuleCat.ofHom (gradedDifferential p k) := by
  change ChainComplex.of.d (fun j : ℕ => ModuleCat.of R (ExteriorAlgebra.exteriorPower R j (I → R)))
    (fun j => ModuleCat.ofHom (gradedDifferential p j)) (k + 1) k = _
  exact ChainComplex.of_d _ _ k

theorem complex_exact (p v : I → R) (hv : ∑ i, v i * p i = 1) (k : ℕ) :
    LinearMap.ker ((complex p).d (k + 1) k).hom = LinearMap.range ((complex p).d (k + 2) (k + 1)).hom := by
  rw [complex_d, complex_d]
  exact graded_exact p v hv k

end LeanCanny.Algebra.KoszulExterior
