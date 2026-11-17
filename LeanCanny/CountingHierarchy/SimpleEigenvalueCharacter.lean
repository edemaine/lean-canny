/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CharacterOfEigenline
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Lean.Elab.Tactic.Omega

/-! # A simple multiplication eigenvalue is the value of an algebra character -/

public section

namespace LeanCanny.CountingHierarchy

open Module
open scoped Classical

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- Commuting multiplication operators preserve the one-dimensional
 eigenspace of a simple eigenvalue. Their scalar actions give a character
 whose value on the distinguished element is that eigenvalue. -/
theorem exists_character_of_simple_multiplication_eigenvalue (v : A) (η : K)
    (hroot : (Algebra.lmul K A v).charpoly.IsRoot η)
    (hsimple : (Algebra.lmul K A v).charpoly.rootMultiplicity η = 1) :
    ∃ χ : A →ₐ[K] K, χ v = η := by
  let φ := Algebra.lmul K A v
  have hEigen : φ.HasEigenvalue η :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly φ η).mpr hroot
  obtain ⟨w, hw⟩ := hEigen.exists_hasEigenvector
  have hwmem : w ∈ φ.eigenspace η := hw.1
  have hwne : w ≠ 0 := hw.2
  have hvw : v * w = η • w := by
    simpa only [φ, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using hw.apply_eq_smul
  have hpos : 0 < finrank K (φ.eigenspace η) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨w, hwmem⟩, fun h => hwne (congrArg Subtype.val h)⟩
  have hupper : finrank K (φ.eigenspace η) ≤ 1 := by
    simpa only [φ, hsimple] using LinearMap.finrank_eigenspace_le φ η
  have hdim : finrank K (φ.eigenspace η) = 1 := by omega
  have hline (a : A) : ∃ c : K, c • w = a * w := by
    have ha : a * w ∈ φ.eigenspace η := by
      apply Module.End.mem_eigenspace_iff.mpr
      change v * (a * w) = η • (a * w)
      rw [mul_left_comm v a w, hvw, mul_smul_comm]
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim
      (show (⟨w, hwmem⟩ : φ.eigenspace η) ≠ 0 from fun h => hwne (congrArg Subtype.val h))
      (⟨a * w, ha⟩ : φ.eigenspace η)
    exact ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨χ, hχ⟩ := exists_character_of_invariant_line w hwne hline
  refine ⟨χ, ?_⟩
  exact smul_left_injective K hwne ((hχ v).trans hvw)

end LeanCanny.CountingHierarchy
