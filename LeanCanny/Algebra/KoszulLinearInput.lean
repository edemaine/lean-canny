/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulExterior

/-! # Linear dependence of Koszul contraction on its inputs -/

@[expose] public section

namespace LeanCanny.Algebra.KoszulExterior
open scoped BigOperators
variable {R I : Type*} [CommRing R] [Fintype I]

theorem linearForm_sub_smul (p q : I → R) (a : R) :
    linearForm (fun i => p i - a * q i) = linearForm p - a • linearForm q := by
  apply LinearMap.ext
  intro v
  change (∑ i, v i * (p i - a * q i)) = (∑ i, v i * p i) - a * ∑ i, v i * q i
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem differential_sub_smul (p q : I → R) (a : R) :
    differential (fun i => p i - a * q i) = differential p - a • differential q := by
  unfold differential
  rw [linearForm_sub_smul, map_sub, map_smul]

end LeanCanny.Algebra.KoszulExterior
