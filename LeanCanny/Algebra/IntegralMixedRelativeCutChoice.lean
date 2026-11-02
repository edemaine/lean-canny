/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutFiniteGuards
/-! # Finite choice probes preserve the actual cut coordinate and parent

A probe changes only the finite choice. Values above the creating choice
are clipped internally; native callers retain an explicit validity guard.
Every strictly lower choice is exactly the factor required by Kind.Valid.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep
variable {n : ℕ} {P : SpatialSource n}

def atChoice (r : Rule n) (c : Kind P r) (k : ℕ) : Kind P r := match c with
  | .coordinate j c => .coordinate j ⟨min k c.val,(min_le_right _ _).trans_lt c.isLt⟩
  | .squarefree j c => .squarefree j ⟨min k c.val,(min_le_right _ _).trans_lt c.isLt⟩
  | .value j c => .value j ⟨min k c.val,(min_le_right _ _).trans_lt c.isLt⟩
  | .limitCoordinate j c => .limitCoordinate j ⟨min k c.val,(min_le_right _ _).trans_lt c.isLt⟩

theorem atChoice_self (r : Rule n) (c : Kind P r) : atChoice r c (choiceIndex r c)=c := by
  cases c <;> simp only [atChoice,choiceIndex,min_self]
theorem atChoice_lower (r : Rule n) (c : Kind P r) (k : ℕ) (hk : k<choiceIndex r c) :
    atChoice r c k=lowerChoice r c k hk := by
  cases c <;> simp only [choiceIndex] at hk <;> simp only [atChoice,lowerChoice,min_eq_left hk.le]
theorem choiceIndex_atChoice (r : Rule n) (c : Kind P r) (k : ℕ) :
    choiceIndex r (atChoice r c k)=min k (choiceIndex r c) := by cases c <;> rfl

end LeanCanny.Algebra.IntegralMixedRelativeCuts
