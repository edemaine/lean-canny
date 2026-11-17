/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerResidue
public import LeanCanny.CountingHierarchy.GridEnumeration

/-! # Addressing the finite indices of the residue functional -/

public section

namespace LeanCanny.CountingHierarchy

open PurePowerResidue
open scoped Classical BigOperators

/-- Base-`B+1` addresses enumerate the actual rectangular residue indices,
 including its unique empty index in dimension zero. -/
theorem sum_residue_grid {M : Type*} [AddCommMonoid M] (B n : ℕ)
    (F : (Fin n → ℕ) → M) :
    (∑ s ∈ Finset.range ((B + 1) ^ n),
      F (fun i => (gridPoint (B + 1) n s)[i.val]?.getD 0)) =
        ∑ j ∈ indices n B, F j := by
  have hpoint (s : ℕ) (i : Fin n) :
      (gridPoint (B + 1) n s)[i.val]?.getD 0 = s / (B + 1) ^ i.val % (B + 1) :=
    gridPoint_get i.isLt
  simp_rw [hpoint]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ z : Fin n → Fin (B + 1), F (fun i => (z i).val) :=
      (finFunctionFinEquiv : (Fin n → Fin (B + 1)) ≃ Fin ((B + 1) ^ n)).symm.sum_comp
        (fun z => F (fun i => (z i).val))
    _ = ∑ j ∈ indices n B, F j := by
      apply Finset.sum_bij (fun z _ => fun i => (z i).val)
      · intro z _
        exact mem_indices.mpr (fun i => by have := (z i).isLt; omega)
      · intro z _ w _ h
        funext i
        exact Fin.ext (congrFun h i)
      · intro j hj
        exact ⟨fun i => ⟨j i, by have := mem_indices.mp hj i; omega⟩, Finset.mem_univ _, rfl⟩
      · intro z _
        rfl

end LeanCanny.CountingHierarchy
