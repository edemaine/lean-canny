/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledRenaming
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Appending auxiliary variables without changing polynomial access -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def appendVariables {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (k : α → ℕ) (hk : ComputableInPolyTime k enc encUnary) :
    Controlled (fun w => MvPolynomial.rename (Fin.castAdd (k w)) (P w)) enc a := by
  apply C.rename (ComputableInPolyTime.unary_add' C.arity_computable hk)
    (fun w => Fin.castAdd (k w)) (fun q => q.2) (ComputableInPolyTime.snd _ _)
  intro w z i
  simp only [Fin.val_castAdd]

end LeanCanny.CountingHierarchy.Controlled
