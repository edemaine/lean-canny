/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledFirstCoefficient
public import LeanCanny.CountingHierarchy.ControlledRenaming
public import LeanCanny.CountingHierarchy.DegreePiecePolynomial
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Uniform coefficient polynomials with an extra inverse coordinate -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def liftedCoefficient {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc) (hn : ComputableInPolyTime n enc encUnary)
    (k : α → ℕ) (hk : ComputableInPolyTime k enc encNat) :
    Controlled (fun w => liftedFirstCoefficient (P w) (k w)) enc (a + 1) := by
  apply (C.firstCoefficient E hn k hk).rename
    (ComputableInPolyTime.unary_add' hn (.const 1)) (fun _ => Fin.succ)
    (fun q => q.2.drop 1)
  · exact (ComputableTidilyInPolyTime.listDropWithInput
      (ComputableInPolyTime.snd enc (encList encNat)).tidy
      (ComputableTidilyInPolyTime.const 1)).computableInPolyTime
  · intro w z i
    simp only [List.getElem?_drop, Fin.val_succ, Nat.add_comm]

end LeanCanny.CountingHierarchy.Controlled
