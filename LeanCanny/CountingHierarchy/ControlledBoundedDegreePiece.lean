/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledDegreePieceBounds
public import LeanCanny.CountingHierarchy.ControlledBounds

/-! # Bounded degree pieces with common explicit access budgets -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def boundedDegreePiece {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc) (hn : ComputableInPolyTime n enc encUnary)
    (d : α → ℕ) (hd : ComputableInPolyTime d enc encNat) (hchoice : ∀ w, d w ≤ C.degreeBound w) :
    Controlled (fun w => degreePiecePolynomial (P w) (C.degreeBound w) (d w)) enc (a + 2) := by
  let CW := C.degreePiece E hn C.degreeBound d C.degree_computable hd
  exact CW.withBounds (fun w => 2 * (C.degreeBound w + 1))
    (fun w => degreePieceMassExponent (C.degreeBound w) (C.massExponent w))
    (fun w => max (C.cutoff w) (C.degreeBound w) + 1)
    (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_add' C.degree_computable (.const 1)))
    (degreePieceMassExponent_polyTime C.degree_computable C.mass_computable)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_max' C.cutoff_computable C.degree_computable) (.const 1))
    (fun w => (degreePiecePolynomial_degree_le (P w) (C.degreeBound w) (d w)).trans
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (C.degree_le w) 1)))
    (fun w => degreePiecePolynomial_mass_le (P w) (C.degreeBound w) (d w) (C.massExponent w) (C.mass_le w))
    (fun w => by simpa only [max_self] using
      C.degreePiece_cutoff_le E hn C.degreeBound d C.degree_computable hd w (hchoice w))

end LeanCanny.CountingHierarchy.Controlled
