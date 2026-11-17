/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledDegreePiece
public import LeanCanny.CountingHierarchy.DegreePiecePolynomialBounds
public import LeanCanny.CountingHierarchy.NativeBinaryBounds

/-! # Source-only budgets shared by every bounded degree-piece choice -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[fun_prop] theorem degreePieceMassExponent_polyTime {α : Type} {enc : α ↪ List Bool} {N b : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => degreePieceMassExponent (N w) (b w)) enc encNat :=
  ComputableInPolyTime.binary_add' (binarySize_polyTime (ComputableInPolyTime.binary_add' hN (.const 2)))
    (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_add' hb (.const 1)))

namespace Controlled

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}

theorem degreePiece_cutoff_le (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N d : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (w : α) (hdN : d w ≤ N w) :
    (C.degreePiece E hn N d hN hd).cutoff w ≤ max (C.cutoff w) (max (C.degreeBound w) (N w)) + 1 := by
  change max (max (max (max (C.cutoff w) (max (C.degreeBound w) (d w)) + 1) 0) 0)
    (max (C.cutoff w) (max (C.degreeBound w) (N w)) + 1) ≤ _
  simp only [Nat.max_zero]
  omega

end Controlled
end LeanCanny.CountingHierarchy
