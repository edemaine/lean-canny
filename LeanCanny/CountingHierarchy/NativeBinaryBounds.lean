/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Binary access to sizes of binary bounds -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM

/-- The native size algorithm outputs unary; explicitly convert it when the
size participates in binary arithmetic for a degree or log-mass bound. -/
@[fun_prop] theorem binarySize_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f enc encNat) :
    ComputableInPolyTime (fun w => (f w).size) enc encNat :=
  ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.binary_size.comp hf)

end LeanCanny.CountingHierarchy
