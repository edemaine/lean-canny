/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-! # Native polynomial-time classes on binary languages

These abbreviations specialize Complexitylib2's encoding-parametric definitions
to raw binary strings. In particular, reductions accept arbitrary native tidy
polynomial-time certificates, independently of the legacy FP bridge.
-/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

/-- A decision problem on arbitrary binary strings. -/
abbrev Language := Set (List Bool)

/-- Polynomial-time decision on raw binary inputs. -/
abbrev P : Set (Set (List Bool)) := Cslib.Complexity.P encBits

/-- Polynomial-time many-one reducibility on all binary strings. -/
abbrev PolyTimeReduces : Set (List Bool) → Set (List Bool) → Prop :=
  Cslib.Complexity.PolyTimeReducible encBits encBits

end LeanCanny
