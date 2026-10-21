/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! # Native unary arithmetic used by the encoders -/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

theorem UnaryFn.div {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => f z / g z) :=
  ComputableTidilyInPolyTime.unary_div.comp (hf.prod hg)

theorem UnaryFn.mod {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => f z % g z) :=
  ComputableTidilyInPolyTime.unary_mod.comp (hf.prod hg)

theorem UnaryFn.size {f : List Bool → ℕ} (hf : UnaryFn f) :
    UnaryFn (fun z => Nat.size (f z)) :=
  (UnaryFn.length (bits_mem_FP hf)).of_eq fun z => Nat.size_eq_bits_len (f z)

end LeanCanny
