/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeRange
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Binary sums over polynomially bounded ranges -/

@[expose] public section
namespace LeanCanny
open Turing.MultiTapeTM

theorem BinaryFn.sum {n f : List Bool → ℕ} (hn : UnaryFn n) (hf : BinaryFn f) :
    BinaryFn (fun z => ∑ i ∈ Finset.range (n z), f (pair z (List.replicate i true))) := by
  have h := ComputableTidilyInPolyTime.binary_sum.comp
    (ComputableTidilyInPolyTime.mapWithInput
      (f := fun z i => f (pair z (List.replicate i true)))
      (ComputableTidilyInPolyTime.range.comp hn) (hf.comp unaryPair_computable))
  refine BinaryFn.of_eq h fun z => ?_
  change ((List.range (n z)).map (fun i => f (pair z (List.replicate i true)))).sum = _
  induction n z with
  | zero => simp
  | succ k ih => simp [List.range_succ, List.map_append, ih, Finset.sum_range_succ]

end LeanCanny
