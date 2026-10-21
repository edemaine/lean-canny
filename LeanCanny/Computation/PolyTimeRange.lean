/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeQuantifiers
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Native polynomial-time traversals of unary ranges -/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

theorem flatMap_range_mem_FP {E m : List Bool → List Bool} (hE : E ∈ FP) (hm : m ∈ FP) :
    (fun z => (List.range (m z).length).flatMap fun i =>
      E (pair z (List.replicate i true))) ∈ FP := by
  have h := ComputableTidilyInPolyTime.bitsFlatten
    (ComputableTidilyInPolyTime.mapWithInput
      (f := fun z i => E (pair z (List.replicate i true)))
      (ComputableTidilyInPolyTime.range.comp (UnaryFn.length hm))
      (hE.comp unaryPair_computable))
  change ComputableTidilyInPolyTime _ encBits encBits
  simpa only [List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq] using h

theorem bitwise_mem_FP {len : List Bool → ℕ} {b : List Bool → ℕ → Bool}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP)
    {G : List Bool → List Bool} (hG : G ∈ FP)
    (hGspec : ∀ x i, G (pair x (List.replicate i true)) = [b x i]) :
    (fun x => (List.range (len x)).map (b x)) ∈ FP := by
  refine mem_FP_of_eq (flatMap_range_mem_FP hG hlen) fun x => ?_
  simp only [List.length_replicate, hGspec]
  exact List.map_eq_flatMap.symm

theorem UnaryFn.sum {n f : List Bool → ℕ} (hn : UnaryFn n) (hf : UnaryFn f) :
    UnaryFn (fun z => ∑ i ∈ Finset.range (n z), f (pair z (List.replicate i true))) := by
  refine (UnaryFn.length (flatMap_range_mem_FP hf.mem_FP hn.mem_FP)).of_eq fun z => ?_
  simp only [List.length_flatMap, List.length_replicate]
  induction n z with
  | zero => simp
  | succ k ih => simp [List.range_succ, List.map_append, ih, Finset.sum_range_succ]

theorem UnaryFn.count {n : List Bool → ℕ} {p : List Bool → Prop} [DecidablePred p]
    (hn : UnaryFn n) (hp : FPPred p) :
    UnaryFn (fun z => ((Finset.range (n z)).filter
      fun i => p (pair z (List.replicate i true))).card) :=
  (hn.sum (UnaryFn.ite hp (UnaryFn.const 1) (UnaryFn.const 0))).of_eq fun _ =>
    (Finset.card_filter _ _).symm

theorem UnaryFn.find {n : List Bool → ℕ} {p : List Bool → Prop} [DecidablePred p]
    (hn : UnaryFn n) (hp : FPPred p) :
    UnaryFn (fun z => (List.range (n z)).findIdx
      fun i => decide (p (pair z (List.replicate i true)))) := by
  have hlist := ComputableTidilyInPolyTime.mapWithInput
    (f := fun z i => decide (p (pair z (List.replicate i true))))
    (ComputableTidilyInPolyTime.range.comp hn)
    (hp.computable.comp unaryPair_computable)
  refine UnaryFn.of_eq (ComputableTidilyInPolyTime.idxOfWithInput hlist
    (ComputableTidilyInPolyTime.const true)) fun z => ?_
  simp [List.idxOf, List.findIdx_map, Function.comp_def]

end LeanCanny
