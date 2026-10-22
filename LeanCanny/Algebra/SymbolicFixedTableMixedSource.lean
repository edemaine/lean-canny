/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableMatrix
public import LeanCanny.Algebra.BerkowitzSingleCallSource
public import LeanCanny.Computation.SingleCallLeaf

/-! # Native leaves and zero guards in the symbolic recursive source

The leaf computation is local and fully charged. The zero guard handles alpha
indices beyond the node's encoding radix. Every active source request still
strictly decreases the actual unary balanced address height.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTableMixedSource
open LeanCanny.Encoding LeanCanny.Computation
open SymbolicFixedTableEntryBits SymbolicFixedTableTaskRouting
open BerkowitzPolynomial.TaskDispatch
open Turing.MultiTapeTM

variable (F : Family) (radix : List Bool → List Bool)
  (high : List Bool → Bool) (leaf : List Bool → List Bool)

def entrySelect (s : List Bool → Bool) (p : List Bool) : Bool := s (pairFst p)

noncomputable def program : SingleCall.Program :=
  ((F.sourceProgram radix (coefficientTask false) (coefficientTask true)).withLeaf
    (entrySelect isLeaf) leaf).withLeaf (entrySelect high) (fun _ => [])

theorem value_eq (answer : List Bool → List Bool)
    (hl : ∀ p, answer (coefficientTask false p) = F.access.leftCoefficient p)
    (hr : ∀ p, answer (coefficientTask true p) = F.access.rightCoefficient p) (p : List Bool) :
    (program F radix high leaf).value answer p =
      if high (pairFst p) then [] else if isLeaf (pairFst p) then leaf p else F.encodedEntry radix p := by
  rw [program, SingleCall.Program.withLeaf_value, SingleCall.Program.withLeaf_value,
    F.sourceProgram_correct radix _ _ answer hl hr]
  rfl

theorem certificates
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction)
    (hB : radix ∈ FP) (hh : (fun c => [high c]) ∈ FP) (hL : SpaceFunction leaf) :
    (program F radix high leaf).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) := by
  have ha := F.access_controls hm hn hc
  let P := F.sourceProgram radix (coefficientTask false) (coefficientTask true)
  have hreq : (fun p => [P.request p]) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (sourceInput_FP radix hB)
      (CannyResultantBits.RecursiveStage.request_FP F.access ha)) (fun _ => rfl)
  have hq0 := (flag_computable (CannyResultantBits.RecursiveStage.selectRight_FP F.access ha)).ite'
    (mem_FP_comp CannyResultantBits.RecursiveStage.rightQuery_FP (coefficientTask_FP true))
    (mem_FP_comp (CannyResultantBits.RecursiveStage.leftQuery_FP F.access ha) (coefficientTask_FP false))
  have hq : P.query ∈ FP := mem_FP_of_eq (mem_FP_comp (sourceInput_FP radix hB) hq0) (fun _ => rfl)
  have hi : SpaceFunction P.immediate := SpaceFunction.ofFP _ (constFn_mem_FP [])
  have hf : SpaceFunction P.finish :=
    (CannyResultantBits.RecursiveStage.finish_space F.access ha).precompose
      (SingleCall.Program.reindexFinish (sourceInput radix))
      (SingleCall.Program.reindexFinish_FP _ (sourceInput_FP radix hB))
  have hleaf := mem_FP_comp pairFst_mem_FP isLeaf_FP
  have hhigh := mem_FP_comp pairFst_mem_FP hh
  have hreq1 : (fun p => [(P.withLeaf (entrySelect isLeaf) leaf).request p]) ∈ FP := by
    refine mem_FP_of_eq ((flag_computable hleaf).ite' (constFn_mem_FP [false]) hreq) ?_
    intro p
    cases hb : isLeaf (pairFst p) <;>
      simp only [SingleCall.Program.withLeaf, entrySelect, hb, Bool.false_eq_true, ite_false, ite_true]
  have hi1 : SpaceFunction (P.withLeaf (entrySelect isLeaf) leaf).immediate :=
    SpaceFunction.branch (entrySelect isLeaf) hleaf hL hi
  exact (P.withLeaf (entrySelect isLeaf) leaf).withLeaf_certificates (entrySelect high) (fun _ => [])
    hhigh hreq1 hq hi1 hf (SpaceFunction.ofFP _ (constFn_mem_FP []))

theorem request_nonleaf (p : List Bool) (h : (program F radix high leaf).request p = true) :
    isLeaf (pairFst p) = false := by
  cases hh : high (pairFst p) <;> cases hl : isLeaf (pairFst p) <;>
    simp only [program, SingleCall.Program.withLeaf, entrySelect, hh, hl,
      Bool.false_eq_true, ite_false, ite_true] at h ⊢

theorem source_levels {G : BerkowitzPolynomial.ModularFamily} (a : BerkowitzPolynomial.ModularAccess G)
    (tasks : List Bool → List Bool → Prop) :
    SourceLevels a (program F radix high leaf).controller (fun _ => 1) tasks level := by
  apply singleCall_source_levels
  intro p hreq _
  have hn := request_nonleaf F radix high leaf p hreq
  change level (origin (if CannyResultantBits.RecursiveStage.selectRight F.access (sourceInput radix p) then
    coefficientTask true (CannyResultantBits.RecursiveStage.rightQuery (sourceInput radix p)) else
    coefficientTask false (CannyResultantBits.RecursiveStage.leftQuery F.access (sourceInput radix p)))) < level (pairFst p)
  cases hb : CannyResultantBits.RecursiveStage.selectRight F.access (sourceInput radix p) with
  | true =>
    simp only [ite_true]
    exact rightTask_decreases radix p hn
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact leftTask_decreases F radix p hn

end LeanCanny.Algebra.SymbolicFixedTableMixedSource
