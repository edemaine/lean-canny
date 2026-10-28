/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntryEncoding
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Native Macaulay entry controls with binary degrees

The monomial box still has polynomially bounded arity and block width.
Degrees and the Macaulay level are computed in binary. The original entry
program and its correctness theorem are unchanged; no unary degree writer
or enumeration of the exponentially large box is required.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayBits
open LeanCanny.Encoding LeanCanny.Computation

structure Layout.BinaryPolyTime (L : Layout) : Prop where
  arity : UnaryFn L.arity
  width : UnaryFn L.width
  degree : BinaryFn (fun q => L.degree (pairFst q) (pairSnd q).length)

theorem Layout.level_binary {L : Layout} (h : L.BinaryPolyTime) : BinaryFn L.level :=
  ((BinaryFn.sum h.arity (h.degree.sub (BinaryFn.const 1))).add (BinaryFn.const 1)).of_eq
    (fun c => by simp only [Layout.level, pairFst_pair, pairSnd_pair, List.length_replicate])

theorem rowRead_binary_mem_FP {L : Layout} (h : L.BinaryPolyTime) : rowRead L ∈ FP :=
  FixedWidthQuery.read_mem_FP (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP) row_mem_FP

theorem colRead_binary_mem_FP {L : Layout} (h : L.BinaryPolyTime) : colRead L ∈ FP :=
  FixedWidthQuery.read_mem_FP (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP) col_mem_FP

theorem degreeLoop_binary {L : Layout} (h : L.BinaryPolyTime) : BinaryFn (degreeLoop L) := by
  refine BinaryFn.of_eq (h.degree.comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP context_mem_FP) pairSnd_mem_FP)) ?_
  intro q
  simp only [degreeLoop, Function.comp_apply, pairFst_pair, pairSnd_pair]

theorem rowTotal_binary {L : Layout} (h : L.BinaryPolyTime) : BinaryFn (rowTotal L) := by
  have hr := BinaryFn.fromBits (mem_FP_comp loopQuery_mem_FP (rowRead_binary_mem_FP h))
  have hl : BinaryFn (fun p => L.level (context p)) := (Layout.level_binary h).comp context_mem_FP
  have hc : BinaryFn (fun q => L.level (context (pairFst q)) + 1) :=
    (hl.add (BinaryFn.const 1)).comp pairFst_mem_FP
  have ht := (BinaryFn.ite (hr.le hc) hr hc).of_eq (fun _ => (min_def _ _).symm)
  refine (BinaryFn.sum (h.arity.comp context_mem_FP) ht).of_eq (fun p => ?_)
  simp only [loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    rowRead, FixedWidthQuery.read_packet, fromBits_encode, rowTotal, rowAt]

theorem pivot_binary_unary {L : Layout} (h : L.BinaryPolyTime) : UnaryFn (pivot L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (rowRead_binary_mem_FP h)
  have ht := BinaryNat.le_fppred (degreeLoop_binary h).bits_mem_FP hr
  refine ((h.arity.comp context_mem_FP).find ht).of_eq (fun p => ?_)
  simp only [pivot, degreeLoop, loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, rowRead, FixedWidthQuery.read_packet, fromBits_encode, rowAt]
  rfl

theorem remainderRead_binary_mem_FP {L : Layout} (h : L.BinaryPolyTime) : remainderRead L ∈ FP := by
  have hp := pivot_binary_unary h
  have he : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = pivot L (pairFst q)) :=
    by simpa only [Nat.fromBitsLE_bits] using
      BinaryNat.eq_fppred pairSnd_mem_FP (bits_mem_FP (hp.comp pairFst_mem_FP))
  have hd : BinaryFn (fun q => L.degree (context (pairFst q)) (pivot L (pairFst q))) := by
    refine BinaryFn.of_eq (h.degree.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP context_mem_FP)
      (hp.comp pairFst_mem_FP).mem_FP)) ?_
    intro q
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  exact mem_FP_comp (mem_FP_pair (rowRead_binary_mem_FP h)
    (he.ite_mem_FP hd.bits_mem_FP (constFn_mem_FP []))) BinaryNat.sub_mem_FP

theorem differenceRead_binary_mem_FP {L : Layout} (h : L.BinaryPolyTime) : differenceRead L ∈ FP :=
  mem_FP_comp (mem_FP_pair (colRead_binary_mem_FP h) (remainderRead_binary_mem_FP h)) BinaryNat.sub_mem_FP

theorem differenceWord_binary_mem_FP {L : Layout} (h : L.BinaryPolyTime) : differenceWord L ∈ FP :=
  FixedWidthNatVector.encode_of_coordinate (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP)
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary
    (FixedWidthNatVector.coordinate_of_reader (differenceRead_binary_mem_FP h) (differenceRead_packet L))

theorem admissible_binary_fppred {L : Layout} (h : L.BinaryPolyTime) : FPPred (admissible L) := by
  have hf := (BinaryNat.le_fppred
    (mem_FP_comp loopQuery_mem_FP (remainderRead_binary_mem_FP h))
    (mem_FP_comp loopQuery_mem_FP (colRead_binary_mem_FP h))).forall_lt (h.arity.comp context_mem_FP)
  apply hf.of_iff
  intro p
  simp only [loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    remainderRead_packet, colRead, FixedWidthQuery.read_packet, fromBits_encode, admissible, colAt]

theorem active_binary_fppred {L : Layout} (h : L.BinaryPolyTime) : FPPred (active L) :=
  (rowTotal_binary h).eq ((Layout.level_binary h).comp context_mem_FP)

theorem sourceQuery_binary_mem_FP {L : Layout} (h : L.BinaryPolyTime) : sourceQuery L ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (bits_mem_FP (pivot_binary_unary h))
    (mem_FP_comp (differenceWord_binary_mem_FP h) BinaryNat.normalize_mem_FP))

theorem entryWithIdentityBinaryEvaluator {L : Layout} (h : L.BinaryPolyTime)
    {coefficient identity : List Bool → List Bool} (E : SpaceFunction coefficient) (hI : identity ∈ FP) :
    SpaceFunction (entryWithIdentity L coefficient identity) := by
  have EC := E.precompose (sourceQuery L) (sourceQuery_binary_mem_FP h)
  have EA := SpaceFunction.branch (fun p => decide (admissible L p)) (admissible_binary_fppred h).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have ER := SpaceFunction.branch (fun p => decide (active L p)) (active_binary_fppred h).flag_mem_FP
    EA (SpaceFunction.ofFP _ hI)
  exact ER.congr (funext fun p => by simp only [entryWithIdentity, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.MacaulayBits
