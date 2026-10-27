/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRankBasis
public import LeanCanny.Encoding.BoundedCriticalSampleFiberRecordGram

/-! # Native selected child-basis Gram entries at actual samples

Both selected row indices are recomputed by the native rank search. The
original moment reader then supplies their inner product. Every child is
charged to the polynomial-space computation; no selected basis is input.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberBasisGram
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice BoundedCriticalSampleFiberRankBasis
open scoped Classical

def leftQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem leftQuery_FP : leftQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair
    (BinaryNatCode.encode (BoundedCriticalSampleFiberRankChoice.index P F (leftQuery q)))
    (BinaryNatCode.encode (BoundedCriticalSampleFiberRankChoice.index P F (rightQuery q))))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem source_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P F) := by
  have E := BoundedCriticalSampleFiberRankChoice.evaluator h A ha
  have L := E.precompose leftQuery leftQuery_FP
  have R := E.precompose rightQuery rightQuery_FP
  have Q := (L.pairOutputs R).withInput
  have H := Q.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def matrix (P : Readers) (F : Family) (c : List Bool) :
    Matrix (Fin (RootCount.count P F c)) (BoundedCriticalSampleFiberRecordSpan.Root P F c) ℚ :=
  selected P F c
noncomputable def gram (P : Readers) (F : Family) (c : List Bool) :
    Matrix (Fin (RootCount.count P F c)) (Fin (RootCount.count P F c)) ℚ :=
  matrix P F c * (matrix P F c).transpose

theorem rank_gram (P : Readers) (F : Family) (c : List Bool) :
    (gram P F c).rank = RootCount.count P F c := by
  rw [gram, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (selected P F c))) = _
  rw [span_selected, finrank_top, Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_coe _

noncomputable def entry (P : Readers) (F : Family) (q : List Bool) : ℤ := BoundedCriticalSampleFiberRecordGram.entry P F (source P F q)

theorem entry_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P F q)) := by
  exact (source_evaluator h A ha).chain (BoundedCriticalSampleFiberRecordGram.evaluator h A ha)

theorem entry_packet (P : Readers) (F : Family) (c : List Bool)
    (i j : Fin (RootCount.count P F c)) :
    (entry P F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) = gram P F c i j := by
  have hs : source P F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair c (pair (BinaryNatCode.encode (selectedIndex P F c i).val)
        (BinaryNatCode.encode (selectedIndex P F c j).val)) := by
    simp only [source, leftQuery, rightQuery, pairFst_pair, pairSnd_pair, selectedIndex, chosen]
  rw [entry, hs, BoundedCriticalSampleFiberRecordGram.entry_packet]
  rfl

theorem entry_bound (P : Readers) (F : Family) (q : List Bool) :
    (entry P F q).natAbs ≤ F.degree (context (pairFst q)) := by
  simpa only [entry, source, pairFst_pair] using BoundedCriticalSampleFiberRecordGram.entry_bound P F (source P F q)

end LeanCanny.Encoding.BoundedCriticalSampleFiberBasisGram
