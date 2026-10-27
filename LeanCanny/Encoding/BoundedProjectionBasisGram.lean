/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRankBasis

/-! # Native entries of the selected projection-sign Gram matrix

Both selected row indices are recomputed by the native rank search. The
original moment reader then supplies their inner product. Every child is
charged to the polynomial-space computation; no selected basis is input.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionBasisGram
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionRankBasis
open scoped Classical

def leftQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem leftQuery_FP : leftQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (P : Readers) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair
    (BinaryNatCode.encode (BoundedProjectionRankChoice.index P (leftQuery q)))
    (BinaryNatCode.encode (BoundedProjectionRankChoice.index P (rightQuery q))))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem source_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P) := by
  have E := BoundedProjectionRankChoice.evaluator h ha
  have L := E.precompose leftQuery leftQuery_FP
  have R := E.precompose rightQuery rightQuery_FP
  have Q := (L.pairOutputs R).withInput
  have H := Q.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def matrix (P : Readers) (c : List Bool) :
    Matrix (Fin (BoundedProjectionRootCount.count P c)) (BoundedProjectionRecordSpan.Root P c) ℚ :=
  selected P c
noncomputable def gram (P : Readers) (c : List Bool) :
    Matrix (Fin (BoundedProjectionRootCount.count P c)) (Fin (BoundedProjectionRootCount.count P c)) ℚ :=
  matrix P c * (matrix P c).transpose

theorem rank_gram (P : Readers) (c : List Bool) :
    (gram P c).rank = BoundedProjectionRootCount.count P c := by
  rw [gram, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (selected P c))) = _
  rw [span_selected, finrank_top, Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_coe _

noncomputable def entry (P : Readers) (q : List Bool) : ℤ := BoundedProjectionRecordSpan.entry P (source P q)

theorem entry_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P q)) := by
  exact (source_evaluator h ha).chain (BoundedProjectionRecordSpan.entry_evaluator h ha)

theorem entry_packet (P : Readers) (c : List Bool)
    (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (entry P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) = gram P c i j := by
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair c (pair (BinaryNatCode.encode (selectedIndex P c i).val)
        (BinaryNatCode.encode (selectedIndex P c j).val)) := by
    simp only [source, leftQuery, rightQuery, pairFst_pair, pairSnd_pair, selectedIndex, chosen]
  rw [entry, hs, BoundedProjectionRecordSpan.entry_packet]
  rfl

theorem entry_bounds (P : Readers) (q : List Bool) :
    -((2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) : ℕ) : ℤ) ≤ entry P q ∧
      entry P q ≤ ((2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) : ℕ) : ℤ) := by
  have H := BoundedProjectionRecordSpan.entry_bounds P (source P q)
  simpa only [entry, source, pairFst_pair] using H

end LeanCanny.Encoding.BoundedProjectionBasisGram
