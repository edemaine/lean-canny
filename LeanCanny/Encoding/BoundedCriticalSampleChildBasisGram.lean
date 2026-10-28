/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildRankBasis

/-! # Native entries of the selected regular-child sign Gram matrix

Both selected row indices are recomputed by the native rank search. The
original moment reader then supplies their inner product. Every child is
charged to the polynomial-space computation; no selected basis is input.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildBasisGram
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleChildRankBasis
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

def leftQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem leftQuery_FP : leftQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (P : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair
    (BinaryNatCode.encode (BoundedCriticalSampleChildRankChoice.index P (leftQuery q)))
    (BinaryNatCode.encode (BoundedCriticalSampleChildRankChoice.index P (rightQuery q))))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem source_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (source P) := by
  have E := BoundedCriticalSampleChildRankChoice.evaluator h
  have L := E.precompose leftQuery leftQuery_FP
  have R := E.precompose rightQuery rightQuery_FP
  have Q := (L.pairOutputs R).withInput
  have H := Q.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def matrix (P : Inputs) (c : List Bool) :
    Matrix (Fin (BoundedCriticalSampleChildRegularCount.count P c)) (BoundedCriticalSampleChildRecordSpan.Root P c) ℚ :=
  Matrix.of (selected P c)
noncomputable def gram (P : Inputs) (c : List Bool) :
    Matrix (Fin (BoundedCriticalSampleChildRegularCount.count P c)) (Fin (BoundedCriticalSampleChildRegularCount.count P c)) ℚ :=
  matrix P c * (matrix P c).transpose

theorem rank_gram (P : Inputs) (c : List Bool) :
    (gram P c).rank = BoundedCriticalSampleChildRegularCount.count P c := by
  rw [gram, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (selected P c))) = _
  rw [span_selected, finrank_top, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_coe]
  exact BoundedCriticalSampleChildQueries.roots_card P c

noncomputable def entry (P : Inputs) (q : List Bool) : ℤ := BoundedCriticalSampleChildRecordSpan.entry P (source P q)

theorem entry_evaluator {P : Inputs} (h : P.PolyTime) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P q)) := by
  exact (source_evaluator h).chain (BoundedCriticalSampleChildRecordSpan.entry_evaluator h)

theorem entry_packet (P : Inputs) (c : List Bool)
    (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (entry P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) = gram P c i j := by
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair c (pair (BinaryNatCode.encode (selectedIndex P c i).val)
        (BinaryNatCode.encode (selectedIndex P c j).val)) := by
    simp only [source, leftQuery, rightQuery, pairFst_pair, pairSnd_pair, selectedIndex, chosen]
  rw [entry, hs, BoundedCriticalSampleChildRecordSpan.entry_packet]
  rfl

theorem entry_bounds (P : Inputs) (q : List Bool) :
    -((2 ^ BoundedCriticalSampleChildThom.labelWidth P (pairFst q) : ℕ) : ℤ) ≤ entry P q ∧
      entry P q ≤ ((2 ^ BoundedCriticalSampleChildThom.labelWidth P (pairFst q) : ℕ) : ℤ) := by
  have H := BoundedCriticalSampleChildRecordSpan.entry_bounds P (source P q)
  simpa only [entry, source, pairFst_pair] using H

end LeanCanny.Encoding.BoundedCriticalSampleChildBasisGram
