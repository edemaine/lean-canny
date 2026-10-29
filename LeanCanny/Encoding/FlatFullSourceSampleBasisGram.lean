/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleRankBasis

/-! # Native entries of the selected regular flat sign Gram matrix

Both selected row indices are recomputed by the native rank search. The
original moment reader then supplies their inner product. Every child is
charged to the polynomial-space computation; no selected basis is input.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleBasisGram
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open FlatFullSourceSampleRankBasis
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

def leftQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem leftQuery_FP : leftQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (P : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair
    (BinaryNatCode.encode (FlatFullSourceSampleRankChoice.index P (leftQuery q)))
    (BinaryNatCode.encode (FlatFullSourceSampleRankChoice.index P (rightQuery q))))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem source_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (source P) := by
  have E := FlatFullSourceSampleRankChoice.evaluator h
  have L := E.precompose leftQuery leftQuery_FP
  have R := E.precompose rightQuery rightQuery_FP
  have Q := (L.pairOutputs R).withInput
  have H := Q.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def matrix (P : Inputs) (c : List Bool) :
    Matrix (Fin (FlatFullSourceSampleRegularCount.count P c)) (FlatFullSourceSampleRecordSpan.Root P c) ℚ :=
  Matrix.of (selected P c)
noncomputable def gram (P : Inputs) (c : List Bool) :
    Matrix (Fin (FlatFullSourceSampleRegularCount.count P c)) (Fin (FlatFullSourceSampleRegularCount.count P c)) ℚ :=
  matrix P c * (matrix P c).transpose

theorem rank_gram (P : Inputs) (c : List Bool) :
    (gram P c).rank = FlatFullSourceSampleRegularCount.count P c := by
  rw [gram, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (selected P c))) = _
  rw [span_selected, finrank_top, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_coe]
  exact FlatFullSourceSampleQueries.roots_card P c

noncomputable def entry (P : Inputs) (q : List Bool) : ℤ := FlatFullSourceSampleRecordSpan.entry P (source P q)

theorem entry_evaluator {P : Inputs} (h : P.Access) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P q)) := by
  exact (source_evaluator h).chain (FlatFullSourceSampleRecordSpan.entry_evaluator h)

theorem entry_packet (P : Inputs) (c : List Bool)
    (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (entry P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) = gram P c i j := by
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair c (pair (BinaryNatCode.encode (selectedIndex P c i).val)
        (BinaryNatCode.encode (selectedIndex P c j).val)) := by
    simp only [source, leftQuery, rightQuery, pairFst_pair, pairSnd_pair, selectedIndex, chosen]
  rw [entry, hs, FlatFullSourceSampleRecordSpan.entry_packet]
  rfl

theorem entry_bounds (P : Inputs) (q : List Bool) :
    -((2 ^ FlatFullSourceSampleThom.labelWidth P (pairFst q) : ℕ) : ℤ) ≤ entry P q ∧
      entry P q ≤ ((2 ^ FlatFullSourceSampleThom.labelWidth P (pairFst q) : ℕ) : ℤ) := by
  have H := FlatFullSourceSampleRecordSpan.entry_bounds P (source P q)
  simpa only [entry, source, pairFst_pair] using H

end LeanCanny.Encoding.FlatFullSourceSampleBasisGram
