/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
/-! # The joint header retains both original Boolean-cover tags literally -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryJointHeader
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open scoped Classical

def packet (original left right : List Bool) := pair original (pair left right)
noncomputable def header (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :=
  packet (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i)
    (CanonicalAuxiliaryCandidateCover.encode d j)

theorem labelQuery_false (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotRadialJointLayout.labelQuery false (header d i j) =
      pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i) := by
  simp only [FormulaSignSlotRadialJointLayout.labelQuery, FormulaSignSlotRadialJointLayout.original,
    FormulaSignSlotRadialJointLayout.label, header, packet, pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false]

theorem labelQuery_true (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotRadialJointLayout.labelQuery true (header d i j) =
      pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d j) := by
  simp only [FormulaSignSlotRadialJointLayout.labelQuery, FormulaSignSlotRadialJointLayout.original,
    FormulaSignSlotRadialJointLayout.label, header, packet, pairFst_pair, pairSnd_pair, ite_true]

theorem source_false (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotRadialJointLayout.source false (header d i j) = CanonicalSignRefinement.source d i.1 := by
  rw [FormulaSignSlotRadialJointLayout.source, labelQuery_false]
  exact CanonicalAuxiliaryCandidateLabels.source_encode d i

theorem source_true (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotRadialJointLayout.source true (header d i j) = CanonicalSignRefinement.source d j.1 := by
  rw [FormulaSignSlotRadialJointLayout.source, labelQuery_true]
  exact CanonicalAuxiliaryCandidateLabels.source_encode d j

theorem candidate_false (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    CanonicalAuxiliaryCandidateLabels.candidate
      (FormulaSignSlotRadialJointLayout.labelQuery false (header d i j)) = i.2.val := by
  rw [labelQuery_false]
  exact CanonicalAuxiliaryCandidateLabels.candidate_encode d i

theorem candidate_true (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    CanonicalAuxiliaryCandidateLabels.candidate
      (FormulaSignSlotRadialJointLayout.labelQuery true (header d i j)) = j.2.val := by
  rw [labelQuery_true]
  exact CanonicalAuxiliaryCandidateLabels.candidate_encode d j

end LeanCanny.Connectivity.CanonicalAuxiliaryJointHeader
