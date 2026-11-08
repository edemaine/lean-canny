/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateDecode
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateFilter

/-! # Actual Boolean-cover vertex validity is in native PSPACE

Only original syntax is used: fixed-width/padding guards, the original sign
circuit and the original-equation test at the same decoded joint bank point.
There is no component-membership, frontier or matrix evaluation premise.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM
open scoped Classical

theorem good_iff_filtered (q : List Bool) :
    AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope (source q) (candidate q) ↔
    candidatePacket q∈IntegralMixedAuxiliaryCandidate.filteredLanguage CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope :=
  (IntegralMixedAuxiliaryCandidate.filtered_iff_pointAt_eval CanonicalAuxiliaryCandidateCover.dimension_unary
    CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope (source q) (candidate q)).symm

theorem decider : SpaceDecider language := by
  let Z:= (IntegralMixedAuxiliaryCandidate.filtered_decider CanonicalAuxiliaryCandidateCover.dimension_unary
    CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope).precompose
      candidatePacket candidatePacket_FP
  let S:=FormulaSignSlotCircuit.decider.precompose source source_FP
  have HG:=ComputableInPolySpace.of_tidyPolyTime guard_FP.computable
  have HF:=ComputableInPolySpace.of_tidyPolyTime
    (ComputableTidilyInPolyTime.const (encIn:=encBits) (encMid:=encBool) false)
  apply SpaceDecider.of_computable (HG.ite (S.computable.ite Z.computable HF) HF)
  intro q
  change Valid q↔(if decide (Guard q) then
    (if decide (source q∈FormulaSignSlotCircuit.language) then decide (candidatePacket q∈IntegralMixedAuxiliaryCandidate.filteredLanguage
      CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
      CanonicalAuxiliaryCandidateCover.equation_scope) else false) else false)=true
  simp only [Valid,good_iff_filtered]
  by_cases hg : Guard q <;> by_cases hs : source q∈FormulaSignSlotCircuit.language <;>
    simp only [hg,hs,decide_true,decide_false,ite_true,ite_false,true_and,false_and,
      Bool.false_eq_true,decide_eq_true_eq]

theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE
end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels
