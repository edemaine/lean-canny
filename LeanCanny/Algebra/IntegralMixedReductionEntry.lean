/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralPurePowerReductionChargedController
public import LeanCanny.Algebra.IntegralCriticalFlatReductionEntry
public import LeanCanny.Algebra.IntegralMixedScalarQueries
/-! # Flat reduction entries with charged mixed-history scalar requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedReductionEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatReductionEntryBits (Source packet lowerInput packet_parent lowerInput_parent)
set_option backward.isDefEq.respectTransparency false

noncomputable def program (P : Parameters) (S : Source) : SingleCall.Program :=
  (IntegralPurePowerReductionBits.Charged.program S (IntegralMixedScalarQueryBits.commonLeading P)
    (IntegralCriticalFlatLowerQuery.writer P)).requery (packet P S)

theorem controls (P : Parameters) (m : Access P) (S : Source) (a : IntegralPurePowerReductionBits.Access S) :
    (program P S).Controls :=
  SingleCall.Program.requery_controls _
    (IntegralPurePowerReductionBits.Charged.controls S a _ _
      (IntegralMixedScalarQueryBits.scalarQuery_FP P m .monomialFactor)
      (IntegralCriticalFlatLowerQuery.writer_FP P m))
    (packet P S) (IntegralCriticalFlatActionBits.packet_FP P m _ (IntegralPurePowerReductionBits.reductionAccess S a))

theorem value_at (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (q : List Bool)
    (hl : PurePowerReductionBits.Charged.scalar (IntegralPurePowerReductionBits.layout S)
        (IntegralPurePowerReductionBits.writer S (packet P S q)) →
      answer (IntegralMixedScalarQueryBits.commonLeading P q) = a.leading q)
    (he : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout S)
        (fun z => S.layout.bound (pairFst z)) (IntegralPurePowerReductionBits.writer S (packet P S q)) →
      answer (IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S q))) =
        a.low (lowerInput S (packet P S q))) :
    (program P S).value answer q = IntegralPurePowerReductionBits.entryProgram S a (packet P S q) := by
  rw [program, SingleCall.Program.requery_value]
  apply IntegralPurePowerReductionBits.Charged.value_at
  · simpa only [packet_parent] using hl
  · exact he

theorem requests_cases (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool)
    (hc : (program P S).controller.Requests answer budget q child) :
    child = IntegralMixedScalarQueryBits.commonLeading P q ∨
      child = IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S q)) := by
  let C := IntegralPurePowerReductionBits.Charged.program S (IntegralMixedScalarQueryBits.commonLeading P)
    (IntegralCriticalFlatLowerQuery.writer P)
  have H := (SingleCall.Program.requery_requests_iff C (packet P S) answer budget q child).mp hc
  have H0 := (C.requests_iff answer budget (packet P S q) child).mpr H
  rcases (IntegralPurePowerReductionBits.Charged.requests_iff S _ _ answer budget (packet P S q) child).mp H0 with h | h
  · exact Or.inl (h.2.trans (congrArg (IntegralMixedScalarQueryBits.commonLeading P) (packet_parent P S q)))
  · exact Or.inr h.2

attribute [local irreducible] program IntegralCriticalFlatReductionEntryBits.packet
  IntegralCriticalFlatReductionEntryBits.lowerInput IntegralCriticalFlatLowerQuery.writer

theorem lower_frame (P : Parameters) (S : Source) (q : List Bool) (hp : isPhase .reductionEntry q) :
    IntegralMixedRoutineTaskBits.Frame P q
      (IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S q))) := by
  let p := lowerInput S (packet P S q)
  have HO : IntegralBerkowitzBlockBits.original p = q := (lowerInput_parent S _).trans (packet_parent P S q)
  refine ⟨?_, ?_, ?_⟩
  · exact (IntegralCriticalFlatLowerQuery.writer_root P p).trans (congrArg RankedHistoryTask.root HO)
  · exact (IntegralCriticalFlatLowerQuery.writer_length P p).trans_eq (congrArg (wordBudget P) HO)
  · apply IntegralMixedRoutineTaskBits.lower_phase
    · exact (IntegralCriticalFlatLowerQuery.writer_birth P p).trans (congrArg (birth P) HO)
    · unfold IntegralMixedRoutineTaskBits.routine
      rw [IntegralCriticalFlatLowerQuery.writer_get]
      simp only [reduceCtorEq, ite_false]
      change min (get P .slot14 (IntegralBerkowitzBlockBits.original p)) 6 = min (get P .slot14 q) 6
      rw [HO]
    · rw [IntegralCriticalFlatLowerQuery.writer_phase]
      change phase q = 17 at hp
      omega

theorem requests_frame (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool) (hp : isPhase .reductionEntry q)
    (hr : 0 < IntegralMixedRoutineTaskBits.routine P q)
    (hc : (program P S).controller.Requests answer budget q child) :
    IntegralMixedRoutineTaskBits.Frame P q child := by
  rcases requests_cases P S answer budget q child hc with rfl | rfl
  · exact IntegralMixedScalarQueryBits.scalar_frame P .monomialFactor q hr
  · exact lower_frame P S q hp

end LeanCanny.Algebra.IntegralMixedReductionEntryBits
