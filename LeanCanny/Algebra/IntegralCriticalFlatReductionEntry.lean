/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatAction
public import LeanCanny.Algebra.IntegralCriticalFlatLowerQuery
public import LeanCanny.Algebra.IntegralPurePowerReductionController
public import LeanCanny.Algebra.PurePowerReductionControllerLocal
/-! # Flat reduction entries from one guarded actual lower coefficient

The native reduction selector keeps the original transpose convention.
Its nonlocal branch emits a phase16 task with the actual old-basis ranks,
lower-row index, and spatial exponent. Correctness requires only that
single guarded reply, rather than arbitrary oversized legacy packets.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatReductionEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalFlatLowerQuery.writer
abbrev Source := IntegralPurePowerActionBits.Source

noncomputable def packet (P : Parameters) (S : Source) : List Bool → List Bool :=
  IntegralCriticalFlatActionBits.packet P (IntegralPurePowerActionBits.reductionSource S)

def lowerInput (S : Source) (p : List Bool) : List Bool :=
  IntegralPurePowerReductionBits.lowQuery (PurePowerReductionBits.sourceQuery (IntegralPurePowerReductionBits.layout S)
    (IntegralPurePowerReductionBits.writer S p))

theorem lowerInput_parent (S : Source) (p : List Bool) :
    IntegralBerkowitzBlockBits.original (lowerInput S p) = IntegralBerkowitzBlockBits.original p := by
  simp only [lowerInput, IntegralPurePowerReductionBits.lowQuery, PurePowerReductionBits.sourceQuery,
    IntegralPurePowerReductionBits.writer, IntegralBerkowitzBlockBits.original, pairFst_pair]

theorem packet_parent (P : Parameters) (S : Source) (c : List Bool) :
    IntegralBerkowitzBlockBits.original (packet P S c) = c :=
  IntegralCriticalFlatRelativeFactorBits.outer_original P (IntegralPurePowerActionBits.reductionSource S).toSource c

noncomputable def program (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S) : SingleCall.Program :=
  (IntegralPurePowerReductionBits.program S a (IntegralCriticalFlatLowerQuery.writer P)).requery (packet P S)

theorem controls (P : Parameters) (m : Access P) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (ha : a.leading ∈ FP) : (program P S a).Controls :=
  SingleCall.Program.requery_controls _
    (IntegralPurePowerReductionBits.program_controls S a ha _ (IntegralCriticalFlatLowerQuery.writer_FP P m))
    (packet P S) (IntegralCriticalFlatActionBits.packet_FP P m _ (IntegralPurePowerReductionBits.reductionAccess S a))

theorem value (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool)
    (he : PurePowerReductionBits.request (IntegralPurePowerReductionBits.layout S)
      (fun z => S.layout.bound (pairFst z)) (IntegralPurePowerReductionBits.writer S (packet P S c)) →
      answer (IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S c))) = a.low (lowerInput S (packet P S c))) :
    (program P S a).value answer c = IntegralPurePowerReductionBits.entryProgram S a (packet P S c) := by
  rw [program, SingleCall.Program.requery_value]
  exact PurePowerReductionBits.program_value_at (IntegralPurePowerReductionBits.layout S)
    (fun z => S.layout.bound (pairFst z)) (IntegralPurePowerReductionBits.constant a)
    (a.low ∘ IntegralPurePowerReductionBits.lowQuery) (IntegralPurePowerReductionBits.writer S)
    (IntegralCriticalFlatLowerQuery.writer P ∘ IntegralPurePowerReductionBits.lowQuery) answer (packet P S c) he

theorem requests_child (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hc : (program P S a).controller.Requests answer budget c child) :
    child = IntegralCriticalFlatLowerQuery.writer P (lowerInput S (packet P S c)) := by
  have H := (SingleCall.Program.requery_requests_iff
    (IntegralPurePowerReductionBits.program S a (IntegralCriticalFlatLowerQuery.writer P))
    (packet P S) answer budget c child).mp hc
  exact H.2

theorem requests_rank (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : isPhase .reductionEntry c) (hc : (program P S a).controller.Requests answer budget c child) :
    rank P child < rank P c := by
  rw [requests_child P S a answer budget c child hc]
  have H := IntegralCriticalFlatLowerQuery.writer_lower_rank P (lowerInput S (packet P S c))
  rw [lowerInput_parent, packet_parent] at H
  apply H
  change phase c = 17 at hp
  omega

theorem requests_tasks (P : Parameters) (S : Source) (a : IntegralPurePowerReductionBits.Access S)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (r c child : List Bool) (ht : Tasks P r c)
    (hc : (program P S a).controller.Requests answer budget c child) : Tasks P r child := by
  rw [requests_child P S a answer budget c child hc]
  apply IntegralCriticalFlatLowerQuery.writer_tasks
  simpa only [lowerInput_parent, packet_parent] using ht

end LeanCanny.Algebra.IntegralCriticalFlatReductionEntryBits
