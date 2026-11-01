/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatAction
public import LeanCanny.Algebra.IntegralBlockPowerRequery

/-! # Flat reduction powering for actual shifted-action entries

The native action packet selects both old-basis ranks and shifted spatial
indices. Its integer matrix is streamed through fresh phase17 tasks.
The controller has no reduction-entry evaluator premise.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatReductionPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

abbrev Source := IntegralReductionActionBits.Source

noncomputable def family (P : Parameters) (S : Source) : IntegralBlockPowerBits.Family :=
  (IntegralReductionActionBits.powerFamily S).requery (IntegralCriticalFlatActionBits.packet P S)

noncomputable def access (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S) :
    IntegralBlockPowerBits.Access (family P S) :=
  IntegralBlockPowerBits.Access.requery (IntegralReductionActionBits.powerFamily S)
    (IntegralReductionActionBits.powerAccess S h n) (IntegralCriticalFlatActionBits.packet P S)
    (IntegralCriticalFlatActionBits.packet_FP P a S h)

noncomputable def controller (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S) :=
  IntegralBlockPowerBits.RecursiveStage.controller (family P S) (access P a S h n)
    (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry)

theorem certificates (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S) :
    (controller P a S h n).Certificates (encQ := encBits) (encS := encBits) :=
  IntegralBlockPowerBits.RecursiveStage.certificates (family P S) (access P a S h n) _
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .reductionEntry)

abbrev Replies (P : Parameters) (S : Source) (answer : List Bool → List Bool) : Prop :=
  ∀ c (i j : Fin ((family P S).dimension c * (family P S).rank c)),
    answer (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((family P S).powerMatrix c i j : ℤ) : ZMod ((family P S).modulus c))

noncomputable def clock (P : Parameters) (S : Source) := ModularRecursiveStage.clock (IntegralBlockPowerBits.powerFamily (family P S))
noncomputable def stateBound (P : Parameters) (S : Source) := ModularRecursiveStage.stateBound (IntegralBlockPowerBits.powerFamily (family P S))

theorem clock_binary (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S) : BinaryFn (clock P S) :=
  IntegralBlockPowerBits.RecursiveStage.clock_binary (family P S) (access P a S h n)

theorem stateBound_unary (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S) : UnaryFn (stateBound P S) :=
  IntegralBlockPowerBits.RecursiveStage.stateBound_unary (family P S) (access P a S h n)

theorem halted_after (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (he : Replies P S answer) (c : List Bool) :
    (controller P a S h n).halted (((controller P a S h n).reference answer)^[clock P S c]
      ((controller P a S h n).initial c)) = true :=
  IntegralBlockPowerBits.RecursiveStage.halted_after (family P S) (access P a S h n) _ answer he c

theorem output_when_halted (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (he : Replies P S answer) (c : List Bool) (t : ℕ)
    (hh : (controller P a S h n).halted (((controller P a S h n).reference answer)^[t]
      ((controller P a S h n).initial c)) = true) :
    (controller P a S h n).output (((controller P a S h n).reference answer)^[t]
      ((controller P a S h n).initial c)) =
      (IntegralReductionActionBits.powerFamily S).value (IntegralCriticalFlatActionBits.packet P S c) :=
  (IntegralBlockPowerBits.RecursiveStage.output_when_halted (family P S) (access P a S h n) _ answer he c t hh).trans
    (IntegralBlockPowerBits.Family.requery_value _ _ c)

theorem state_length (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (he : Replies P S answer) (c : List Bool) (t : ℕ) :
    (((controller P a S h n).reference answer)^[t] ((controller P a S h n).initial c)).length ≤ stateBound P S c :=
  IntegralBlockPowerBits.RecursiveStage.state_length (family P S) (access P a S h n) _ answer he c t

theorem requests_rank (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (he : Replies P S answer) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : isPhase .reductionPower c) (hc : (controller P a S h n).Requests answer budget c child) :
    rank P child < rank P c := by
  obtain ⟨i, j, rfl⟩ := IntegralBlockPowerBits.RecursiveStage.requests_in_bounds
    (family P S) (access P a S h n) (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry) answer he budget c child hc
  have H := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .reductionEntry
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  simp only [pairFst_pair] at H
  apply H
  change phase c = 18 at hp
  change 17 < phase c
  omega

theorem requests_tasks (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S)
    (answer : List Bool → List Bool) (he : Replies P S answer) (budget : List Bool → ℕ) (r c child : List Bool)
    (ht : Tasks P r c) (hc : (controller P a S h n).Requests answer budget c child) : Tasks P r child := by
  obtain ⟨i, j, rfl⟩ := IntegralBlockPowerBits.RecursiveStage.requests_in_bounds
    (family P S) (access P a S h n) (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry) answer he budget c child hc
  apply IntegralCriticalFlatMatrixQuery.writer_tasks
  simpa only [pairFst_pair] using ht

end LeanCanny.Algebra.IntegralCriticalFlatReductionPowerBits
