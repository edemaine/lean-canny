/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactor
public import LeanCanny.Algebra.IntegralReductionActionController

/-! # Flat shifted-action entries request only reduction powers

The low block digit is the old-basis rank. The normal-column guard is
computed from native reduction metadata; nonnormal entries return zero.
A requested power keeps both block indices and the original root intact.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Source := IntegralReductionActionBits.Source

def packet (P : Parameters) (S : Source) (c : List Bool) : List Bool :=
  IntegralBerkowitzBlockBits.outerPacket S.toSource (IntegralCriticalFlatRelativeFactorBits.packet P c)

theorem packet_FP (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S.toSource) : packet P S ∈ FP :=
  mem_FP_comp (IntegralCriticalFlatRelativeFactorBits.packet_FP P a) (IntegralBerkowitzBlockBits.outerPacket_FP S.toSource h)

noncomputable def program (P : Parameters) (S : Source) : SingleCall.Program where
  request c := decide (IntegralReductionActionBits.normalGuard S (packet P S c))
  query := IntegralCriticalFlatEulerBits.next P .reductionPower
  immediate _ := []
  finish := pairSnd

theorem controls (P : Parameters) (a : Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S.toSource) (n : IntegralReductionActionBits.Controls S) :
    (program P S).Controls :=
  ⟨(n.normal.comp (packet_FP P a S h)).flag_mem_FP,
    IntegralCriticalFlatEulerBits.next_FP P a .reductionPower, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem value (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (he : ∀ c, IntegralReductionActionBits.normalGuard S (packet P S c) →
      answer (IntegralCriticalFlatEulerBits.next P .reductionPower c) = (IntegralReductionActionBits.powerFamily S).value (packet P S c))
    (c : List Bool) : (program P S).value answer c = IntegralReductionActionBits.entryProgram S (packet P S c) := by
  by_cases h : IntegralReductionActionBits.normalGuard S (packet P S c)
  · simp only [SingleCall.Program.value, program, h, decide_true, ite_true, pairSnd_pair,
      IntegralReductionActionBits.entryProgram, he c h]
  · simp only [SingleCall.Program.value, program, h, decide_false, Bool.false_eq_true, ite_false,
      IntegralReductionActionBits.entryProgram]

theorem requests_iff (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program P S).controller.Requests answer budget c child ↔
      IntegralReductionActionBits.normalGuard S (packet P S c) ∧ child = IntegralCriticalFlatEulerBits.next P .reductionPower c := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem requests_rank (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) (hp : isPhase .actionEntry c)
    (hc : (program P S).controller.Requests answer budget c child) : rank P child < rank P c := by
  obtain ⟨_, rfl⟩ := (requests_iff P S answer budget c child).mp hc
  apply IntegralCriticalFlatEulerBits.next_lower_rank
  change phase c = 19 at hp
  change 18 < phase c
  omega

theorem requests_tasks (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (r c child : List Bool) (ht : Tasks P r c)
    (hc : (program P S).controller.Requests answer budget c child) : Tasks P r child := by
  obtain ⟨_, rfl⟩ := (requests_iff P S answer budget c child).mp hc
  exact IntegralCriticalFlatEulerBits.next_tasks P .reductionPower r c ht

abbrev Queries := IntegralCriticalScriptGeneratorBits.Queries

noncomputable def source (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  IntegralPurePowerActionBits.reductionSource (IntegralCriticalFlatCoefficientBits.relative F q)

noncomputable def sourceAccess (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalFlatCoefficientBits.Controls F q) :=
  IntegralPurePowerReductionBits.reductionAccess (IntegralCriticalFlatCoefficientBits.relative F q)
    (IntegralCriticalFlatCoefficientBits.relativeAccess F q h)

theorem sourceControls (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalFlatCoefficientBits.Controls F q) : IntegralReductionActionBits.Controls (source F q) :=
  IntegralPurePowerActionBits.controls _ (IntegralCriticalFlatCoefficientBits.relativeAccess F q h).layout
    (IntegralCriticalFlatCoefficientBits.relativeAccess F q h).coordinate
    (IntegralCriticalFlatCoefficientBits.relativeAccess F q h).bound

end LeanCanny.Algebra.IntegralCriticalFlatActionBits
