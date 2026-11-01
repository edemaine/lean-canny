/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PurePowerReductionChargedController
public import LeanCanny.Algebra.IntegralPurePowerReductionController
/-! # Charged leading requests with both retained basis indices

The native postprocessor masks off-diagonal old-basis entries. The scalar
itself is a recursive reply, so no FP leading evaluator is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerReductionBits.Charged
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralPurePowerActionBits (Source)
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
set_option backward.isDefEq.respectTransparency false

def scalarFinish (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (basisRowCode (pairFst z)) = Nat.fromBitsLE (basisColCode (pairFst z)) then pairSnd z else []

theorem scalarFinish_FP : scalarFinish ∈ FP := by
  have HG := ((BinaryFn.fromBits IntegralBerkowitzBlockBits.basisRowCode_FP).eq
    (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisColCode_FP)).comp pairFst_mem_FP
  exact HG.ite_mem_FP pairSnd_mem_FP (constFn_mem_FP [])

noncomputable def program (S : Source) (leadingTask lowerTask : List Bool → List Bool) : SingleCall.Program :=
  PurePowerReductionBits.Charged.program (layout S) (fun z => S.layout.bound (pairFst z))
    (writer S) (leadingTask ∘ original) (lowerTask ∘ lowQuery) scalarFinish

theorem controls (S : Source) (a : Access S) (leadingTask lowerTask : List Bool → List Bool)
    (hl : leadingTask ∈ FP) (he : lowerTask ∈ FP) : (program S leadingTask lowerTask).Controls :=
  PurePowerReductionBits.Charged.controls (layout S) (layout_polyTime S a) _ (a.bound.comp pairFst_mem_FP)
    _ _ _ _ (writer_FP S a) (mem_FP_comp IntegralBerkowitzBlockBits.original_FP hl)
      (mem_FP_comp lowQuery_FP he) scalarFinish_FP

theorem value_at (S : Source) (a : Access S) (leadingTask lowerTask answer : List Bool → List Bool)
    (p : List Bool)
    (hl : PurePowerReductionBits.Charged.scalar (layout S) (writer S p) →
      answer (leadingTask (original p)) = a.leading (original p))
    (he : PurePowerReductionBits.request (layout S) (fun z => S.layout.bound (pairFst z)) (writer S p) →
      answer (lowerTask (lowQuery (PurePowerReductionBits.sourceQuery (layout S) (writer S p)))) =
        a.low (lowQuery (PurePowerReductionBits.sourceQuery (layout S) (writer S p)))) :
    (program S leadingTask lowerTask).value answer p = entryProgram S a p := by
  apply PurePowerReductionBits.Charged.value_at
  · intro hs
    have HL := hl hs
    simp only [scalarFinish, constant, writer, original, basisRowCode, basisColCode,
      pairFst_pair, pairSnd_pair, Function.comp_apply] at HL ⊢
    rw [HL]
  · exact he

theorem requests_iff (S : Source) (leadingTask lowerTask answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (program S leadingTask lowerTask).controller.Requests answer budget p child ↔
      (PurePowerReductionBits.Charged.scalar (layout S) (writer S p) ∧ child = leadingTask (original p)) ∨
      (PurePowerReductionBits.request (layout S) (fun z => S.layout.bound (pairFst z)) (writer S p) ∧
        child = lowerTask (lowQuery (PurePowerReductionBits.sourceQuery (layout S) (writer S p)))) := by
  rw [program, PurePowerReductionBits.Charged.requests_iff]
  simp only [Function.comp_apply, writer, original, pairFst_pair]

end LeanCanny.Algebra.IntegralPurePowerReductionBits.Charged
