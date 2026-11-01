/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStageLocal
/-! # Actual relative characteristic powering on one total source

The controller uses the uniform creating source and streams fresh phase23
entries. Semantic replies are required only for its current context, so
skipped invalid births are not additional correctness obligations.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualRelativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalHistoryTask IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess

noncomputable def controller (F : Scripts) (h : Controls F) :=
  IntegralBerkowitzBlockBits.RecursiveStage.controller (characteristic F) (characteristicAccess F h)
    (IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor)

theorem certificates (F : Scripts) (h : Controls F) :
    (controller F h).Certificates (encQ := encBits) (encS := encBits) :=
  IntegralBerkowitzBlockBits.RecursiveStage.certificates (characteristic F) (characteristicAccess F h) _
    (IntegralCriticalFlatMatrixQuery.writer_FP F.toParameters h.task.toAccess .relativeFactor)

abbrev RepliesAt (F : Scripts) (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i j : Fin (IntegralBerkowitzBlockBits.powerDimension (characteristic F) c),
    answer (IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod ((characteristic F).modulus c))

noncomputable def clock (F : Scripts) := ModularRecursiveStage.clock (IntegralBerkowitzBlockBits.powerFamily (characteristic F))
noncomputable def stateBound (F : Scripts) := ModularRecursiveStage.stateBound (IntegralBerkowitzBlockBits.powerFamily (characteristic F))

theorem clock_binary (F : Scripts) (h : Controls F) : BinaryFn (clock F) :=
  IntegralBerkowitzBlockBits.RecursiveStage.clock_binary (characteristic F) (characteristicAccess F h)

theorem stateBound_unary (F : Scripts) (h : Controls F) : UnaryFn (stateBound F) :=
  IntegralBerkowitzBlockBits.RecursiveStage.stateBound_unary (characteristic F) (characteristicAccess F h)

theorem halted_after (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt F answer c) :
    (controller F h).halted (((controller F h).reference answer)^[clock F c] ((controller F h).initial c)) = true :=
  IntegralBerkowitzBlockBits.RecursiveStage.halted_after_local (characteristic F) (characteristicAccess F h)
    (IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor) answer c he

theorem output_when_halted (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt F answer c) (t : ℕ)
    (hh : (controller F h).halted (((controller F h).reference answer)^[t] ((controller F h).initial c)) = true) :
    (controller F h).output (((controller F h).reference answer)^[t] ((controller F h).initial c)) = (characteristic F).value c :=
  IntegralBerkowitzBlockBits.RecursiveStage.output_when_halted_local (characteristic F) (characteristicAccess F h)
    (IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor) answer c he t hh

theorem state_length (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt F answer c) (t : ℕ) :
    (((controller F h).reference answer)^[t] ((controller F h).initial c)).length ≤ stateBound F c :=
  IntegralBerkowitzBlockBits.RecursiveStage.state_length_local (characteristic F) (characteristicAccess F h)
    (IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor) answer c he t

theorem requests_frame (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (he : RepliesAt F answer c) (budget : List Bool → ℕ) (child : List Bool) (hp : isPhase .relativePower c)
    (hc : (controller F h).Requests answer budget c child) :
    RankedHistoryTask.root child = RankedHistoryTask.root c ∧ child.length ≤ wordBudget F.toParameters c ∧
      rank F.toParameters child < rank F.toParameters c := by
  obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
    (characteristic F) (characteristicAccess F h) (IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor)
    answer c he budget child hc
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root F.toParameters .relativeFactor
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  · simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_length F.toParameters .relativeFactor
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  · have H := IntegralCriticalFlatMatrixQuery.writer_lower_rank F.toParameters .relativeFactor
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    simp only [pairFst_pair] at H
    apply H
    change phase c = 24 at hp
    change 23 < phase c
    omega

end LeanCanny.Algebra.IntegralCriticalFlatActualRelativeBits
