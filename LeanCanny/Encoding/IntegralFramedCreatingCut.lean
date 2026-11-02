/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNormalization
/-! # Native actual-cut classification from original instruction headers

A virtual fallback selection is not evidence of a creating cut. This
guard reads the literal original instruction, distinguishing integer and
physical-critical births before applying relative cut-validity tests.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCreatingCut
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedFullHistoryScript

def IsCut {n B : ℕ} {P : IntegralMixedHistory.SpatialSource n} : Command P B→Prop
  | .cut .. => True
  | _ => False

theorem isCut_iff_context {n B : ℕ} {P : IntegralMixedHistory.SpatialSource n} (c : Command P B) :
    IsCut c ↔ 2≤c.context := by
  cases c with
  | integer => simp only [IsCut,Command.context]; decide
  | critical => simp only [IsCut,Command.context]; decide
  | cut r k => cases k <;> simp only [IsCut,Command.context] <;> decide

noncomputable def ParentCut (P : Parameters) (D : Plan P) (c : List Bool) : Prop :=
  IsCut (instruction P D (IntegralMixedVirtualTaskBits.saved P c)).command

theorem commandContext_binary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) :
    BinaryFn (fun key=>(instruction P D key).command.context) := by
  have HS:=IntegralMixedHeaderTablesBits.producer_readers P a h0.tables h0.native
  exact HS.context.of_eq (fun key=>(congrArg IntegralMixedCommandHeaderBits.Header.context
    (IntegralMixedFramedHeaderBits.producer_eq P D H h0.tables h0.represents key)).trans
      (IntegralMixedCommandHeaderBits.command_context _))

theorem parentCut_FP (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) :
    FPPred (ParentCut P D) := by
  have HC : BinaryFn (fun c=>(instruction P D (IntegralMixedVirtualTaskBits.saved P c)).command.context) :=
    (commandContext_binary P a D H h0).comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact ((BinaryFn.const 2).le HC).of_iff (fun c=>(isCut_iff_context _).symm)

end LeanCanny.Encoding.IntegralFramedCreatingCut
