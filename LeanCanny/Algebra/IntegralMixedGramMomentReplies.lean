/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramMomentTypedRoutes
public import LeanCanny.Algebra.MatrixMomentEntryTypedReplies
/-! # Every selected phase-twenty-one child has its actual action value -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
attribute [local irreducible] IntegralMixedGramCharacteristicSource.source characteristicAccess

theorem action_replies21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (c : List Bool) (hv : IntegralMixedVirtualCaps.valid P c) :
    IntegralCriticalFlatMomentEntryBits.RepliesAt P a (characteristic P F)
      (characteristicAccess P a F h) (IntegralMixedGramMatrixModel.actionValue P F) c := by
  let r : Fin (IntegralMixedGramMomentMatrix.size P F c) :=
    ⟨get P .row c % IntegralMixedGramMomentMatrix.size P F c, Nat.mod_lt _ (moment_size_pos P F c)⟩
  let t : Fin (IntegralMixedGramMomentMatrix.size P F c) :=
    ⟨get P .col c % IntegralMixedGramMomentMatrix.size P F c, Nat.mod_lt _ (moment_size_pos P F c)⟩
  have HI : IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) c =
      pair (IntegralBlockMomentBits.context c r.modNat.val t.modNat.val)
        (pair (BinaryNatCode.encode r.divNat.val) (BinaryNatCode.encode t.divNat.val)) :=
    IntegralBlockMomentBits.outer_packet (moment P F) c r t
  have HD : (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F)
      (characteristicAccess P a F h)).dimension (IntegralBlockMomentBits.context c r.modNat.val t.modNat.val) =
      BinaryNatCode.encode ((moment P F).dimension c) := by
    simp only [IntegralCriticalFlatMomentEntryBits.bits, IntegralBlockMomentBits.bitsAccess,
      IntegralBlockMomentBits.context, pairFst_pair]
  exact MatrixMoment.EntryBits.repliesAt_of_typed _ _ _ _ _ _ c
    (IntegralBlockMomentBits.context c r.modNat.val t.modNat.val) ((moment P F).dimension c) r.divNat t.divNat HD HI
    (fun i => rowTask_value P a F h g c hv i r.modNat t.modNat)
    (fun i => columnTask_value P a F h g c hv i r.modNat t.modNat)
    (fun i j => matrixTask_value P a F h g c hv i j r.modNat t.modNat)

theorem action_value21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (c : List Bool) (hv : IntegralMixedVirtualCaps.valid P c) :
    (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
      (characteristicAccess P a F h)).value (IntegralMixedGramMatrixModel.actionValue P F) c = momentEntry P F c :=
  value21 P a F h _ c (action_replies21 P a F h g c hv)

theorem action_value21_local (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (c : List Bool) (hv : IntegralMixedVirtualCaps.valid P c)
    (ha : (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
      (characteristicAccess P a F h)).request c = true →
      answer ((IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
        (characteristicAccess P a F h)).query c) =
      IntegralMixedGramMatrixModel.actionValue P F ((IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
        (characteristicAccess P a F h)).query c)) :
    (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
      (characteristicAccess P a F h)).value answer c = momentEntry P F c := by
  have HE : (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
      (characteristicAccess P a F h)).value answer c =
      (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F)
        (characteristicAccess P a F h)).value (IntegralMixedGramMatrixModel.actionValue P F) c := by
    unfold SingleCall.Program.value
    split_ifs with hr
    · rw [ha hr]
    · rfl
  exact HE.trans (action_value21 P a F h g c hv)

end LeanCanny.Algebra.IntegralMixedGramUpperBits
