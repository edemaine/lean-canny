/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingFields
/-! # Native raw leading scalar of the total Euler source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false

theorem euler_leading (F : Scripts) (q : List Bool) : (euler F).leading q =
    if valid F q then IntegralCriticalScriptFP.leading (IntegralCriticalFlatClearedHeightBits.metadata F) q
      (IntegralCriticalHistoryTask.birth F.toParameters q) else 1 := by
  change ((atFamily F q).data []).leading = _
  by_cases h : valid F q
  · rw [atFamily_valid F q h, ite_eq_left h]
    unfold IntegralCriticalScriptFP.leading
    rw [commandAt_creating F q h]
    rfl
  · rw [atFamily_invalid F q h, ite_eq_right h]
    rfl

attribute [local irreducible] atFamily euler

theorem leading_FP (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) :
    (fun q => residueBits ((euler F).leading q : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))) ∈ FP := by
  have HR := mem_FP_comp (IntegralCriticalFlatClearedHeightBits.cursorPacket_FP F a) n.leading
  have HE : (fun q => residueBits (IntegralCriticalScriptFP.leading (IntegralCriticalFlatClearedHeightBits.metadata F) q
      (IntegralCriticalHistoryTask.birth F.toParameters q) : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))) ∈ FP := by
    apply mem_FP_of_eq HR
    intro q
    dsimp only [Function.comp_apply]
    have HF : pairFst (IntegralCriticalFlatClearedHeightBits.cursorPacket F q) = q := by
      simp only [IntegralCriticalFlatClearedHeightBits.cursorPacket, BoundedFold.packet, pairFst_pair]
    rw [HF, IntegralCriticalFlatClearedHeightBits.cursor_cursorPacket]
  have HO := ModularScalarFP.natCast (IntegralCriticalHistoryTask.modulus_binary _ a.toAccess) (fun _ => 1) (BinaryFn.const 1)
  have HP := (valid_FP F a).ite_mem_FP HE HO
  refine mem_FP_of_eq HP (fun q => ?_)
  rw [euler_leading]
  by_cases h : valid F q
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, Nat.cast_one, Int.cast_one]
end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
