/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatHeightCorrect
public import LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP

/-! # Actual coordinate cofactors from flat critical-source metadata

The creating command is looked up chronologically in the original root
script. Slot eight chooses the common-cleared retained coordinate. Every
scale residue is derived by the native actual-prefix denominator pass.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def metadata (F : Scripts) : IntegralCriticalScriptFP.Family where
  ambient q := F.ambient (root q)
  sourceWidth q := F.sourceWidth (root q)
  degreeBound q := F.degree (root q)
  height q := F.height (root q)
  rules q := F.rules (root q)
  modulus := IntegralCriticalHistoryTask.modulus F.toParameters
  modulus_ne_zero := IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters

def cursorPacket (F : Scripts) (q : List Bool) : List Bool :=
  BoundedFold.packet q (IntegralCriticalHistoryTask.birth F.toParameters q) []

theorem cursorPacket_FP (F : Scripts) (a : Access F) : cursorPacket F ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair
    (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary _ a.toAccess))).bits_mem_FP
    (constFn_mem_FP []))

theorem cursor_cursorPacket (F : Scripts) (q : List Bool) :
    IntegralDenominatorPass.cursor (cursorPacket F q) = IntegralCriticalHistoryTask.birth F.toParameters q := by
  simp only [IntegralDenominatorPass.cursor, cursorPacket, BoundedFold.packet, BoundedFold.counter,
    pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def selector (F : Scripts) (q : List Bool) (i : ℕ) : ℕ :=
  IntegralCriticalScriptFP.selector (metadata F) q (IntegralCriticalHistoryTask.birth F.toParameters q) i

theorem selector_binary (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) :
    BinaryFn (fun p => selector F (pairFst p) (Nat.fromBitsLE (pairSnd p))) := by
  have HQ := mem_FP_pair (mem_FP_comp pairFst_mem_FP (cursorPacket_FP F a)) pairSnd_mem_FP
  apply BinaryFn.of_eq (n.selector.comp HQ)
  intro p
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, cursor_cursorPacket]
  have HP : pairFst (cursorPacket F (pairFst p)) = pairFst p := by
    simp only [cursorPacket, BoundedFold.packet, pairFst_pair]
  rw [HP]
  rfl

def coordinate (F : Scripts) := IntegralCriticalHistoryTask.get F.toParameters .slot8

def selected (F : Scripts) (q : List Bool) := selector F q (coordinate F q)

theorem selected_binary (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) : BinaryFn (selected F) := by
  have HQ := mem_FP_pair id_mem_FP (IntegralCriticalHistoryTask.get_binary _ a.toAccess .slot8).bits_mem_FP
  apply BinaryFn.of_eq ((selector_binary F a n).comp HQ)
  intro q
  simp only [Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def queries (F : Scripts) : IntegralCriticalScriptHeightBits.Queries :=
  { IntegralCriticalFlatHeightBits.heightQueries F with selector := selector F, coordinate := coordinate F }

theorem controls (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) :
    IntegralCriticalScriptHeightBits.Controls (queries F) :=
  { IntegralCriticalFlatHeightBits.heightControls F a with
    selector := selector_binary F a n
    coordinate := IntegralCriticalHistoryTask.get_binary _ a.toAccess .slot8 }

noncomputable def access (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) :
    CommonHeightBits.Access (IntegralCriticalScriptHeightBits.scalars (queries F)) :=
  IntegralCriticalScriptHeightBits.access (queries F) (controls F a n) (IntegralCriticalScriptFP.access (metadata F) n)

theorem cofactor_FP (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) :
    (fun q => residueBits ((IntegralCriticalScriptHeightBits.scalars (queries F)).cofactor q :
      ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))) ∈ FP :=
  CommonHeightBits.cofactor_FP _ (access F a n)

theorem selector_outside (F : Scripts) (q : List Bool) (i : ℕ) (hi : ¬ i < F.ambient (root q) + 1) :
    selector F q i = IntegralCriticalHistoryTask.birth F.toParameters q := by
  unfold selector IntegralCriticalScriptFP.selector
  cases IntegralCriticalScriptFP.commandAt (metadata F) q (IntegralCriticalHistoryTask.birth F.toParameters q) with
  | none => rfl
  | some r => exact dite_eq_right hi

end LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
