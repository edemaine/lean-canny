/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatClearedHeightSource
public import LeanCanny.Algebra.IntegralCriticalFlatCreatingFP

/-! # Total native companion metadata for arbitrary flat task words -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Scripts := IntegralCriticalFlatHeightBits.Scripts
abbrev Access := IntegralCriticalFlatHeightBits.Access

abbrev root := IntegralCriticalFlatHeightBits.root

abbrev valid (F : Scripts) (q : List Bool) : Prop :=
  IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length

instance (F : Scripts) (q : List Bool) : Decidable (valid F q) := inferInstanceAs (Decidable (_ < _))

def scalarDegree (F : Scripts) (q : List Bool) : ℕ := 2 ^ F.width (root q)
def oldRank (F : Scripts) (q : List Bool) : ℕ := count (IntegralCriticalHistoryTask.birth F.toParameters q) (F.width (root q))
def bornRank (F : Scripts) (q : List Bool) : ℕ := count (IntegralCriticalHistoryTask.birth F.toParameters q + 1) (F.width (root q))
def row (F : Scripts) (q : List Bool) : ℕ := IntegralCriticalHistoryTask.get F.toParameters .row q % bornRank F q
def col (F : Scripts) (q : List Bool) : ℕ := IntegralCriticalHistoryTask.get F.toParameters .col q % bornRank F q

def commandDegree (F : Scripts) (q : List Bool) : ℕ :=
  IntegralCriticalScriptFP.degree (IntegralCriticalFlatClearedHeightBits.metadata F) q (IntegralCriticalHistoryTask.birth F.toParameters q)

def commandOffset (F : Scripts) (q : List Bool) : ℕ :=
  IntegralCriticalScriptFP.offset (IntegralCriticalFlatClearedHeightBits.metadata F) q (IntegralCriticalHistoryTask.birth F.toParameters q)

def selectedDegree (F : Scripts) (q : List Bool) : ℕ :=
  if valid F q then PurePowerReductionBounds.dimension (F.ambient (root q) - commandOffset F q + 1) (commandDegree F q) else 0

theorem scalarDegree_pos (F : Scripts) (q : List Bool) : 0 < scalarDegree F q := Nat.two_pow_pos _
theorem oldRank_pos (F : Scripts) (q : List Bool) : 0 < oldRank F q := pow_pos (Nat.two_pow_pos _) _
theorem bornRank_pos (F : Scripts) (q : List Bool) : 0 < bornRank F q := pow_pos (Nat.two_pow_pos _) _
theorem bornRank_eq (F : Scripts) (q : List Bool) : bornRank F q = oldRank F q * scalarDegree F q := pow_succ _ _
theorem row_lt (F : Scripts) (q : List Bool) : row F q < bornRank F q := Nat.mod_lt _ (bornRank_pos _ _)
theorem col_lt (F : Scripts) (q : List Bool) : col F q < bornRank F q := Nat.mod_lt _ (bornRank_pos _ _)

def oldRow (F : Scripts) (q : List Bool) : Fin (oldRank F q) :=
  ⟨row F q / scalarDegree F q, (Nat.div_lt_iff_lt_mul (scalarDegree_pos F q)).mpr ((row_lt F q).trans_eq (bornRank_eq F q))⟩
def oldCol (F : Scripts) (q : List Bool) : Fin (oldRank F q) :=
  ⟨col F q / scalarDegree F q, (Nat.div_lt_iff_lt_mul (scalarDegree_pos F q)).mpr ((col_lt F q).trans_eq (bornRank_eq F q))⟩
def scalarRow (F : Scripts) (q : List Bool) : Fin (scalarDegree F q) :=
  ⟨row F q % scalarDegree F q, Nat.mod_lt _ (scalarDegree_pos F q)⟩
def scalarCol (F : Scripts) (q : List Bool) : Fin (scalarDegree F q) :=
  ⟨col F q % scalarDegree F q, Nat.mod_lt _ (scalarDegree_pos F q)⟩

theorem birth_unary (F : Scripts) (a : Access F) : UnaryFn (IntegralCriticalHistoryTask.birth F.toParameters) :=
  RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary _ a.toAccess)

theorem valid_FP (F : Scripts) (a : Access F) : FPPred (valid F) :=
  (BinaryFn.ofUnary (birth_unary F a)).lt (BinaryFn.ofUnary (a.count.comp RankedHistoryTask.root_FP))

theorem scalarDegree_binary (F : Scripts) (a : Access F) : BinaryFn (scalarDegree F) :=
  (BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)

theorem oldRank_binary (F : Scripts) (a : Access F) : BinaryFn (oldRank F) :=
  (scalarDegree_binary F a).powUnary (birth_unary F a)

theorem bornRank_binary (F : Scripts) (a : Access F) : BinaryFn (bornRank F) :=
  (scalarDegree_binary F a).powUnary ((birth_unary F a).add (UnaryFn.const 1))

theorem row_binary (F : Scripts) (a : Access F) : BinaryFn (row F) :=
  (IntegralCriticalHistoryTask.get_binary _ a.toAccess .row).mod (bornRank_binary F a)
theorem col_binary (F : Scripts) (a : Access F) : BinaryFn (col F) :=
  (IntegralCriticalHistoryTask.get_binary _ a.toAccess .col).mod (bornRank_binary F a)

theorem commandDegree_binary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : BinaryFn (commandDegree F) := by
  apply BinaryFn.of_eq (n.degree.comp (IntegralCriticalFlatClearedHeightBits.cursorPacket_FP F a))
  intro q
  dsimp only [Function.comp_apply]
  rw [IntegralCriticalFlatClearedHeightBits.cursor_cursorPacket]
  have HP : pairFst (IntegralCriticalFlatClearedHeightBits.cursorPacket F q) = q := by
    simp only [IntegralCriticalFlatClearedHeightBits.cursorPacket, BoundedFold.packet, pairFst_pair]
  rw [HP]
  rfl

theorem commandOffset_binary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : BinaryFn (commandOffset F) := by
  apply BinaryFn.of_eq (n.offset.comp (IntegralCriticalFlatClearedHeightBits.cursorPacket_FP F a))
  intro q
  dsimp only [Function.comp_apply]
  rw [IntegralCriticalFlatClearedHeightBits.cursor_cursorPacket]
  have HP : pairFst (IntegralCriticalFlatClearedHeightBits.cursorPacket F q) = q := by
    simp only [IntegralCriticalFlatClearedHeightBits.cursorPacket, BoundedFold.packet, pairFst_pair]
  rw [HP]
  rfl

theorem commandOffset_unary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : UnaryFn (commandOffset F) :=
  (UnaryFn.fromBitsLE_of_le (commandOffset_binary F a n).bits_mem_FP (a.ambient.comp RankedHistoryTask.root_FP)
    (fun q => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact IntegralCriticalScriptFP.offset_le _ _ _)).of_eq
      (fun _ => Nat.fromBitsLE_bits _)

theorem selectedDegree_binary (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : BinaryFn (selectedDegree F) :=
  BinaryFn.ite (valid_FP F a)
    (PurePowerReductionBounds.dimension_binary
      (((a.ambient.comp RankedHistoryTask.root_FP).sub (commandOffset_unary F a n)).add (UnaryFn.const 1))
      (commandDegree_binary F a n)) (BinaryFn.const 0)

end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
