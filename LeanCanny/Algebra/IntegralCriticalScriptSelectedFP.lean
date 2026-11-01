/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatCompanion

/-! # Primitive leading residues at actual creating commands

The newest-first command index is converted to its chronological cursor.
Native primitive metadata then reads the original integer leading residue;
this reader does not execute an algebraic coefficient or history evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptSelectedFP
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript IntegralCriticalFlatCompanionBits
set_option backward.isDefEq.respectTransparency false

variable (F : IntegralCriticalScriptGeneratorBits.Queries)

theorem commandAt_creating (c : List Bool) :
    IntegralCriticalScriptFP.commandAt (metadata F) c (older (F.rules c) (F.selected c)).length =
      some (chosen (F.rules c) (F.selected c)) := by
  change (F.rules c).reverse[(older (F.rules c) (F.selected c)).length]? = _
  rw [List.getElem?_reverse' (j := (F.selected c).val) (by
    have H := (F.selected c).isLt
    rw [older_length]
    omega)]
  exact List.getElem?_eq_getElem (F.selected c).isLt

def packet (c : List Bool) : List Bool :=
  BoundedFold.packet c (older (F.rules c) (F.selected c)).length []

theorem packet_FP (h : IntegralCriticalScriptGeneratorBits.Controls F) : packet F ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair
    (BinaryFn.ofUnary (IntegralCriticalScriptGeneratorBits.arity_unary F h)).bits_mem_FP (constFn_mem_FP []))

theorem cursor_packet (c : List Bool) : IntegralDenominatorPass.cursor (packet F c) =
    (older (F.rules c) (F.selected c)).length := by
  simp only [IntegralDenominatorPass.cursor, BoundedFold.counter, packet, BoundedFold.packet,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem leading_FP (h : IntegralCriticalScriptGeneratorBits.Controls F)
    (a : IntegralCriticalScriptFP.Access (metadata F)) :
    (fun c => residueBits ((chosen (F.rules c) (F.selected c)).leading : ZMod (F.modulus c))) ∈ FP := by
  have H := mem_FP_comp (packet_FP F h) a.leading
  refine mem_FP_of_eq H (fun c => ?_)
  change residueBits (IntegralCriticalScriptFP.leading (metadata F) (pairFst (packet F c))
    (IntegralDenominatorPass.cursor (packet F c)) : ZMod (F.modulus (pairFst (packet F c)))) = _
  rw [cursor_packet]
  have HP : pairFst (packet F c) = c := by simp only [packet, BoundedFold.packet, pairFst_pair]
  rw [HP]
  unfold IntegralCriticalScriptFP.leading
  rw [commandAt_creating F c]
  rfl

end LeanCanny.Algebra.IntegralCriticalScriptSelectedFP
