/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockLayout
/-! # Native physical powers on the full numeric critical block -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def degree (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :=
  ((IntegralMixedFramedPhysicalSourceAtBits.family P D J base).spatial q).degree

def physicalPower (P : Parameters) (base : List Bool→List Bool) (q : List Bool) :=
  physical (P.cap (RankedHistoryTask.root (base q))+1) (2^P.width (RankedHistoryTask.root (base q))) (birth P (base q))

noncomputable def powers (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (p : List Bool) :=
  if Nat.fromBitsLE (pairSnd p)<oldCount P D base (pairFst p) then 1 else
  if Nat.fromBitsLE (pairSnd p)<oldCount P D base (pairFst p)+spatialCount P D J base (pairFst p) then physicalPower P base (pairFst p) else
  if Nat.fromBitsLE (pairSnd p)<oldCount P D base (pairFst p)+spatialCount P D J base (pairFst p)+(spatialCount P D J base (pairFst p)+1)
    then (degree P D J base (pairFst p)-1)*physicalPower P base (pairFst p) else 1

theorem physicalPower_binary (P : Parameters) (a : Access P) (base : List Bool→List Bool) (hb : base∈FP) : BinaryFn (physicalPower P base) :=
  physical_binary (((a.cap.comp (mem_FP_comp hb RankedHistoryTask.root_FP)).add (UnaryFn.const 1)))
    ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp hb RankedHistoryTask.root_FP)))
    ((RankedHistoryTask.birth_unary _ (birthCap_unary P a)).comp hb)

theorem powers_binary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : BinaryFn (powers P D J base) := by
  have HI : BinaryFn (fun p=>Nat.fromBitsLE (pairSnd p)):=BinaryFn.fromBits pairSnd_mem_FP
  have HO : BinaryFn (fun p=>oldCount P D base (pairFst p)):=
    (BinaryFn.ofUnary (oldCount_unary P a D J c base hb)).comp pairFst_mem_FP
  have HA : BinaryFn (fun p=>spatialCount P D J base (pairFst p)):=
    (BinaryFn.ofUnary (spatialCount_unary P a D J c base hb)).comp pairFst_mem_FP
  have HW : BinaryFn (fun p=>physicalPower P base (pairFst p)):=(physicalPower_binary P a base hb).comp pairFst_mem_FP
  have HD : BinaryFn (fun p=>degree P D J base (pairFst p)):=
    (IntegralMixedFramedPhysicalSourceAtBits.metadata P a D J c base hb).degree.comp pairFst_mem_FP
  exact BinaryFn.ite (HI.lt HO) (BinaryFn.const 1) (BinaryFn.ite (HI.lt (HO.add HA)) HW
    (BinaryFn.ite (HI.lt ((HO.add HA).add (HA.add (BinaryFn.const 1)))) ((HD.sub (BinaryFn.const 1)).mul HW) (BinaryFn.const 1)))

theorem powers_pos (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (fullCount P D J base q)) :
    0<powers P D J base (pair q (BinaryNatCode.encode i.val)) := by
  unfold powers
  simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  split_ifs
  · exact Nat.zero_lt_one
  · exact physical_pos _ _ _
  · have HD : 2≤degree P D J base q:=((IntegralMixedFramedPhysicalSourceAtBits.family P D J base).spatial q).degree_two
    exact Nat.mul_pos (by omega) (physical_pos _ _ _)
  · exact Nat.zero_lt_one

theorem powers_old (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (oldCount P D base q)) :
    powers P D J base (pair q (BinaryNatCode.encode (oldIndex P D J base q i).val))=1 := by
  unfold powers oldIndex
  simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,ite_eq_left i.isLt]

theorem powers_ambient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q)) :
    powers P D J base (pair q (BinaryNatCode.encode (ambientIndex P D J base q i).val))=physicalPower P base q := by
  unfold powers ambientIndex
  simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [ite_eq_right (by omega),ite_eq_left (by have H:=i.isLt;omega)]

theorem powers_multiplier (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q+1)) :
    powers P D J base (pair q (BinaryNatCode.encode (multiplierIndex P D J base q i).val))=
      (degree P D J base q-1)*physicalPower P base q := by
  unfold powers multiplierIndex
  simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by have H:=i.isLt;omega)]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
