/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceAtSpace
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarRowSpace
/-! # Native oldest-first columns of a new physical critical block

Old columns precede the ambient block, the multiplier block and the fresh
scalar. All maps are literal arithmetic; no finite-equivalence evaluator is
assumed. Counts come from original represented headers.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def oldCount (P : Parameters) (D : Plan P) (base : List Bool→List Bool) (q : List Bool) :=
  IntegralMixedFramedFullScalarRowBits.fullCount P D (IntegralMixedVirtualTaskBits.saved P) (base q)
noncomputable abbrev spatialCount (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) := (IntegralMixedFramedPhysicalSourceAtBits.family P D J base).ambient q+1
noncomputable def fullCount (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) := oldCount P D base q+
      (spatialCount P D J base q+(spatialCount P D J base q+1)+1)

noncomputable def oldIndex (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (oldCount P D base q)) : Fin (fullCount P D J base q) :=
  ⟨i.val,by have H:=i.isLt;unfold fullCount;omega⟩
noncomputable def ambientIndex (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q)) : Fin (fullCount P D J base q) :=
  ⟨oldCount P D base q+i.val,by have H:=i.isLt;unfold fullCount;omega⟩
noncomputable def multiplierIndex (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q+1)) : Fin (fullCount P D J base q) :=
  ⟨oldCount P D base q+spatialCount P D J base q+i.val,by have H:=i.isLt;unfold fullCount;omega⟩

theorem oldIndex_injective (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) : Function.Injective (oldIndex P D J base q) := by
  intro i j h
  have H:=congrArg Fin.val h
  exact Fin.ext H
theorem ambientIndex_injective (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) : Function.Injective (ambientIndex P D J base q) := by
  intro i j h
  have H:=congrArg Fin.val h
  apply Fin.ext
  exact Nat.add_left_cancel H
theorem multiplierIndex_injective (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) : Function.Injective (multiplierIndex P D J base q) := by
  intro i j h
  have H:=congrArg Fin.val h
  apply Fin.ext
  exact Nat.add_left_cancel H

theorem oldCount_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : UnaryFn (oldCount P D base) :=
  (IntegralMixedFramedFullScalarRowBits.fullCount_unary P a D J c.critical.tables c.critical.native c.critical.represents
    _ (IntegralMixedVirtualTaskBits.saved_FP P a)).comp hb

theorem spatialCount_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : UnaryFn (spatialCount P D J base) :=
  (IntegralMixedFramedPhysicalSourceAtBits.metadata P a D J c base hb).ambient.add (UnaryFn.const 1)

theorem fullCount_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : UnaryFn (fullCount P D J base) := by
  have HA:=spatialCount_unary P a D J c base hb
  exact (oldCount_unary P a D J c base hb).add ((HA.add (HA.add (UnaryFn.const 1))).add (UnaryFn.const 1))

def oldReader (p : List Bool) := pairSnd p
noncomputable def ambientReader (P : Parameters) (D : Plan P) (base : List Bool→List Bool) (p : List Bool) :=
  BinaryNatCode.encode (oldCount P D base (pairFst p)+Nat.fromBitsLE (pairSnd p))
noncomputable def multiplierReader (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (p : List Bool) :=
  BinaryNatCode.encode (oldCount P D base (pairFst p)+spatialCount P D J base (pairFst p)+Nat.fromBitsLE (pairSnd p))

theorem ambientReader_FP (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : ambientReader P D base∈FP := by
  have HO : BinaryFn (fun p=>oldCount P D base (pairFst p)):=
    (BinaryFn.ofUnary (oldCount_unary P a D J c base hb)).comp pairFst_mem_FP
  exact (HO.add (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP

theorem multiplierReader_FP (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : multiplierReader P D J base∈FP := by
  have HO : BinaryFn (fun p=>oldCount P D base (pairFst p)):=
    (BinaryFn.ofUnary (oldCount_unary P a D J c base hb)).comp pairFst_mem_FP
  have HA : BinaryFn (fun p=>spatialCount P D J base (pairFst p)):=
    (BinaryFn.ofUnary (spatialCount_unary P a D J c base hb)).comp pairFst_mem_FP
  exact ((HO.add HA).add (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP

theorem ambientReader_packet (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q)) :
    ambientReader P D base (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode (ambientIndex P D J base q i).val := by
  simp only [ambientReader,ambientIndex,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem multiplierReader_packet (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q+1)) :
    multiplierReader P D J base (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode (multiplierIndex P D J base q i).val := by
  simp only [multiplierReader,multiplierIndex,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
