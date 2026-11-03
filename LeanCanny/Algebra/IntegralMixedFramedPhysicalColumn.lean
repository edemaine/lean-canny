/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLayout
/-! # Native scalar columns in the actual full physical carrier

A request pairs the unchanged saved key with a newest-first scalar index.
The column is the last column of that scalar's creating full prefix.
Out-of-range scalar requests return zero, with no implicit physical root.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength commands)
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def retainedPrefix (P : Parameters) (q : List Bool) :=
  prefixLength P (pairFst q)-min (Nat.fromBitsLE (pairSnd q)) (prefixLength P (pairFst q))

theorem retainedPrefix_unary (P : Parameters) (a : Access P) : UnaryFn (retainedPrefix P) :=
  ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP).sub
    (UnaryFn.fromBitsLE_min pairSnd_mem_FP ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP))

def columnPacket (P : Parameters) (q : List Bool) := pair (pairFst q) (List.replicate (retainedPrefix P q) true)
theorem columnPacket_FP (P : Parameters) (a : Access P) : columnPacket P∈FP :=
  mem_FP_pair pairFst_mem_FP (retainedPrefix_unary P a).mem_FP

def scalarColumn (P : Parameters) (T : Tables) (q : List Bool) := prefixArity P T (columnPacket P q)-1
theorem scalarColumn_unary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (scalarColumn P T) :=
  ((prefixArity_unary P a T h).comp (columnPacket_FP P a)).sub (UnaryFn.const 1)

theorem scalarColumn_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (i : ℕ)
    (hi : i<prefixLength P key) :
    scalarColumn P T (pair key (BinaryNatCode.encode i))=slotNumber (commands P D key) i := by
  have HR : retainedPrefix P (pair key (BinaryNatCode.encode i))=prefixLength P key-i := by
    simp only [retainedPrefix,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
      min_eq_left hi.le]
  unfold scalarColumn columnPacket
  simp only [pairFst_pair,HR]
  rw [prefixArity_packet P D H T hr]
  have HL : (commands P D key).length=prefixLength P key :=
    IntegralMixedFramedHistoryScript.paddedPast_length _ _ _
  rw [slotNumber_drop _ i (hi.trans_eq HL.symm)]
  have HD:=IntegralMixedFramedHistoryScript.paddedPast_drop
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key))
    (prefixLength P key) (prefixLength P key-i) (Nat.sub_le _ _)
  have HI : prefixLength P key-(prefixLength P key-i)=i := Nat.sub_sub_self hi.le
  rw [HI] at HD
  exact congrArg (fun cs=>arity cs-1) HD.symm

/-- Literal actual sampler injection, computed from the original headers. -/
theorem scalarColumn_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool)
    (i : Fin ((commands P D key).length)) :
    scalarColumn P T (pair key (BinaryNatCode.encode i.val))=
      (enumerate (commands P D key)
        (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalar i)).val := by
  rw [family_scalar,enumerate_scalar]
  exact scalarColumn_packet P D H T hr key i.val (i.isLt.trans_eq (IntegralMixedFramedHistoryScript.paddedPast_length _ _ _))

theorem scalarColumn_outside (P : Parameters) (T : Tables) (key : List Bool) (i : ℕ)
    (hi : prefixLength P key ≤ i) : scalarColumn P T (pair key (BinaryNatCode.encode i))=0 := by
  have HR : retainedPrefix P (pair key (BinaryNatCode.encode i))=0 := by
    simp only [retainedPrefix,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
      min_eq_right hi,Nat.sub_self]
  unfold scalarColumn columnPacket
  simp only [pairFst_pair,HR,prefixArity,pairSnd_pair,List.length_replicate,Finset.range_zero,
    Finset.sum_empty,Nat.zero_sub]
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
