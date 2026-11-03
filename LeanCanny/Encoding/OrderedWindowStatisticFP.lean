/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SignStatisticSpace
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # Native comparison of the five ordered window statistics

Signed statistics keep their positive and negative binary parts. Cross
addition implements the exact integer inequalities without truncation.
-/
@[expose] public section
namespace LeanCanny.Encoding.OrderedWindowStatisticBits
open LeanCanny.Algebra LeanCanny.Computation

def pack (code unit lowerSquare lower upperSquare upper : List Bool) :=
  pair code (pair unit (pair lowerSquare (pair lower (pair upperSquare upper))))
def unit (q : List Bool) :=pairFst (pairSnd q)
def lowerSquare (q : List Bool) :=pairFst (pairSnd (pairSnd q))
def lower (q : List Bool) :=pairFst (pairSnd (pairSnd (pairSnd q)))
def upperSquare (q : List Bool) :=pairFst (pairSnd (pairSnd (pairSnd (pairSnd q))))
def upper (q : List Bool) :=pairSnd (pairSnd (pairSnd (pairSnd (pairSnd q))))

theorem unit_FP : unit∈FP:=by polytime [unit]
theorem lowerSquare_FP : lowerSquare∈FP:=by polytime [lowerSquare]
theorem lower_FP : lower∈FP:=by polytime [lower]
theorem upperSquare_FP : upperSquare∈FP:=by polytime [upperSquare]
theorem upper_FP : upper∈FP:=by polytime [upper]

def positive (f : List Bool→List Bool) (q : List Bool) :=Nat.fromBitsLE (pairFst (f q))
def negative (f : List Bool→List Bool) (q : List Bool) :=Nat.fromBitsLE (pairSnd (f q))

def Accept (q : List Bool) : Prop :=
  2*positive unit q+negative lowerSquare q+negative lower q≤
    2*Nat.fromBitsLE (pairFst q)+positive lowerSquare q+positive lower q+2*negative unit q ∧
  2*Nat.fromBitsLE (pairFst q)+negative upperSquare q+positive upper q<positive upperSquare q+negative upper q

theorem positive_binary (f : List Bool→List Bool) (hf : f∈FP) : BinaryFn (positive f) :=
  BinaryFn.fromBits (mem_FP_comp hf pairFst_mem_FP)
theorem negative_binary (f : List Bool→List Bool) (hf : f∈FP) : BinaryFn (negative f) :=
  BinaryFn.fromBits (mem_FP_comp hf pairSnd_mem_FP)

theorem accept_fppred : FPPred Accept :=by
  have h0p:=positive_binary unit unit_FP
  have h0n:=negative_binary unit unit_FP
  have hLp:=positive_binary lowerSquare lowerSquare_FP
  have hLn:=negative_binary lowerSquare lowerSquare_FP
  have hlp:=positive_binary lower lower_FP
  have hln:=negative_binary lower lower_FP
  have hUp:=positive_binary upperSquare upperSquare_FP
  have hUn:=negative_binary upperSquare upperSquare_FP
  have hup:=positive_binary upper upper_FP
  have hun:=negative_binary upper upper_FP
  have hk : BinaryFn (fun q=>Nat.fromBitsLE (pairFst q)):=BinaryFn.fromBits pairFst_mem_FP
  exact (((((BinaryFn.const 2).mul h0p).add hLn).add hln).le
    (((((BinaryFn.const 2).mul hk).add hLp).add hlp).add ((BinaryFn.const 2).mul h0n))).and
      (((((BinaryFn.const 2).mul hk).add hUn).add hup).lt (hUp.add hun))

theorem packet (code : ℕ) (v0 vl2 vl1 vh2 vh1 : ℤ) :
    Accept (pack (BinaryNatCode.encode code) (SignStatisticBits.integerCode v0)
      (SignStatisticBits.integerCode vl2) (SignStatisticBits.integerCode vl1)
      (SignStatisticBits.integerCode vh2) (SignStatisticBits.integerCode vh1))↔
      2*v0≤2*(code:ℤ)+vl2+vl1 ∧ 2*(code:ℤ)<vh2-vh1 :=by
  simp only [Accept,positive,negative,pack,unit,lowerSquare,lower,upperSquare,upper,
    SignStatisticBits.integerCode,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  omega

end LeanCanny.Encoding.OrderedWindowStatisticBits
