/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TermModularData
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
public import LeanCanny.ETR.NNFFP
public import LeanCanny.Encoding.ContextSourceTreeFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-! # Raw-data frames with separately encoded modular annotations -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.TermModular

open LeanCanny.Encoding LeanCanny.ETR Turing.MultiTapeTM
open Brackets

structure Parameters where
  prime : List Bool → ℕ
  coordinate : List Bool → ℕ → ℕ

structure Access (P : Parameters) : Prop where
  prime : BinaryFn P.prime
  coordinate : ComputableTidilyInPolyTime (fun q : List Bool × ℕ => P.coordinate q.1 q.2)
    (encPair encBits encNat) encNat

 def cap (P : Parameters) (z : List Bool) : ℕ := modulus (P.prime z)
 def raw (frame : List Bool) : List Bool := pairFst frame
 def values (frame : List Bool) : List ℕ := (Decoder.list Decoder.nat).decode (pairSnd frame)
 def context (packet : List Bool) : List Bool := pairFst packet
 def frame (packet : List Bool) : List Bool := pairSnd packet
 def variableIndex (packet : List Bool) : ℕ := Codec.unaryValue (NNF.second (raw (frame packet)))
 def leftValue (packet : List Bool) : ℕ := (values (frame packet))[1]?.getD 0
 def rightValue (packet : List Bool) : ℕ := (values (frame packet))[2]?.getD 0

 def code (P : Parameters) (z : List Bool) (xs : List Data) : List Bool :=
  pair (Data.l xs).toBits (encList encNat (xs.map (value (P.prime z) (P.coordinate z))))

 def finish (P : Parameters) (packet : List Bool) : ℕ :=
  if NNF.HasOne 0 (raw (frame packet)) then
    Nat.fromBitsLE (Codec.IntegerResidue.value
      (pair (NNF.second (raw (frame packet))) (BinaryNatCode.encode (cap P (context packet))))) % cap P (context packet)
  else if NNF.HasOne 1 (raw (frame packet)) then P.coordinate (context packet) (variableIndex packet) % cap P (context packet)
  else if NNF.HasTwo 2 (raw (frame packet)) then (leftValue packet + rightValue packet) % cap P (context packet)
  else if NNF.HasTwo 3 (raw (frame packet)) then (leftValue packet * rightValue packet) % cap P (context packet)
  else 0

 theorem cap_binary (P : Parameters) (hP : Access P) : BinaryFn (cap P) :=
  (ComputableInPolyTime.binary_max' (.const 1) hP.prime.computableInPolyTime).tidy

 theorem values_FP : ComputableTidilyInPolyTime values encBits (encList encNat) :=
  (Decoder.list Decoder.nat).computableInPolyTime.tidy.comp (FP.computable pairSnd_mem_FP)

 theorem variableIndex_unary : UnaryFn variableIndex := by
  have hs : (fun p => NNF.second (raw (frame p))) ∈ FP :=
    mem_FP_comp (f := fun p => raw (frame p)) (g := NNF.second)
      (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) NNF.second_mem_FP
  exact UnaryFn.comp (f := Codec.unaryValue) (g := fun p => NNF.second (raw (frame p)))
    Codec.unaryValue_unary hs

 theorem leftValue_binary : BinaryFn leftValue := by
  have hv := values_FP.comp (FP.computable pairSnd_mem_FP)
  have h : ComputableInPolyTime (fun p : List Bool => (values (frame p))[1]?.getD 0) encBits encNat := by
    simpa only [List.getD_eq_getElem?_getD, frame, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hv.computableInPolyTime (ComputableInPolyTime.const 1)
  exact h.tidy

 theorem rightValue_binary : BinaryFn rightValue := by
  have hv := values_FP.comp (FP.computable pairSnd_mem_FP)
  have h : ComputableInPolyTime (fun p : List Bool => (values (frame p))[2]?.getD 0) encBits encNat := by
    simpa only [List.getD_eq_getElem?_getD, frame, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hv.computableInPolyTime (ComputableInPolyTime.const 2)
  exact h.tidy

theorem raw_FP : raw ∈ FP := pairFst_mem_FP
theorem frame_FP : frame ∈ FP := pairSnd_mem_FP
theorem context_FP : context ∈ FP := pairFst_mem_FP

section NativeFinish

attribute [local irreducible] cap raw values context frame variableIndex leftValue rightValue
attribute [local irreducible] NNF.second Codec.IntegerResidue.value BinaryNatCode.encode

 theorem finish_binary (P : Parameters) (hP : Access P) : BinaryFn (finish P) := by
  have hraw : (fun p => raw (frame p)) ∈ FP := mem_FP_comp (f := frame) (g := raw) frame_FP raw_FP
  have hctx : context ∈ FP := context_FP
  have hcap : BinaryFn (fun p => cap P (context p)) :=
    (cap_binary P hP).comp (FP.computable hctx)
  have hpayload := mem_FP_comp hraw NNF.second_mem_FP
  have hconstantBits := mem_FP_comp (mem_FP_pair hpayload hcap.bits_mem_FP) Codec.IntegerResidue.value_mem_FP
  have hconstant := (BinaryFn.fromBits hconstantBits).mod hcap
  have hcoordinate : BinaryFn (fun p => P.coordinate (context p) (variableIndex p)) :=
    hP.coordinate.comp ((FP.computable hctx).prod (BinaryFn.ofUnary variableIndex_unary))
  have hvar := hcoordinate.mod hcap
  have hadd := (leftValue_binary.add rightValue_binary).mod hcap
  have hmul := (leftValue_binary.mul rightValue_binary).mod hcap
  have h : BinaryFn (finish P) := BinaryFn.ite ((NNF.hasOne_fppred 0).comp hraw) hconstant
    (BinaryFn.ite ((NNF.hasOne_fppred 1).comp hraw) hvar
      (BinaryFn.ite ((NNF.hasTwo_fppred 2).comp hraw) hadd
        (BinaryFn.ite ((NNF.hasTwo_fppred 3).comp hraw) hmul (BinaryFn.const 0))))
  exact h

end NativeFinish

 theorem raw_code (P : Parameters) (z : List Bool) (xs : List Data) : raw (code P z xs) = (Data.l xs).toBits := by
  rw [raw, code, pairFst_pair]

 theorem values_code (P : Parameters) (z : List Bool) (xs : List Data) :
    values (code P z xs) = xs.map (value (P.prime z) (P.coordinate z)) := by
  rw [values, code, pairSnd_pair, Decoder.decode_enc]

 theorem finish_code (P : Parameters) (z : List Bool) (xs : List Data) :
    finish P (pair z (code P z xs)) = value (P.prime z) (P.coordinate z) (.l xs) := by
  rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
  all_goals simp [finish, context, frame, raw_code, values_code, NNF.hasOne_toBits, NNF.hasTwo_toBits,
    NNF.one, NNF.two, NNF.second, remainingChildren_toBits, firstChild_toBits,
    variableIndex, leftValue, rightValue, Codec.unaryValue, Data.length_toBits, value, constant, cap]

end LeanCanny.CountingHierarchy.TermModular
