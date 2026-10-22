/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ParameterSourceBounds
public import LeanCanny.Algebra.RationalSubstitutionBudget

/-! # FP binary writers for effective small-parameter bounds

The writers use only addition, multiplication, successor, and binary length.
Their semantics cover arbitrary metadata words, including redundant zero bits.
-/

@[expose] public section

namespace LeanCanny.Algebra.ParameterBudget

open LeanCanny.Encoding

def add (a b : List Bool) : List Bool := BinaryNat.add (pair a b)
def mul (a b : List Bool) : List Bool := BinaryNat.mul (pair a b)
def sizeCode (a : List Bool) : List Bool := BinaryNatCode.encode (BinaryNat.normalize a).length

theorem add_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) : (fun c => add (a c) (b c)) ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha hb) BinaryNat.add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem mul_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) : (fun c => mul (a c) (b c)) ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha hb) BinaryNat.mul_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem sizeCode_FP {a : List Bool → List Bool} (ha : a ∈ FP) : (fun c => sizeCode (a c)) ∈ FP := by
  have h := bits_mem_FP (UnaryFn.length (mem_FP_comp ha BinaryNat.normalize_mem_FP))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem add_value (a b : List Bool) : Nat.fromBitsLE (add a b) = Nat.fromBitsLE a + Nat.fromBitsLE b := by
  simp only [add, BinaryNat.add_pair, Nat.fromBitsLE_bits]

theorem mul_value (a b : List Bool) : Nat.fromBitsLE (mul a b) = Nat.fromBitsLE a * Nat.fromBitsLE b := by
  simp only [mul, BinaryNat.mul_pair, Nat.fromBitsLE_bits]

theorem sizeCode_value (a : List Bool) : Nat.fromBitsLE (sizeCode a) = (Nat.fromBitsLE a).size := by
  simp only [sizeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, BinaryNat.normalize_eq_bits, Nat.size_eq_bits_len]

def seedCode (dp df bp bf : List Bool) : List Bool :=
  add (add (add (mul (mul [false, true] (BinaryNat.succ (add dp df))) (BinaryNat.succ bp)) bf) (sizeCode dp)) bp

theorem seedCode_FP {dp df bp bf : List Bool → List Bool}
    (hdp : dp ∈ FP) (hdf : df ∈ FP) (hbp : bp ∈ FP) (hbf : bf ∈ FP) :
    (fun c => seedCode (dp c) (df c) (bp c) (bf c)) ∈ FP := by
  have hD := mem_FP_comp (add_FP hdp hdf) BinaryNat.succ_mem_FP
  have hp := mem_FP_comp hbp BinaryNat.succ_mem_FP
  have hn := mul_FP (constFn_mem_FP [false, true]) hD
  have h := add_FP (add_FP (add_FP (mul_FP hn hp) hbf) (sizeCode_FP hdp)) hbp
  refine mem_FP_of_eq h ?_
  intro c
  simp only [seedCode, Function.comp_apply]

theorem seedCode_value (dp df bp bf : List Bool) : Nat.fromBitsLE (seedCode dp df bp bf) =
    ParameterTarski.seedMassBound (Nat.fromBitsLE dp) (Nat.fromBitsLE df) (Nat.fromBitsLE bp) (Nat.fromBitsLE bf) := by
  simp only [seedCode, add_value, mul_value, sizeCode_value, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
    ParameterTarski.seedMassBound, show Nat.fromBitsLE [false, true] = 2 from rfl]

def principalCode (R a : List Bool) : List Bool := add (add (mul (sizeCode R) R) (mul R a)) a

theorem principalCode_FP {R a : List Bool → List Bool} (hR : R ∈ FP) (ha : a ∈ FP) :
    (fun c => principalCode (R c) (a c)) ∈ FP := by
  have h := add_FP (add_FP (mul_FP (sizeCode_FP hR) hR) (mul_FP hR ha)) ha
  refine mem_FP_of_eq h ?_
  intro c
  simp only [principalCode]

theorem principalCode_value (R a : List Bool) : Nat.fromBitsLE (principalCode R a) =
    PrincipalSubresultant.parameterMassBound (Nat.fromBitsLE R) (Nat.fromBitsLE a) := by
  simp only [principalCode, add_value, mul_value, sizeCode_value, PrincipalSubresultant.parameterMassBound]

def sourceCode (dp df bp bf : List Bool) : List Bool :=
  principalCode (mul [false, true] dp) (add bp (seedCode dp df bp bf))

theorem sourceCode_FP {dp df bp bf : List Bool → List Bool}
    (hdp : dp ∈ FP) (hdf : df ∈ FP) (hbp : bp ∈ FP) (hbf : bf ∈ FP) :
    (fun c => sourceCode (dp c) (df c) (bp c) (bf c)) ∈ FP := by
  have h := principalCode_FP (mul_FP (constFn_mem_FP [false, true]) hdp)
    (add_FP hbp (seedCode_FP hdp hdf hbp hbf))
  refine mem_FP_of_eq h ?_
  intro c
  simp only [sourceCode]

theorem sourceCode_value (dp df bp bf : List Bool) : Nat.fromBitsLE (sourceCode dp df bp bf) =
    ParameterTarski.sourceBound (Nat.fromBitsLE dp) (Nat.fromBitsLE df) (Nat.fromBitsLE bp) (Nat.fromBitsLE bf) := by
  simp only [sourceCode, principalCode_value, add_value, mul_value, seedCode_value, ParameterTarski.sourceBound,
    show Nat.fromBitsLE [false, true] = 2 from rfl]

def coefficientCode (dp df bp bf : List Bool) : List Bool := sourceCode dp df
  (RationalSubstitution.sourceBudgetCode [true] dp bp) (RationalSubstitution.sourceBudgetCode [true] df bf)

theorem coefficientCode_FP {dp df bp bf : List Bool → List Bool}
    (hdp : dp ∈ FP) (hdf : df ∈ FP) (hbp : bp ∈ FP) (hbf : bf ∈ FP) :
    (fun c => coefficientCode (dp c) (df c) (bp c) (bf c)) ∈ FP := by
  have hp := RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hdp hbp
  have hf := RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hdf hbf
  exact sourceCode_FP hdp hdf hp hf

theorem coefficientCode_value (dp df bp bf : List Bool) : Nat.fromBitsLE (coefficientCode dp df bp bf) =
    ParameterTarski.sourceBound (Nat.fromBitsLE dp) (Nat.fromBitsLE df)
      (Nat.fromBitsLE bp + (Nat.fromBitsLE dp + 1).size) (Nat.fromBitsLE bf + (Nat.fromBitsLE df + 1).size) := by
  simp only [coefficientCode, sourceCode_value, RationalSubstitution.sourceBudgetCode_code,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl, one_mul]

def patternCode (dp D k bp bf : List Bool) : List Bool := sourceCode dp (mul (mul [false, true] k) D)
  (RationalSubstitution.sourceBudgetCode [true] dp bp)
  (mul (mul [false, true] k) (RationalSubstitution.sourceBudgetCode [true] D bf))

theorem patternCode_FP {dp D k bp bf : List Bool → List Bool}
    (hdp : dp ∈ FP) (hD : D ∈ FP) (hk : k ∈ FP) (hbp : bp ∈ FP) (hbf : bf ∈ FP) :
    (fun c => patternCode (dp c) (D c) (k c) (bp c) (bf c)) ∈ FP := by
  have hn := mul_FP (constFn_mem_FP [false, true]) hk
  have hd := mul_FP hn hD
  have hp := RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hdp hbp
  have hf := mul_FP hn (RationalSubstitution.sourceBudgetCode_mem_FP (constFn_mem_FP [true]) hD hbf)
  exact sourceCode_FP hdp hd hp hf

theorem patternCode_value (dp D k bp bf : List Bool) : Nat.fromBitsLE (patternCode dp D k bp bf) =
    ParameterTarski.patternSourceBound (Nat.fromBitsLE dp) (Nat.fromBitsLE D) (Nat.fromBitsLE k)
      (Nat.fromBitsLE bp) (Nat.fromBitsLE bf) := by
  simp only [patternCode, sourceCode_value, mul_value, RationalSubstitution.sourceBudgetCode_code,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl, one_mul,
    show Nat.fromBitsLE [false, true] = 2 from rfl, ParameterTarski.patternSourceBound]

end LeanCanny.Algebra.ParameterBudget
