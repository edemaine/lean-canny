/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexGateEncoding

/-! # Native constructors for shared complex arithmetic networks

Gate writers retain unary wire-index certificates and copy serialized integer
constants. They produce the exact network codec consumed by the real-equation
compiler, allowing later query generators to keep shared intermediate values.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Encoding.Brackets

def pairDataBits (a b : List Bool) : List Bool := wrap (a ++ b)

theorem pairDataBits_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun c => pairDataBits (a c) (b c)) ∈ FP :=
  mem_FP_comp (f := fun c => a c ++ b c) (g := wrap) (appendFn_mem_FP ha hb) wrap_mem_FP

theorem pairDataBits_toBits (a b : Data) : pairDataBits a.toBits b.toBits = (pairData a b).toBits := by
  simp [pairDataBits, pairData, Data.toBits_l, wrap]

def constantGateBits (out : ℕ) (value : List Bool) : List Bool :=
  pairDataBits (Codec.unary 0).toBits (pairDataBits (Codec.unary out).toBits value)

def arithmeticGateBits (tag out left right : ℕ) : List Bool :=
  pairDataBits (Codec.unary tag).toBits
    (pairDataBits (Codec.unary out).toBits (pairDataBits (Codec.unary left).toBits (Codec.unary right).toBits))

def zeroGateBits (wire : ℕ) : List Bool := pairDataBits (Codec.unary 3).toBits (Codec.unary wire).toBits

theorem constantGateBits_mem_FP {out : List Bool → ℕ} {value : List Bool → List Bool}
    (ho : UnaryFn out) (hv : value ∈ FP) : (fun c => constantGateBits (out c) (value c)) ∈ FP :=
  pairDataBits_mem_FP (constFn_mem_FP _) (pairDataBits_mem_FP (Codec.unary_toBits_mem_FP ho) hv)

theorem arithmeticGateBits_mem_FP (tag : ℕ) {out left right : List Bool → ℕ}
    (ho : UnaryFn out) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => arithmeticGateBits tag (out c) (left c) (right c)) ∈ FP :=
  pairDataBits_mem_FP (constFn_mem_FP _) (pairDataBits_mem_FP (Codec.unary_toBits_mem_FP ho)
    (pairDataBits_mem_FP (Codec.unary_toBits_mem_FP hl) (Codec.unary_toBits_mem_FP hr)))

theorem zeroGateBits_mem_FP {wire : List Bool → ℕ} (hw : UnaryFn wire) :
    (fun c => zeroGateBits (wire c)) ∈ FP :=
  pairDataBits_mem_FP (constFn_mem_FP _) (Codec.unary_toBits_mem_FP hw)

theorem constantGateBits_encode (out : ℕ) (z : ℤ) :
    constantGateBits out (Term.const z).toData.toBits = (Gate.constant out z).encode := by
  simp only [constantGateBits, pairDataBits_toBits, Gate.encode, Gate.toData]

theorem addGateBits_encode (out left right : ℕ) :
    arithmeticGateBits 1 out left right = (Gate.add out left right).encode := by
  simp only [arithmeticGateBits, pairDataBits_toBits, Gate.encode, Gate.toData]

theorem mulGateBits_encode (out left right : ℕ) :
    arithmeticGateBits 2 out left right = (Gate.mul out left right).encode := by
  simp only [arithmeticGateBits, pairDataBits_toBits, Gate.encode, Gate.toData]

theorem zeroGateBits_encode (wire : ℕ) : zeroGateBits wire = (Gate.zero wire).encode := by
  simp only [zeroGateBits, pairDataBits_toBits, Gate.encode, Gate.toData]

end LeanCanny.ETR.ComplexCircuit
