/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.SumSquaresFP

/-!
# Polynomial-time writers for fresh-witness and selector equations

The term argument is already serialized; integer payloads are copied verbatim.
Indices are supplied through the polynomial-time unary-number interface, so
writing a unary variable index cannot hide an exponential expansion.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open Turing.MultiTapeTM


def nonzeroBits (term : List Bool) (i : ℕ) : List Bool :=
  Codec.taggedTwo 2 (Codec.taggedTwo 3 term (variableBits i)) (const (-1)).toData.toBits

def negativeBits (term : List Bool) (i : ℕ) : List Bool :=
  Codec.taggedTwo 2
    (Codec.taggedTwo 3 term (Codec.taggedTwo 3 (variableBits i) (variableBits i)))
    (const 1).toData.toBits

def nonnegativeBits (term : List Bool) (i : ℕ) : List Bool :=
  Codec.taggedTwo 2 term
    (Codec.taggedTwo 3 (const (-1)).toData.toBits
      (Codec.taggedTwo 3 (variableBits i) (variableBits i)))

def oneMinusBits (i : ℕ) : List Bool :=
  Codec.taggedTwo 2 (const 1).toData.toBits
    (Codec.taggedTwo 3 (const (-1)).toData.toBits (variableBits i))

def booleanBits (i : ℕ) : List Bool :=
  Codec.taggedTwo 3 (variableBits i)
    (Codec.taggedTwo 2 (variableBits i) (const (-1)).toData.toBits)

@[program_certificate]
theorem nonzeroBits_mem_FP {term : List Bool → List Bool} {i : List Bool → ℕ}
    (ht : ComputableTidilyInPolyTime term encBits encBits)
    (hi : ComputableTidilyInPolyTime i encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => nonzeroBits (term z) (i z)) encBits encBits :=
  Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 ht (variableBits_mem_FP hi))
    (constFn_mem_FP (const (-1)).toData.toBits)

@[program_certificate]
theorem negativeBits_mem_FP {term : List Bool → List Bool} {i : List Bool → ℕ}
    (ht : ComputableTidilyInPolyTime term encBits encBits)
    (hi : ComputableTidilyInPolyTime i encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => negativeBits (term z) (i z)) encBits encBits :=
  Codec.taggedTwo_mem_FP 2
    (Codec.taggedTwo_mem_FP 3 ht
      (Codec.taggedTwo_mem_FP 3 (variableBits_mem_FP hi) (variableBits_mem_FP hi)))
    (constFn_mem_FP (const 1).toData.toBits)

@[program_certificate]
theorem nonnegativeBits_mem_FP {term : List Bool → List Bool} {i : List Bool → ℕ}
    (ht : ComputableTidilyInPolyTime term encBits encBits)
    (hi : ComputableTidilyInPolyTime i encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => nonnegativeBits (term z) (i z)) encBits encBits :=
  Codec.taggedTwo_mem_FP 2 ht
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (const (-1)).toData.toBits)
      (Codec.taggedTwo_mem_FP 3 (variableBits_mem_FP hi) (variableBits_mem_FP hi)))

theorem oneMinusBits_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) :
    (fun z => oneMinusBits (i z)) ∈ FP :=
  Codec.taggedTwo_mem_FP 2 (constFn_mem_FP (const 1).toData.toBits)
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (const (-1)).toData.toBits) (variableBits_mem_FP hi))

theorem booleanBits_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) :
    (fun z => booleanBits (i z)) ∈ FP :=
  Codec.taggedTwo_mem_FP 3 (variableBits_mem_FP hi)
    (Codec.taggedTwo_mem_FP 2 (variableBits_mem_FP hi) (constFn_mem_FP (const (-1)).toData.toBits))

@[simp] theorem nonzeroBits_toBits (t : Term) (i : ℕ) :
    nonzeroBits t.toData.toBits i = (t.nonzeroEquation i).toData.toBits := by
  simp only [nonzeroBits, nonzeroEquation, add_toBits, mul_toBits, variableBits_eq]

@[simp] theorem negativeBits_toBits (t : Term) (i : ℕ) :
    negativeBits t.toData.toBits i = (t.negativeEquation i).toData.toBits := by
  simp only [negativeBits, negativeEquation, square, add_toBits, mul_toBits, variableBits_eq]

@[simp] theorem nonnegativeBits_toBits (t : Term) (i : ℕ) :
    nonnegativeBits t.toData.toBits i = (t.nonnegativeEquation i).toData.toBits := by
  simp only [nonnegativeBits, nonnegativeEquation, square, add_toBits, mul_toBits, variableBits_eq]

@[simp] theorem oneMinusBits_toBits (i : ℕ) : oneMinusBits i = (oneMinus i).toData.toBits := by
  simp only [oneMinusBits, oneMinus, add_toBits, mul_toBits, variableBits_eq]

@[simp] theorem booleanBits_toBits (i : ℕ) : booleanBits i = (booleanEquation i).toData.toBits := by
  simp only [booleanBits, booleanEquation, add_toBits, mul_toBits, variableBits_eq]

@[simp] theorem variableBits_length (i : ℕ) : (variableBits i).length = 2 * i + 8 := by
  simp only [variableBits_eq, Data.length_toBits, dataSize_var]

@[simp] theorem nonzeroBits_length (term : List Bool) (i : ℕ) :
    (nonzeroBits term i).length = term.length + 2 * i + 38 := by
  simp only [nonzeroBits, SumSquares.taggedTwo_length, variableBits_length,
    Data.length_toBits, dataSize_const_neg_one]
  omega

@[simp] theorem negativeBits_length (term : List Bool) (i : ℕ) :
    (negativeBits term i).length = term.length + 4 * i + 58 := by
  simp only [negativeBits, SumSquares.taggedTwo_length, variableBits_length,
    Data.length_toBits, dataSize_const_one]
  omega

@[simp] theorem nonnegativeBits_length (term : List Bool) (i : ℕ) :
    (nonnegativeBits term i).length = term.length + 4 * i + 56 := by
  simp only [nonnegativeBits, SumSquares.taggedTwo_length, variableBits_length,
    Data.length_toBits, dataSize_const_neg_one]
  omega

@[simp] theorem oneMinusBits_length (i : ℕ) : (oneMinusBits i).length = 2 * i + 52 := by
  rw [oneMinusBits_toBits, Data.length_toBits, dataSize_oneMinus]

@[simp] theorem booleanBits_length (i : ℕ) : (booleanBits i).length = 4 * i + 46 := by
  rw [booleanBits_toBits, Data.length_toBits, dataSize_booleanEquation]

end LeanCanny.ETR.Term
