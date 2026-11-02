/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationCoefficientSpace
public import LeanCanny.Algebra.MonicParameterNativeLower
public import LeanCanny.Algebra.FixedWidthPowerMonomial

/-! # Native newest-first scalar-row query controls

Only original dimensions, widths and the fixed global power schedule enter
the query. Scalar exponents and indices remain binary. The full old source
and arbitrary caller modulus are retained in the coefficient request.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open PaddedIntegralGeneratorSource UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def scalarDegree (S : Source) (c : List Bool) := 2^S.width c
def birthPower (S : Source) (cap : List Bool→ℕ) (c : List Bool) :=
  birth (cap c) (scalarDegree S c) (S.arity c)
def newExponent (V : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :=
  Nat.fromBitsLE ((target c).take (V c))
def selectedPower (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :=
  newExponent V target c / birthPower S cap c

def coefficientContext (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :=
  pair c (BinaryNatCode.encode (selectedPower S cap V target c))

def tailTarget (V : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) := (target c).drop (V c)

def Active (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) : Prop :=
  newExponent V target c % birthPower S cap c=0 ∧ selectedPower S cap V target c<scalarDegree S c

instance (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool) :
    DecidablePred (Active S cap V target) := fun _=>inferInstanceAs (Decidable (_ ∧ _))

theorem scalarDegree_binary (S : Source) (hw : UnaryFn S.width) : BinaryFn (scalarDegree S) :=
  (BinaryFn.const 2).powUnary hw

theorem birthPower_binary (S : Source) (cap : List Bool→ℕ)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) : BinaryFn (birthPower S cap) :=
  birth_binary hc (scalarDegree_binary S hw) ha

theorem newExponent_binary (V : List Bool→ℕ) (target : List Bool→List Bool)
    (hV : UnaryFn V) (ht : target∈FP) : BinaryFn (newExponent V target) :=
  BinaryFn.fromBits (take_mem_FP ht hV)

theorem selectedPower_binary (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V) (ht : target∈FP) :
    BinaryFn (selectedPower S cap V target) :=
  (newExponent_binary V target hV ht).div (birthPower_binary S cap hc ha hw)

theorem coefficientContext_FP (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V) (ht : target∈FP) :
    coefficientContext S cap V target∈FP :=
  mem_FP_pair id_mem_FP (selectedPower_binary S cap V target hc ha hw hV ht).bits_mem_FP

theorem tailTarget_FP (V : List Bool→ℕ) (target : List Bool→List Bool) (hV : UnaryFn V) (ht : target∈FP) :
    tailTarget V target∈FP := drop_mem_FP ht hV

theorem active_FP (S : Source) (cap V : List Bool→ℕ) (target : List Bool→List Bool)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V) (ht : target∈FP) :
    FPPred (Active S cap V target) :=
  (((newExponent_binary V target hV ht).mod (birthPower_binary S cap hc ha hw)).eq (BinaryFn.const 0)).and
    ((selectedPower_binary S cap V target hc ha hw hV ht).lt (scalarDegree_binary S hw))

theorem newExponent_eq (V : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :
    newExponent V target c=entry (V c) (Nat.fromBitsLE (target c)) 0 := by
  rw [entry_eq_digit]
  simp only [Nat.zero_mul,pow_zero,Nat.div_one,newExponent,BinaryNat.value_take]

end LeanCanny.Algebra.PaddedIntegralRowBits
