/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialCoefficientFP
public import LeanCanny.ETR.MonomialExponentFP
public import LeanCanny.ETR.IndexedExpansionSize
public import LeanCanny.Algebra.RationalSubstitutionSign

/-!
# The complete encoded ETR source for streamed rational substitution

An FP term field and arity allowance determine the actual indexed source.
All source metadata, exponents, and coefficient residues are implemented.
Only coordinate coefficient routines and their semantic contracts are supplied
by the caller. The clearing width is twice the validated term's literal size.
-/

@[expose] public section

namespace LeanCanny.ETR.RationalSubstitutionBits

open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Algebra
open LeanCanny.Algebra.RationalSubstitution.IntegerBits
open Polynomial

structure Source where
  term : List Bool → List Bool
  arity : List Bool → List Bool
  scope : ∀ c, (TermView.term (term c)).arity ≤ Nat.fromBitsLE (arity c)

structure Source.PolyTime (S : Source) : Prop where
  term : S.term ∈ FP
  arity : S.arity ∈ FP

noncomputable def Source.syntax (S : Source) (c : List Bool) : Term := TermView.term (S.term c)
def Source.normalized (S : Source) : List Bool → List Bool := TermView.normalize ∘ S.term
def Source.sizeCode (S : Source) (c : List Bool) : List Bool := BinaryNatCode.encode (S.normalized c).length
def Source.widthCode (S : Source) (c : List Bool) : List Bool := BinaryNat.add (pair (S.sizeCode c) (S.sizeCode c))
def Source.countCode (S : Source) : List Bool → List Bool := MonomialCount.read ∘ S.normalized

theorem Source.normalized_eq (S : Source) (c : List Bool) : S.normalized c = (S.syntax c).toData.toBits :=
  TermView.normalize_eq_term (S.term c)

theorem Source.sizeCode_eq (S : Source) (c : List Bool) : S.sizeCode c = BinaryNatCode.encode (S.syntax c).toData.size := by
  rw [Source.sizeCode, S.normalized_eq, Data.length_toBits]

theorem Source.widthCode_eq (S : Source) (c : List Bool) :
    S.widthCode c = BinaryNatCode.encode (2 * (S.syntax c).toData.size) := by
  simp only [Source.widthCode, S.sizeCode_eq, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, two_mul]

theorem Source.countCode_eq (S : Source) (c : List Bool) :
    S.countCode c = BinaryNatCode.encode (S.syntax c).monomialCount := by
  rw [Source.countCode, Function.comp_apply, S.normalized_eq, MonomialCount.read_term]

theorem Source.normalized_mem_FP (S : Source) (hS : S.PolyTime) : S.normalized ∈ FP :=
  mem_FP_comp hS.term TermView.normalize_mem_FP

theorem Source.sizeCode_mem_FP (S : Source) (hS : S.PolyTime) : S.sizeCode ∈ FP :=
  bits_mem_FP (UnaryFn.length (S.normalized_mem_FP hS))

theorem Source.widthCode_mem_FP (S : Source) (hS : S.PolyTime) : S.widthCode ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (S.sizeCode_mem_FP hS) (S.sizeCode_mem_FP hS)) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := S.widthCode) h (fun _ => rfl)

theorem Source.countCode_mem_FP (S : Source) (hS : S.PolyTime) : S.countCode ∈ FP :=
  mem_FP_comp (S.normalized_mem_FP hS) MonomialCount.read_mem_FP

/-- Literal input size is always a valid arity allowance. -/
noncomputable def Source.ofTerm (term : List Bool → List Bool) : Source where
  term := term
  arity := fun c => BinaryNatCode.encode (TermView.normalize (term c)).length
  scope := fun c => by
    simp only [TermView.normalize_eq_term, Data.length_toBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (TermView.term (term c)).arity_le_dataSize

theorem Source.ofTerm_polyTime {term : List Bool → List Bool} (ht : term ∈ FP) : (Source.ofTerm term).PolyTime := by
  constructor
  · exact ht
  · exact bits_mem_FP (UnaryFn.length (mem_FP_comp ht TermView.normalize_mem_FP))

noncomputable def Source.family (S : Source) (np dp : List Bool → ℕ → ℤ[X]) : Family where
  arity := fun c => Nat.fromBitsLE (S.arity c)
  width := fun c => 2 * (S.syntax c).toData.size
  terms := fun c => (S.syntax c).monomialCount
  exponent := fun c => (S.syntax c).monomialExponent
  coefficient := fun c => (S.syntax c).monomialCoefficient
  numerator := np
  denominator := dp
  exponent_le := fun c r _ i _ => by
    have hdegree := (S.syntax c).monomialExponent_le r i
    have hsize := (S.syntax c).degreeBound_le_dataSize
    omega

noncomputable def Source.access (S : Source) (np dp : List Bool → ℕ → ℤ[X]) (n d : List Bool → List Bool)
    (hn : ∀ c i, i < Nat.fromBitsLE (S.arity c) → ∀ k m, 0 < m →
      n (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
        Algebra.MatrixPower.residueBits (((np c i).coeff k : ℤ) : ZMod m))
    (hd : ∀ c i, i < Nat.fromBitsLE (S.arity c) → ∀ k m, 0 < m →
      d (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
        Algebra.MatrixPower.residueBits (((dp c i).coeff k : ℤ) : ZMod m)) : Access (S.family np dp) where
  arity := S.arity
  width := S.widthCode
  terms := S.countCode
  exponent := MonomialReader.sourceExponent S.term
  coefficient := MonomialReader.sourceCoefficient S.term
  numerator := n
  denominator := d
  arity_eq := fun _ => rfl
  width_eq := fun c => by simp only [S.widthCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits, Source.family]
  terms_eq := fun c => by simp only [S.countCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits, Source.family]
  exponent_eq := fun c r _ i _ => by
    rw [MonomialReader.sourceExponent_packet S.term c r i]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Source.family, Source.syntax]
  coefficient_eq := fun c r _ m hm => MonomialReader.sourceCoefficient_packet S.term c r m hm
  numerator_eq := hn
  denominator_eq := hd

theorem Source.access_controls (S : Source) (hS : S.PolyTime) (np dp : List Bool → ℕ → ℤ[X])
    (n d : List Bool → List Bool) (hn hd) : (S.access np dp n d hn hd).ControlsPolyTime :=
  ⟨hS.arity, S.widthCode_mem_FP hS, S.countCode_mem_FP hS, MonomialReader.sourceExponent_mem_FP hS.term⟩

end LeanCanny.ETR.RationalSubstitutionBits
