/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficients
public import LeanCanny.ETR.MonomialExponentFP
public import LeanCanny.Encoding.FixedWidthNatVector
public import LeanCanny.Tactic.PolyTime

/-! # FP exponent matching for collected coefficient queries

An exponent query uses fixed-width little-endian blocks. The dimension is
the validated source length and the width is one more than that dimension.
Short blocks are zero-padded by numeral decoding; extra blocks are ignored.
Matching an indexed monomial against the whole query is polynomial-time,
including for malformed source strings and noncanonical exponent words.
-/

@[expose] public section

namespace LeanCanny.ETR.CollectedCoefficient

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open Algebra.RationalSubstitution.Indexed

def dimension (source : List Bool → List Bool) (c : List Bool) : ℕ := (TermView.normalize (source c)).length
def block (source target : List Bool → List Bool) (c : List Bool) (i : ℕ) : List Bool :=
  ((target c).drop (i * (dimension source c + 1))).take (dimension source c + 1)
def exponent (source target : List Bool → List Bool) (c : List Bool) (i : ℕ) : ℕ :=
  Nat.fromBitsLE (block source target c i)

theorem dimension_unary {source : List Bool → List Bool} (hs : source ∈ FP) : UnaryFn (dimension source) :=
  UnaryFn.length (mem_FP_comp hs TermView.normalize_mem_FP)

theorem arity_le_dimension (source : List Bool → List Bool) (c : List Bool) :
    (TermView.term (source c)).arity ≤ dimension source c := by
  rw [dimension, TermView.normalize_eq_term, Data.length_toBits]
  exact Term.arity_le_dataSize _

noncomputable def coefficient (source target : List Bool → List Bool) (c : List Bool) : ℤ :=
  (Term.finitePolynomial (dimension source c) (TermView.term (source c))).coeff
    (exponentVector (dimension source c) (exponent source target c))

theorem coefficient_eq_of_encoded_target (source target : List Bool → List Bool) (c : List Bool) (e : ℕ → ℕ)
    (ht : target c = FixedWidthNatVector.encode (dimension source c) (dimension source c + 1) e)
    (he : ∀ i < dimension source c, e i < 2 ^ (dimension source c + 1)) :
    coefficient source target c = (Term.finitePolynomial (dimension source c) (TermView.term (source c))).coeff
      (exponentVector (dimension source c) e) := by
  unfold coefficient
  congr 1
  apply (Term.exponentVector_eq_iff _ _ _).mpr
  intro i hi
  rw [exponent, block, ht]
  exact FixedWidthNatVector.decode_block _ _ e i hi (he i hi)

def Matches (source target : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i < dimension source (pairFst q),
    (TermView.term (source (pairFst q))).monomialExponent (Nat.fromBitsLE (pairSnd q)) i =
      exponent source target (pairFst q) i

def atom (source target : List Bool → List Bool) (z : List Bool) : Prop :=
  (TermView.term (source (pairFst (pairFst z)))).monomialExponent
    (Nat.fromBitsLE (pairSnd (pairFst z))) (pairSnd z).length =
      exponent source target (pairFst (pairFst z)) (pairSnd z).length

theorem atom_fppred {source target : List Bool → List Bool} (hs : source ∈ FP) (ht : target ∈ FP) :
    FPPred (atom source target) := by
  have hctx := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hsrc := mem_FP_comp hctx hs
  have hindex := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hvar := bits_mem_FP UnaryFn.index
  have hread := MonomialReader.exponentRead_mem_FP hsrc hindex hvar
  have hw := ((dimension_unary hs).comp hctx).add (UnaryFn.const 1)
  have hslice := take_mem_FP (drop_mem_FP (mem_FP_comp hctx ht) (UnaryFn.index.mul hw)) hw
  have hnorm := mem_FP_comp hslice BinaryNat.normalize_mem_FP
  apply (stringEq_fppred hread hnorm).of_iff
  intro z
  simp only [MonomialReader.exponentRead_correct, Function.comp_apply, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, BinaryNat.normalize_eq_bits, atom, exponent, block]
  exact BinaryNatCode.encode_injective.eq_iff

theorem matches_fppred {source target : List Bool → List Bool} (hs : source ∈ FP) (ht : target ∈ FP) :
    FPPred (Matches source target) := by
  apply (FPPred.forall_lt ((dimension_unary hs).comp pairFst_mem_FP) (atom_fppred hs ht)).of_iff
  intro q
  simp only [atom, Matches, pairFst_pair, pairSnd_pair, List.length_replicate]

end LeanCanny.ETR.CollectedCoefficient
