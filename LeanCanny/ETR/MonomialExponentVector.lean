/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficientQuery
public import LeanCanny.Encoding.FixedWidthNatVectorFP

/-! # FP exponent-vector queries for indexed source monomials

Writing one selected monomial's entire exponent vector still has polynomial
output length. Its coordinates fit in the fixed width used by collected
coefficient queries, so decoding recovers the exact exponent vector.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding

noncomputable def exponentVectorWord (source index : List Bool → List Bool) (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (CollectedCoefficient.dimension source c) (CollectedCoefficient.dimension source c + 1)
    ((TermView.term (source c)).monomialExponent (Nat.fromBitsLE (index c)))

theorem exponentVectorWord_mem_FP {source index : List Bool → List Bool} (hs : source ∈ FP) (hi : index ∈ FP) :
    exponentVectorWord source index ∈ FP := by
  let read := exponentRead (source ∘ pairFst) (index ∘ pairFst) pairSnd
  have hr : read ∈ FP := exponentRead_mem_FP (mem_FP_comp pairFst_mem_FP hs)
    (mem_FP_comp pairFst_mem_FP hi) pairSnd_mem_FP
  apply FixedWidthNatVector.encode_of_coordinate (CollectedCoefficient.dimension_unary hs)
    ((CollectedCoefficient.dimension_unary hs).add (UnaryFn.const 1))
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary
  apply FixedWidthNatVector.coordinate_of_reader
    (e := fun c => (TermView.term (source c)).monomialExponent (Nat.fromBitsLE (index c))) hr
  intro c i
  simp only [read, exponentRead_correct, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem monomialExponent_fits (source : List Bool → List Bool) (c : List Bool) (r i : ℕ) :
    (TermView.term (source c)).monomialExponent r i < 2 ^ (CollectedCoefficient.dimension source c + 1) := by
  have hd := ((TermView.term (source c)).monomialExponent_le r i).trans
    (TermView.term (source c)).degreeBound_le_dataSize
  have he : (TermView.term (source c)).toData.size = CollectedCoefficient.dimension source c := by
    rw [CollectedCoefficient.dimension, TermView.normalize_eq_term, Data.length_toBits]
  rw [he] at hd
  exact hd.trans_lt ((Nat.lt_two_pow_self : CollectedCoefficient.dimension source c < 2 ^ CollectedCoefficient.dimension source c).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))

theorem coefficient_at_exponentVectorWord (source index : List Bool → List Bool) (c : List Bool) :
    CollectedCoefficient.coefficient source (exponentVectorWord source index) c =
      (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c))).coeff
        (Algebra.RationalSubstitution.Indexed.exponentVector (CollectedCoefficient.dimension source c)
          ((TermView.term (source c)).monomialExponent (Nat.fromBitsLE (index c)))) := by
  exact CollectedCoefficient.coefficient_eq_of_encoded_target source (exponentVectorWord source index) c _ rfl
    (fun i _ => monomialExponent_fits source c _ i)

end LeanCanny.ETR.MonomialReader
