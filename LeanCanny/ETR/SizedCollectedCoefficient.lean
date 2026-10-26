/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficientSpace
public import LeanCanny.Encoding.FixedWidthQuery

/-! # Collected coefficients with explicit dimension and block width

The matcher scans exactly the requested spatial dimension. Neither the
exponent width nor the variable count is tied to the serialized term length.
-/

@[expose] public section
namespace LeanCanny.ETR.SizedCollectedCoefficient
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Encoding.Brackets
open Algebra.RationalSubstitution.Indexed Algebra.MatrixPower
open scoped Classical BigOperators

def Matches (A W : List Bool → ℕ) (source target : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i < A (pairFst q),
    (TermView.term (source (pairFst q))).monomialExponent (Nat.fromBitsLE (pairSnd q)) i =
      FixedWidthQuery.coordinate W target (pairFst q) i

private def atom (W : List Bool → ℕ) (source target : List Bool → List Bool) (z : List Bool) : Prop :=
  (TermView.term (source (pairFst (pairFst z)))).monomialExponent
    (Nat.fromBitsLE (pairSnd (pairFst z))) (pairSnd z).length =
      FixedWidthQuery.coordinate W target (pairFst (pairFst z)) (pairSnd z).length

private theorem atom_fppred {W : List Bool → ℕ} {source target : List Bool → List Bool}
    (hW : UnaryFn W) (hs : source ∈ FP) (ht : target ∈ FP) : FPPred (atom W source target) := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hr := MonomialReader.exponentRead_mem_FP (mem_FP_comp hc hs)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (bits_mem_FP UnaryFn.index)
  have hw := hW.comp hc
  have hb := take_mem_FP (drop_mem_FP (mem_FP_comp hc ht) (UnaryFn.index.mul hw)) hw
  apply (stringEq_fppred hr (mem_FP_comp hb BinaryNat.normalize_mem_FP)).of_iff
  intro z
  simp only [MonomialReader.exponentRead_correct, Function.comp_apply, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, BinaryNat.normalize_eq_bits, atom, FixedWidthQuery.coordinate]
  exact BinaryNatCode.encode_injective.eq_iff

theorem matches_fppred {A W : List Bool → ℕ} {source target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : source ∈ FP) (ht : target ∈ FP) :
    FPPred (Matches A W source target) := by
  apply (FPPred.forall_lt (hA.comp pairFst_mem_FP) (atom_fppred hW hs ht)).of_iff
  intro q
  simp only [atom, Matches, pairFst_pair, pairSnd_pair, List.length_replicate]

noncomputable def summand (A W : List Bool → ℕ) (source target modulus : List Bool → List Bool)
    (q : List Bool) : List Bool :=
  if Matches A W source target q then
    MonomialReader.coefficientRead (source ∘ pairFst) pairSnd (modulus ∘ pairFst) q else []

theorem summand_mem_FP {A W : List Bool → ℕ} {source target modulus : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    summand A W source target modulus ∈ FP :=
  (matches_fppred hA hW hs ht).ite_mem_FP
    (MonomialReader.coefficientRead_mem_FP (mem_FP_comp pairFst_mem_FP hs) pairSnd_mem_FP
      (mem_FP_comp pairFst_mem_FP hm)) (constFn_mem_FP [])

noncomputable def value (A W : List Bool → ℕ) (source target modulus : List Bool → List Bool)
    (c : List Bool) : List Bool :=
  residueBits ((((TermView.term (source c)).finitePolynomial (A c)).coeff
    (exponentVector (A c) (FixedWidthQuery.coordinate W target c)) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator {A W : List Bool → ℕ} {source target modulus : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (source c)).arity ≤ A c) : SpaceFunction (value A W source target modulus) := by
  let a := fun (c : List Bool) (r : ℕ) =>
    if ∀ i < A c, (TermView.term (source c)).monomialExponent r i = FixedWidthQuery.coordinate W target c i
      then ((TermView.term (source c)).monomialCoefficient r : ZMod (Nat.fromBitsLE (modulus c) + 1)) else 0
  have E := Algebra.ModularSum.evaluatorWithModulus
    (SpaceFunction.ofFP _ (summand_mem_FP hA hW hs ht hm)) (CollectedCoefficient.count source) (BinaryNat.succ ∘ modulus)
    (CollectedCoefficient.count_mem_FP hs) (mem_FP_comp hm BinaryNat.succ_mem_FP)
    (fun c => Nat.fromBitsLE (modulus c) + 1)
    (by funext c; simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits])
    a (fun _ => by omega) (fun c r _ => by
      simp only [summand, Matches, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with h
      · rw [MonomialReader.coefficientRead_correct]
        simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits]
        simp only [a, ite_eq_left h]
        rfl
      · simp [a, residueBits, BinaryNatCode.encode, *])
  apply E.congr
  funext c
  rw [CollectedCoefficient.count_code]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold value
  rw [Term.finitePolynomial_coeff _ _ (ha c)]
  congr 1
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, a]

end LeanCanny.ETR.SizedCollectedCoefficient
