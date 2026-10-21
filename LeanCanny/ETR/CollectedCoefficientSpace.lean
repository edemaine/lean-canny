/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficientQuery
public import LeanCanny.ETR.MonomialCoefficientFP
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Polynomial-space access to collected integer polynomial coefficients

The summand reader checks the full exponent vector, then reads one indexed
integer coefficient modulo the requested positive modulus. A streamed sum
collects repeated monomials. Saved inputs and child computations are included
in the space bound. All source, target, and modulus fields are total FP maps.
-/

@[expose] public section

namespace LeanCanny.ETR.CollectedCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Algebra.MatrixPower
open scoped BigOperators

noncomputable def summand (source target modulus : List Bool → List Bool) (q : List Bool) : List Bool := by
  classical
  exact if Matches source target q then
    MonomialReader.coefficientRead (source ∘ pairFst) pairSnd (modulus ∘ pairFst) q else []

theorem summand_mem_FP {source target modulus : List Bool → List Bool}
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : summand source target modulus ∈ FP := by
  classical
  have hread := MonomialReader.coefficientRead_mem_FP (mem_FP_comp pairFst_mem_FP hs) pairSnd_mem_FP
    (mem_FP_comp pairFst_mem_FP hm)
  exact (matches_fppred hs ht).ite_mem_FP hread (constFn_mem_FP [])

def count (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  MonomialCount.read (TermView.normalize (source c))

theorem count_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : count source ∈ FP :=
  mem_FP_comp (mem_FP_comp hs TermView.normalize_mem_FP) MonomialCount.read_mem_FP

theorem count_code (source : List Bool → List Bool) (c : List Bool) :
    count source c = BinaryNatCode.encode (TermView.term (source c)).monomialCount := by
  rw [count, TermView.normalize_eq_term, MonomialCount.read_term]

theorem summand_packet (source target modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    summand source target modulus (pair c (BinaryNatCode.encode r)) =
      residueBits (if ∀ i < dimension source c, (TermView.term (source c)).monomialExponent r i = exponent source target c i
        then ((TermView.term (source c)).monomialCoefficient r : ZMod (Nat.fromBitsLE (modulus c) + 1)) else 0) := by
  classical
  simp only [summand, Matches, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs
  · rw [MonomialReader.coefficientRead_correct]
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits]
    rfl
  · simp [residueBits, BinaryNatCode.encode]

noncomputable def value (source target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((coefficient source target c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator (source target modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (value source target modulus) := by
  classical
  let a := fun (c : List Bool) (r : ℕ) =>
    if ∀ i < dimension source c, (TermView.term (source c)).monomialExponent r i = exponent source target c i
    then ((TermView.term (source c)).monomialCoefficient r : ZMod (Nat.fromBitsLE (modulus c) + 1)) else 0
  let E := Algebra.ModularSum.evaluatorWithModulus
    (SpaceFunction.ofFP _ (summand_mem_FP hs ht hm)) (count source) (BinaryNat.succ ∘ modulus)
    (count_mem_FP hs) (mem_FP_comp hm BinaryNat.succ_mem_FP)
    (fun c => Nat.fromBitsLE (modulus c) + 1)
    (by funext c; simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits])
    a (fun _ => by omega) (fun c r _ => summand_packet source target modulus c r)
  refine E.congr (funext fun c => ?_)
  rw [count_code]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold value coefficient
  rw [Term.finitePolynomial_coeff _ _ (arity_le_dimension source c)]
  congr 1
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, a]

end LeanCanny.ETR.CollectedCoefficient
