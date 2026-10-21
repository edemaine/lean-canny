/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficientSpace
public import LeanCanny.ETR.PolynomialMass
public import LeanCanny.Algebra.IntegerSignSpace

/-! # Polynomial-space signs of collected source coefficients

The actual integer coefficient has at most N+1 magnitude bits for validated
source length N. The residue evaluator and this FP budget instantiate the
certified CRT integer-sign routine, with no coefficient oracle assumption.
-/

@[expose] public section

namespace LeanCanny.ETR.CollectedCoefficient

open LeanCanny.Encoding LeanCanny.Computation
open Algebra.MatrixPower

def budget (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (dimension source c + 1)

theorem budget_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : budget source ∈ FP :=
  bits_mem_FP ((dimension_unary hs).add (UnaryFn.const 1))

theorem coefficient_bits (source target : List Bool → List Bool) (c : List Bool) :
    (coefficient source target c).natAbs.size ≤ Nat.fromBitsLE (budget source c) := by
  have hmass := (TermView.term (source c)).finitePolynomial_mass (dimension source c)
  have hd : (TermView.term (source c)).toData.size = dimension source c := by
    rw [dimension, TermView.normalize_eq_term, Data.length_toBits]
  have h := Nat.size_le_size ((Algebra.MvMass.coeff_le _
    (Algebra.RationalSubstitution.Indexed.exponentVector (dimension source c) (exponent source target c))).trans hmass)
  simpa only [coefficient, hd, Nat.size_pow, budget, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

theorem residue_packet (source target : List Bool → List Bool) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    value (source ∘ pairFst) (target ∘ pairFst) pairSnd (pair c (BinaryNatCode.encode (m - 1))) =
      residueBits ((coefficient source target c : ℤ) : ZMod m) := by
  have he : exponent (source ∘ pairFst) (target ∘ pairFst) (pair c (BinaryNatCode.encode (m - 1))) =
      exponent source target c := by
    funext i
    simp only [exponent, block, dimension, Function.comp_apply, pairFst_pair]
  have hd : dimension (source ∘ pairFst) (pair c (BinaryNatCode.encode (m - 1))) = dimension source c := by
    simp only [dimension, Function.comp_apply, pairFst_pair]
  have hc : coefficient (source ∘ pairFst) (target ∘ pairFst) (pair c (BinaryNatCode.encode (m - 1))) =
      coefficient source target c := by
    unfold coefficient
    rw [hd, he]
    simp only [Function.comp_apply, pairFst_pair]
  unfold value
  rw [hc, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

theorem negativeEvaluator (source target : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) :
    SpaceFunction (fun c => if coefficient source target c < 0 then [true] else []) := by
  let R := evaluator (source ∘ pairFst) (target ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP hs) (mem_FP_comp pairFst_mem_FP ht) pairSnd_mem_FP
  exact Algebra.IntegerSignBits.evaluator R (budget source) (budget_mem_FP hs) (coefficient source target)
    (coefficient_bits source target) (residue_packet source target)

theorem negativeLanguage_mem_PSPACE (source target : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) : {c | coefficient source target c < 0} ∈ PSPACE := by
  let R := evaluator (source ∘ pairFst) (target ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP hs) (mem_FP_comp pairFst_mem_FP ht) pairSnd_mem_FP
  exact Algebra.IntegerSignBits.negativeLanguage_mem_PSPACE R (budget source) (budget_mem_FP hs)
    (coefficient source target) (coefficient_bits source target) (residue_packet source target)

end LeanCanny.ETR.CollectedCoefficient
