/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CompactCoefficientSpace
public import LeanCanny.ETR.PolynomialMass
public import LeanCanny.Algebra.IntegerSignSpace

/-! # Polynomial-space signs of compactified coefficients

The coefficient mass bound supplies N+2*N²+1 magnitude bits. The complete
compactification residue evaluator instantiates CRT sign recovery on every
binary input, with no coefficient or actual-degree oracle.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactCoefficient

open LeanCanny.Encoding LeanCanny.Computation
open Algebra.MatrixPower

def budget (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2 + 1)

theorem budget_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : budget source ∈ FP :=
  bits_mem_FP (((CollectedCoefficient.dimension_unary hs).add
    ((UnaryFn.const 2).mul ((CollectedCoefficient.dimension_unary hs).pow_const 2))).add (UnaryFn.const 1))

theorem polynomial_mass (source : List Bool → List Bool) (c : List Bool) :
    Algebra.MvMass.mass (Geometry.CubePolynomial.cleared
      (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c)))) ≤
        2 ^ (CollectedCoefficient.dimension source c + 2 * CollectedCoefficient.dimension source c ^ 2) := by
  let N := CollectedCoefficient.dimension source c
  let t := TermView.term (source c)
  have ht : t.toData.size = N := by
    change (TermView.term (source c)).toData.size = CollectedCoefficient.dimension source c
    rw [CollectedCoefficient.dimension, TermView.normalize_eq_term, Data.length_toBits]
  have hd : (Term.finitePolynomial N t).totalDegree ≤ N := by
    exact (Term.totalDegree_finitePolynomial t N).trans (t.degreeBound_le_dataSize.trans_eq ht)
  have he : 2 * Fintype.card (Fin N) * (Term.finitePolynomial N t).totalDegree ≤ 2 * N ^ 2 := by
    rw [Fintype.card_fin, pow_two, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_left (2 * N) hd
  apply (Geometry.CubePolynomial.cleared_mass_of_degree (Term.finitePolynomial N t)).trans
  apply (Nat.mul_le_mul (t.finitePolynomial_mass N) (Nat.pow_le_pow_right (by decide) he)).trans
  rw [ht, ← pow_add]

theorem coefficient_bits (source target : List Bool → List Bool) (c : List Bool) :
    (coefficient source target c).natAbs.size ≤ Nat.fromBitsLE (budget source c) := by
  have h := Nat.size_le_size ((Algebra.MvMass.coeff_le _
    (Algebra.RationalSubstitution.Indexed.exponentVector (CollectedCoefficient.dimension source c)
      (exponent source target c))).trans (polynomial_mass source c))
  simpa only [coefficient, Nat.size_pow, budget, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

theorem residue_packet (source target : List Bool → List Bool) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    value (source ∘ pairFst) (target ∘ pairFst) pairSnd (pair c (BinaryNatCode.encode (m - 1))) =
      residueBits ((coefficient source target c : ℤ) : ZMod m) := by
  have he : exponent (source ∘ pairFst) (target ∘ pairFst) (pair c (BinaryNatCode.encode (m - 1))) =
      exponent source target c := by
    funext i
    simp only [exponent, width, CollectedCoefficient.dimension, Function.comp_apply, pairFst_pair]
  have hd : CollectedCoefficient.dimension (source ∘ pairFst) (pair c (BinaryNatCode.encode (m - 1))) = CollectedCoefficient.dimension source c := by
    simp only [CollectedCoefficient.dimension, Function.comp_apply, pairFst_pair]
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

end LeanCanny.ETR.CompactCoefficient
