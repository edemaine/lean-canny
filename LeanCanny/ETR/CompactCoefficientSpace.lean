/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CompactCoefficientQuery
public import LeanCanny.Algebra.ModularProductSpace
public import LeanCanny.Geometry.CubeCoefficientFormula

/-! # Polynomial-space compactification coefficient access

A coordinate product calls the actual source-degree evaluator and the binomial
residue evaluator. A source-term sum then collects all contributions to the
coefficient of the denominator-cleared polynomial, including cancellation.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Algebra.MatrixPower
open scoped BigOperators

attribute [local irreducible] BinaryNat.succ BinaryNat.mulMod

def reassociate (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (BinaryNat.normalize (pairSnd (pairFst p))) (pairSnd p))

theorem reassociate_mem_FP : reassociate ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP) pairSnd_mem_FP)

noncomputable def factor (source target : List Bool → List Bool) (c : List Bool) (r i : ℕ) : ℤ :=
  (Algebra.CubeFactor.polynomial (R := ℤ) ((TermView.term (source c)).monomialExponent r i)
    (2 * Term.indexedDegree (TermView.term (source c)) (CollectedCoefficient.dimension source c) i -
      (TermView.term (source c)).monomialExponent r i)).coeff (exponent source target c i)

theorem factor_packet (source target modulus : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < CollectedCoefficient.dimension source c) :
    factorComputed source target modulus (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      residueBits ((factor source target c r i : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  rw [factorComputed_packet source target modulus c r i hi]
  unfold factor
  rw [Term.indexedDegree_eq_degreeOf _ _ (CollectedCoefficient.arity_le_dimension source c) ⟨i, hi⟩]

noncomputable def coordinateProduct (source target modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (∏ i ∈ Finset.range (CollectedCoefficient.dimension source (pairFst q)),
    ((factor source target (pairFst q) (Nat.fromBitsLE (pairSnd q)) i : ℤ) :
      ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))

noncomputable def productEvaluator (source target modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (coordinateProduct source target modulus) := by
  let count := fun q => BinaryNatCode.encode (CollectedCoefficient.dimension source (pairFst q))
  have hc : count ∈ FP := bits_mem_FP ((CollectedCoefficient.dimension_unary hs).lift)
  let m := fun q => Nat.fromBitsLE (modulus (pairFst q)) + 1
  let a := fun q i => ((factor source target (pairFst q) (Nat.fromBitsLE (pairSnd q)) i : ℤ) : ZMod (m q))
  let E := Algebra.ModularProduct.evaluatorWithModulus
    ((factorEvaluator source target modulus hs ht hm).precompose reassociate reassociate_mem_FP)
    count (BinaryNat.succ ∘ modulus ∘ pairFst) hc
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP)
    m (by funext q; simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]; rfl)
    a (fun _ => by dsimp [m]; omega) (by
      intro q i hi
      have hi' : i < CollectedCoefficient.dimension source (pairFst q) := by
        simpa only [count, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi
      simp only [Function.comp_apply, reassociate, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
      simpa only [BinaryNatCode.encode] using
        factor_packet source target modulus (pairFst q) (Nat.fromBitsLE (pairSnd q)) i hi')
  exact E.congr (funext fun q => by simp only [count, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

def finishSummand (source modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNat.succ (modulus (pairFst (pairFst z))))
    (pair (MonomialReader.coefficientRead (source ∘ pairFst) pairSnd (modulus ∘ pairFst) (pairFst z)) (pairSnd z)))

theorem finishSummand_mem_FP {source modulus : List Bool → List Bool}
    (hs : source ∈ FP) (hm : modulus ∈ FP) : finishSummand source modulus ∈ FP := by
  have hc := MonomialReader.coefficientRead_mem_FP (mem_FP_comp pairFst_mem_FP hs) pairSnd_mem_FP
    (mem_FP_comp pairFst_mem_FP hm)
  have hm' := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm' (mem_FP_pair (mem_FP_comp pairFst_mem_FP hc) pairSnd_mem_FP)) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

noncomputable def summand (source target modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  finishSummand source modulus (pair q (coordinateProduct source target modulus q))

noncomputable def summandEvaluator (source target modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (summand source target modulus) := by
  let E := (productEvaluator source target modulus hs ht hm).withInput.postcompose
    (finishSummand source modulus) (finishSummand_mem_FP hs hm)
  exact E.congr (funext fun _ => rfl)

theorem summand_correct (source target modulus : List Bool → List Bool) (q : List Bool) :
    summand source target modulus q = residueBits
      (((TermView.term (source (pairFst q))).monomialCoefficient (Nat.fromBitsLE (pairSnd q)) *
        ∏ i ∈ Finset.range (CollectedCoefficient.dimension source (pairFst q)),
          factor source target (pairFst q) (Nat.fromBitsLE (pairSnd q)) i : ℤ) :
            ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)) := by
  rw [summand, finishSummand, pairFst_pair, pairSnd_pair, MonomialReader.coefficientRead_correct]
  simp only [Function.comp_apply]
  change BinaryNat.mulMod (pair (BinaryNat.succ (modulus (pairFst q)))
    (pair (residueBits _) (coordinateProduct source target modulus q))) = _
  rw [BinaryNat.succ_eq_bits]
  change BinaryNat.mulMod (pair (BinaryNatCode.encode _) (pair (residueBits _) (residueBits _))) = _
  rw [ArithmeticBits.mulMod_residueBits]
  simp only [Int.cast_mul, Int.cast_prod]

noncomputable def coefficient (source target : List Bool → List Bool) (c : List Bool) : ℤ :=
  (Geometry.CubePolynomial.cleared
    (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c)))).coeff
      (Algebra.RationalSubstitution.Indexed.exponentVector (CollectedCoefficient.dimension source c) (exponent source target c))

theorem coefficient_eq_of_encoded_target (source target : List Bool → List Bool) (c : List Bool) (e : ℕ → ℕ)
    (ht : target c = FixedWidthNatVector.encode (CollectedCoefficient.dimension source c) (width source c) e)
    (he : ∀ i < CollectedCoefficient.dimension source c, e i < 2 ^ width source c) :
    coefficient source target c =
      (Geometry.CubePolynomial.cleared
        (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c)))).coeff
          (Algebra.RationalSubstitution.Indexed.exponentVector (CollectedCoefficient.dimension source c) e) := by
  unfold coefficient
  congr 1
  apply (Term.exponentVector_eq_iff _ _ _).mpr
  intro i hi
  rw [exponent, ht]
  exact FixedWidthNatVector.decode_block _ _ e i hi (he i hi)

theorem coefficient_eq_sum (source target : List Bool → List Bool) (c : List Bool) :
    coefficient source target c = ∑ r ∈ Finset.range (TermView.term (source c)).monomialCount,
      (TermView.term (source c)).monomialCoefficient r *
        ∏ i ∈ Finset.range (CollectedCoefficient.dimension source c), factor source target c r i := by
  unfold coefficient
  rw [Geometry.CubePolynomial.coeff_cleared_finitePolynomial _ _ (CollectedCoefficient.arity_le_dimension source c)]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (factor source target c r)]
  apply Finset.prod_congr rfl
  intro i _
  unfold factor
  rw [Term.indexedDegree_eq_degreeOf _ _ (CollectedCoefficient.arity_le_dimension source c) i]

noncomputable def value (source target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((coefficient source target c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def evaluator (source target modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (value source target modulus) := by
  let a := fun (c : List Bool) (r : ℕ) =>
    (((TermView.term (source c)).monomialCoefficient r *
      ∏ i ∈ Finset.range (CollectedCoefficient.dimension source c), factor source target c r i : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1))
  let E := Algebra.ModularSum.evaluatorWithModulus (summandEvaluator source target modulus hs ht hm)
    (CollectedCoefficient.count source) (BinaryNat.succ ∘ modulus)
    (CollectedCoefficient.count_mem_FP hs) (mem_FP_comp hm BinaryNat.succ_mem_FP)
    (fun c => Nat.fromBitsLE (modulus c) + 1)
    (by funext c; simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits])
    a (fun _ => by omega) (by
      intro c r _
      have h := summand_correct source target modulus (pair c (BinaryNatCode.encode r))
      rw [pairFst_pair, pairSnd_pair] at h
      simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, a] using h)
  refine E.congr (funext fun c => ?_)
  rw [CollectedCoefficient.count_code]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, coefficient_eq_sum]
  simp only [Int.cast_sum, a]

end LeanCanny.ETR.CompactCoefficient
