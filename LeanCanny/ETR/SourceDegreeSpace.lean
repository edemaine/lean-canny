/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedDegreeSpace
public import LeanCanny.ETR.CompactSource
public import LeanCanny.ETR.FinitePolynomialPadding

/-! # Actual source degrees for compiled ETR in polynomial space

The input `pair bits variableIndex` requests a source variable's actual degree,
after collecting equal monomials and cancellation. Padding the source to its
encoded length preserves degrees of its original variables, so the result
gives precisely the degree used in the compactification denominator exponent.
-/

@[expose] public section

namespace LeanCanny.ETR.SourceDegree

open LeanCanny.Encoding LeanCanny.Computation

-- Keep FP field checking from unfolding the equation compiler.
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def source : List Bool → List Bool := RationalSubstitutionBits.compiledTerm ∘ pairFst

theorem source_mem_FP : source ∈ FP :=
  mem_FP_comp (f := pairFst) (g := RationalSubstitutionBits.compiledTerm) pairFst_mem_FP
    RationalSubstitutionBits.compiledTerm_mem_FP

noncomputable def value (q : List Bool) : List Bool := BinaryNatCode.encode (CollectedDegree.degree source pairSnd q)

theorem evaluator : SpaceFunction value := by
  have E := CollectedDegree.evaluator source pairSnd source_mem_FP pairSnd_mem_FP
  exact E

theorem value_packet (bits : List Bool) (i : Fin (CompactSource.size bits)) :
    value (pair bits (BinaryNatCode.encode i.val)) = BinaryNatCode.encode
      ((Term.finitePolynomial (CompactSource.size bits) (CompactSource.term bits)).degreeOf i) := by
  have h := CollectedDegree.indexedDegree_eq_degree source pairSnd (pair bits (BinaryNatCode.encode i.val))
  have hd : CollectedCoefficient.dimension source (pair bits (BinaryNatCode.encode i.val)) = CompactSource.size bits := by
    simp only [CollectedCoefficient.dimension, source, Function.comp_apply, pairFst_pair]
    rfl
  rw [hd] at h
  simp only [source, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at h
  have hA : (CompactSource.term bits).arity ≤ CompactSource.size bits :=
    (CompactSource.term bits).arity_le_dataSize.trans_eq (CompactSource.size_eq bits).symm
  have he := Term.indexedDegree_eq_degreeOf (CompactSource.term bits) (CompactSource.size bits) hA i
  have hresult : CollectedDegree.degree source pairSnd (pair bits (BinaryNatCode.encode i.val)) =
      (Term.finitePolynomial (CompactSource.size bits) (CompactSource.term bits)).degreeOf i := h.symm.trans he
  exact congrArg BinaryNatCode.encode hresult

theorem value_original_variable (bits : List Bool) (i : Fin (CompactSource.term bits).arity) :
    value (pair bits (BinaryNatCode.encode i.val)) = BinaryNatCode.encode
      ((Term.finitePolynomial (CompactSource.term bits).arity (CompactSource.term bits)).degreeOf i) := by
  have hA : (CompactSource.term bits).arity ≤ CompactSource.size bits :=
    (CompactSource.term bits).arity_le_dataSize.trans_eq (CompactSource.size_eq bits).symm
  have h := value_packet bits (Fin.castLE hA i)
  have hd := Term.degreeOf_finitePolynomial_padding (CompactSource.term bits) _ _ le_rfl hA i
  rw [hd] at h
  exact h

end LeanCanny.ETR.SourceDegree
