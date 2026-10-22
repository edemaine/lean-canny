/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicCoordinateClear
public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace
public import LeanCanny.Algebra.UnivariateRationalSpace
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Encoding.BinaryDivFP

/-! # Native streamed symbolic denominator clearing

Parameter slices retain the genuine root index. Every integer clearing stage
includes the supplied source and coordinate coefficient evaluators.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicCoordinateClearBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped BigOperators
attribute [local irreducible] BinaryNat.normalize BinaryNat.sub

noncomputable def sliced (p : List Bool → Polynomial (Polynomial ℤ)) (c : List Bool) : ℤ[X] :=
  SymbolicFixedTable.slice (p (pairFst c)) (Nat.fromBitsLE (pairSnd c))

def sliceQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (context q)) (pairSnd q)) (pair (pairSnd (context q)) (selectedDegree q))

lemma sliceQuery_FP : sliceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP)

lemma sliceEvaluator (p : List Bool → Polynomial (Polynomial ℤ))
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (sliced p)) := by
  refine (P.precompose sliceQuery sliceQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, sliceQuery,
    PrimitivePairBits.coefficient, sliced, SymbolicFixedTable.slice_coeff,
    pairFst_pair, pairSnd_pair, mValue]
  rfl


/-- Forget the slice field in an ordinary coefficient query. -/
def unsliceQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (context q)) (selectedDegree q)) (pairSnd q)

lemma unsliceQuery_FP : unsliceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

lemma unsliceEvaluator (p : List Bool → ℤ[X])
    (P : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => p (pairFst c))) := by
  refine (P.precompose unsliceQuery unsliceQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, PrimitivePairBits.coefficient, unsliceQuery, context,
    selectedDegree, mValue, pairFst_pair, pairSnd_pair]

/-- The summand query carries its alpha slice as an extra context field. -/
def summandQuery (q : List Bool) : List Bool :=
  pair (pair (pair (context (pairFst q)) (pairSnd q))
    (BinaryNat.sub (pair (selectedDegree (pairFst q)) (pairSnd q)))) (pairSnd (pairFst q))

lemma summandQuery_FP : summandQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP
  have hk := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP)
    (mem_FP_comp (mem_FP_pair hk pairSnd_mem_FP) BinaryNat.sub_mem_FP))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def summand (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) ≤ Nat.fromBitsLE (selectedDegree (pairFst q)) then
    f (summandQuery q) else []

lemma summandEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (summand f) := by
  have h := BinaryNat.le_fppred pairSnd_mem_FP
    (mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP)
  refine (SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairSnd q) ≤
    Nat.fromBitsLE (selectedDegree (pairFst q)))) h.flag_mem_FP
      (E.precompose summandQuery summandQuery_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr ?_
  funext q
  simp only [summand, decide_eq_true_eq, Function.comp_apply]

/-- A canonical encoded coefficient reader for one actual symbolic clearing step.
The source is sliced before the univariate clearing evaluator is invoked. -/
theorem encodedEvaluator (p : List Bool → Polynomial (Polynomial ℤ))
    (n d : List Bool → ℤ[X]) (e A : List Bool → ℕ) (he : BinaryFn e) (hA : BinaryFn A)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient p))
    (N : SpaceFunction (PrimitivePairBits.coefficient n))
    (D : SpaceFunction (PrimitivePairBits.coefficient d)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c =>
      ∑ l ∈ Finset.range (A c + 1), X ^ l *
        UnivariateRational.clear (e c) (SymbolicFixedTable.slice (p c) l) (n c) (d c))) := by
  let f := PrimitivePairBits.coefficient (fun c => UnivariateRational.clear (e (pairFst c))
    (sliced p c) (n (pairFst c)) (d (pairFst c)))
  have E : SpaceFunction f := UnivariateRationalBits.evaluator _ _ _ _ (he.comp pairFst_mem_FP)
    (sliceEvaluator p P) (unsliceEvaluator n N) (unsliceEvaluator d D)
  let count := fun q => BinaryNatCode.encode (A (context q) + 1)
  let modulus := fun q => BinaryNat.succ (pairSnd q)
  have hcount : BinaryFn (fun q => A (context q) + 1) :=
    (hA.add (BinaryFn.const 1)).comp RationalSubstitution.IntegerBits.context_mem_FP
  have hc : count ∈ FP := hcount.bits_mem_FP
  have hm : modulus ∈ FP := mem_FP_comp (f := pairSnd) (g := BinaryNat.succ) pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hmval (q : List Bool) : Nat.fromBitsLE (modulus q) = mValue q := by
    simp only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, mValue]
  let a := fun q l => (((X ^ l * UnivariateRational.clear (e (context q))
    (SymbolicFixedTable.slice (p (context q)) l) (n (context q)) (d (context q))).coeff
      (Nat.fromBitsLE (selectedDegree q)) : ℤ) : ZMod (mValue q))
  have hs : ∀ q l, l < Nat.fromBitsLE (count q) →
      summand f (pair q (BinaryNatCode.encode l)) = residueBits (a q l) := by
    intro q l _
    simp only [summand, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [a, coeff_X_pow_mul']
    split_ifs with h
    · simp only [f, PrimitivePairBits.coefficient, summandQuery, pairFst_pair, pairSnd_pair,
        context, selectedDegree, BinaryNat.sub_pair, sliced, mValue,
        Nat.fromBitsLE_bits]
      rfl
    · simp only [Int.cast_zero, residueBits, BinaryNatCode.encode, ZMod.val_zero]
      rfl
  have H := ModularSum.evaluatorWithModulus (summandEvaluator E) count modulus hc hm
    mValue (funext hmval) a (fun q => Nat.zero_lt_succ _) hs
  refine H.congr (funext fun q => ?_)
  simp only [count, Nat.fromBitsLE_bits, BinaryNatCode.encode, a,
    PrimitivePairBits.coefficient, finsetSum_coeff, Int.cast_sum,
    RationalSubstitution.IntegerBits.coefficientResidue]

end LeanCanny.Algebra.SymbolicCoordinateClearBits
