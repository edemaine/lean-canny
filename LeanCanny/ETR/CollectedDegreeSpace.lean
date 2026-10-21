/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedDegree
public import LeanCanny.ETR.MonomialExponentVector
public import LeanCanny.ETR.CollectedCoefficientZero
public import LeanCanny.Computation.BoundedMaximum
public import LeanCanny.Computation.SpaceFunctionSelect
public import LeanCanny.Computation.SpaceDeciderOutput

/-! # Actual variable degree computation in polynomial space

For each indexed monomial, test its collected coefficient for zero and retain
its selected-variable exponent only when it survives. A streamed maximum
computes the actual degree. Variable indices stay binary; out-of-range indices
give zero. No expansion or coefficient oracle is assumed.
-/

@[expose] public section

namespace LeanCanny.ETR.CollectedDegree
open Complexity
open LeanCanny.Encoding LeanCanny.Computation

noncomputable def survivingValue (source varIndex : List Bool → List Bool) (q : List Bool) : List Bool := by
  classical
  exact if CollectedCoefficient.coefficient (source ∘ pairFst)
    (MonomialReader.exponentVectorWord (source ∘ pairFst) pairSnd) q = 0 then [] else
      MonomialReader.exponentRead (source ∘ pairFst) pairSnd (varIndex ∘ pairFst) q

theorem survivingEvaluator (source varIndex : List Bool → List Bool)
    (hs : source ∈ FP) (hv : varIndex ∈ FP) : SpaceFunction (survivingValue source varIndex) := by
  classical
  have hsrc := mem_FP_comp pairFst_mem_FP hs
  let D := CollectedCoefficient.zeroDecider (source ∘ pairFst)
    (MonomialReader.exponentVectorWord (source ∘ pairFst) pairSnd) hsrc
      (MonomialReader.exponentVectorWord_mem_FP hsrc pairSnd_mem_FP)
  let R := SpaceFunction.ofFP _ (MonomialReader.exponentRead_mem_FP hsrc pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hv))
  let E := SpaceFunction.select D.indicator (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])) R
  refine E.congr (funext fun q => ?_)
  simp only [survivingValue, Set.mem_ofPred_eq, List.getElem?_cons_zero, Option.getD_some, decide_eq_true_eq]

theorem survivingValue_packet (source varIndex : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    survivingValue source varIndex (pair c (BinaryNatCode.encode r)) = BinaryNatCode.encode
      (Term.survivingExponent (TermView.term (source c)) (CollectedCoefficient.dimension source c) r
        (Nat.fromBitsLE (varIndex c))) := by
  classical
  have hc := MonomialReader.coefficient_at_exponentVectorWord (source ∘ pairFst) pairSnd (pair c (BinaryNatCode.encode r))
  have hd : CollectedCoefficient.dimension (source ∘ pairFst) (pair c (BinaryNatCode.encode r)) =
      CollectedCoefficient.dimension source c := by simp only [CollectedCoefficient.dimension, Function.comp_apply, pairFst_pair]
  rw [hd] at hc
  have hr : Nat.fromBitsLE (BinaryNatCode.encode r) = r := Nat.fromBitsLE_bits r
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, hr] at hc
  rw [survivingValue, hc, Term.survivingExponent]
  split_ifs
  · rfl
  · rw [MonomialReader.exponentRead_correct]
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def degree (source varIndex : List Bool → List Bool) (c : List Bool) : ℕ := by
  classical
  exact if hi : Nat.fromBitsLE (varIndex c) < CollectedCoefficient.dimension source c then
    (Term.finitePolynomial (CollectedCoefficient.dimension source c) (TermView.term (source c))).degreeOf
      ⟨Nat.fromBitsLE (varIndex c), hi⟩ else 0

theorem indexedDegree_eq_degree (source varIndex : List Bool → List Bool) (c : List Bool) :
    Term.indexedDegree (TermView.term (source c)) (CollectedCoefficient.dimension source c)
      (Nat.fromBitsLE (varIndex c)) = degree source varIndex c := by
  classical
  unfold degree
  split_ifs with hi
  · exact Term.indexedDegree_eq_degreeOf _ _ (CollectedCoefficient.arity_le_dimension source c) ⟨_, hi⟩
  · exact Term.indexedDegree_eq_zero_of_arity_le _ _ _
      ((CollectedCoefficient.arity_le_dimension source c).trans (by omega))

theorem evaluator (source varIndex : List Bool → List Bool) (hs : source ∈ FP) (hv : varIndex ∈ FP) :
    SpaceFunction (fun c => BinaryNatCode.encode (degree source varIndex c)) := by
  let bound := fun c => BinaryNatCode.encode (CollectedCoefficient.dimension source c)
  have hb : bound ∈ FP := bits_mem_FP (CollectedCoefficient.dimension_unary hs)
  let a := fun c r => Term.survivingExponent (TermView.term (source c)) (CollectedCoefficient.dimension source c) r
    (Nat.fromBitsLE (varIndex c))
  let E := BoundedMaximum.evaluator (survivingEvaluator source varIndex hs hv) (CollectedCoefficient.count source) bound
    (CollectedCoefficient.count_mem_FP hs) hb a (fun c r _ => survivingValue_packet source varIndex c r) (by
      intro c r _
      have h := (Term.survivingExponent_le (TermView.term (source c)) (CollectedCoefficient.dimension source c) r
        (Nat.fromBitsLE (varIndex c))).trans (TermView.term (source c)).degreeBound_le_dataSize
      simpa only [a, bound, BinaryNatCode.encode, Nat.fromBitsLE_bits, CollectedCoefficient.dimension,
        TermView.normalize_eq_term, Data.length_toBits] using h)
  refine E.congr (funext fun c => ?_)
  rw [CollectedCoefficient.count_code]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact congrArg Nat.bits (indexedDegree_eq_degree source varIndex c)

end LeanCanny.ETR.CollectedDegree
