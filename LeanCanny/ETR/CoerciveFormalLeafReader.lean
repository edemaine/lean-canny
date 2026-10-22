/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.CoerciveIntegerPreparation
public import LeanCanny.Algebra.SymbolicFormalSquarefreeSpace

/-! # Total native coercive symbolic leaves from retained integer metadata -/
@[expose] public section
namespace LeanCanny.ETR.CoerciveFormalLeafReader
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveIntegerPreparation
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det
  CoerciveNativeAnnihilators.original CoerciveNativeAnnihilators.degreeBound
  CoerciveNativeAnnihilators.massExponent CoerciveSourceSampling.dimension
set_option backward.isDefEq.respectTransparency false

def rawInput (p : List Bool) : List Bool := pair (pairFst (pairFst (pairFst p))) (pairSnd p)
theorem rawInput_FP : rawInput ∈ FP := mem_FP_pair
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) pairSnd_mem_FP
noncomputable def source (p : List Bool) : Polynomial (Polynomial ℤ) := raw (rawInput p)
noncomputable def degree (p : List Bool) : ℕ := Nat.fromBitsLE (retainedReaders.degree p)
noncomputable def order (p : List Bool) : ℕ := Nat.fromBitsLE (gcdRead p)
noncomputable def innerDegree (p : List Bool) : ℕ := CoerciveNativeAnnihilators.degreeBound (pairFst (rawInput p))

theorem degree_binary : BinaryFn degree := BinaryFn.fromBits retainedReaders.degreeFP
theorem order_binary : BinaryFn order := BinaryFn.fromBits gcdRead_FP
theorem innerDegree_binary : BinaryFn innerDegree := CoerciveNativeAnnihilators.degreeBound_binary.comp
  (mem_FP_comp rawInput_FP pairFst_mem_FP)

theorem source_inner_degree (p : List Bool) (k : ℕ) : (source p |>.coeff k).natDegree ≤ innerDegree p := by
  have h := (raw_controls (rawInput p)).2.1 k
  rw [padded_inner] at h
  exact h

theorem sourceEvaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient source) := by
  have E := rawEvaluator.precompose (SeparableBits.reindexQuery rawInput)
    (SeparableBits.reindexQuery_FP rawInput rawInput_FP)
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, rawCoefficient, SymbolicFixedTableEntryBits.coefficient,
    SeparableBits.reindexQuery, source, pairFst_pair, pairSnd_pair]

noncomputable def payloadLeaf (p : List Bool) : Polynomial (Polynomial ℤ) :=
  SymbolicFormalSquarefreeBits.polynomial (source p) (degree p) (order p)

theorem payloadEvaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient payloadLeaf) :=
  SymbolicFormalSquarefreeBits.evaluator source degree order innerDegree source_inner_degree
    degree_binary order_binary innerDegree_binary sourceEvaluator

theorem degree_eq (p : List Bool) : degree p=(retainedFamily.polynomial p).natDegree := by
  unfold degree
  rw [retainedReaders.degree_eq]
  exact Nat.fromBitsLE_bits _

noncomputable def payloadBound (p : List Bool) : ℕ :=
  (retainedDegree p+1)*(2*retainedDegree p+1)*CoerciveNativeAnnihilators.degreeBound (pairFst (pairFst p))
theorem payloadBound_binary : BinaryFn payloadBound :=
  ((retainedDegree_binary.add (BinaryFn.const 1)).mul
    (((BinaryFn.const 2).mul retainedDegree_binary).add (BinaryFn.const 1))).mul
      ((CoerciveNativeAnnihilators.degreeBound_binary.comp pairFst_mem_FP).comp pairFst_mem_FP)

theorem payload_inner_degree (p : List Bool) (i k : ℕ) :
    ((payloadLeaf (pair p (BinaryNatCode.encode i))).coeff k).natDegree ≤ payloadBound p := by
  have hD : degree (pair p (BinaryNatCode.encode i)) ≤ retainedDegree p := by
    rw [degree_eq]
    change (checkedFamily.polynomial (retainedInput (pair p (BinaryNatCode.encode i)))).natDegree ≤ _
    simp only [retainedInput, pairFst_pair, pairSnd_pair]
    exact (checked_degree (pairFst p) i).le
  have hE := SymbolicFormalSquarefreeBits.polynomial_inner_degree
    (source (pair p (BinaryNatCode.encode i))) (degree (pair p (BinaryNatCode.encode i)))
    (order (pair p (BinaryNatCode.encode i))) (innerDegree (pair p (BinaryNatCode.encode i))) k
    (source_inner_degree (pair p (BinaryNatCode.encode i)))
  apply hE.trans
  simp only [innerDegree, rawInput, pairFst_pair, pairSnd_pair]
  unfold payloadBound
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul (Nat.add_le_add_right hD 1)
    (Nat.mul_le_mul_right _ (by omega))

theorem payloadLeaf_prepare (bits : List Bool) (i : ℕ) (hi : i<count bits) :
    payloadLeaf (pair (prepare bits) (BinaryNatCode.encode i))=
      SymbolicScaledSquarefree.polynomial (raw (pair bits (BinaryNatCode.encode i))) := by
  have hs : source (pair (prepare bits) (BinaryNatCode.encode i))=raw (pair bits (BinaryNatCode.encode i)) := by
    unfold source rawInput
    simp only [pairFst_pair, pairSnd_pair, prepare_source]
  have hd : degree (pair (prepare bits) (BinaryNatCode.encode i))=(raw (pair bits (BinaryNatCode.encode i))).natDegree := by
    rw [degree_eq, retained_prepared_polynomial bits i hi, clear_degree]
  have hk : order (pair (prepare bits) (BinaryNatCode.encode i))=
      SymbolicScaledSquarefree.degree (raw (pair bits (BinaryNatCode.encode i))) := by
    rw [order, gcdRead_prepare bits i hi]
    exact Nat.fromBitsLE_bits _
  unfold payloadLeaf
  rw [hs, hd, hk, SymbolicFormalSquarefreeBits.polynomial_eq]

def payloadInput (p : List Bool) : List Bool :=
  pair (BalancedMetadataTable.source (pairFst p)) (pairSnd p)
theorem payloadInput_FP : payloadInput ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP BalancedMetadataTable.source_FP) pairSnd_mem_FP
noncomputable def leaf (p : List Bool) : Polynomial (Polynomial ℤ) := payloadLeaf (payloadInput p)
noncomputable def bound (p : List Bool) : ℕ := payloadBound (BalancedMetadataTable.source p)
theorem bound_binary : BinaryFn bound := payloadBound_binary.comp BalancedMetadataTable.source_FP

theorem leafEvaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient leaf) := by
  have E := payloadEvaluator.precompose (SeparableBits.reindexQuery payloadInput)
    (SeparableBits.reindexQuery_FP payloadInput payloadInput_FP)
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient,
    SeparableBits.reindexQuery, leaf, pairFst_pair, pairSnd_pair]

theorem leaf_inner_degree (p : List Bool) (i k : ℕ) :
    ((leaf (pair p (BinaryNatCode.encode i))).coeff k).natDegree ≤ bound p := by
  change ((payloadLeaf (payloadInput (pair p (BinaryNatCode.encode i)))).coeff k).natDegree ≤ _
  simp only [payloadInput, pairFst_pair, pairSnd_pair]
  exact payload_inner_degree (BalancedMetadataTable.source p) i k

end LeanCanny.ETR.CoerciveFormalLeafReader
