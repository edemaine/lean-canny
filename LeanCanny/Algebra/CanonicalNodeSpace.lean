/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CanonicalNodeContext
public import LeanCanny.Algebra.BalancedTableSubtrees
public import LeanCanny.Algebra.PrimitivePairSpace
public import LeanCanny.Algebra.ValidatedPolynomialReaders

/-! # Uniform native degrees and coefficients for every canonical subtree

Every word is normalized to a valid finite-tree node. The complete prepared
table supplies its exact degree and coefficient readers; the source-derived
height envelope applies at every normalized node.
-/

@[expose] public section

namespace LeanCanny.Algebra.CanonicalNodeBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (original)
open RationalSubstitution.IntegerBits (context selectedDegree mValue)

noncomputable def node (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (p : List Bool) : SeparableIntegerPolynomial :=
  BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne (original p))
    (CanonicalNodeContext.height count p) (CanonicalNodeContext.index count p)

def heightBudget (count D b : List Bool → ℕ) (p : List Bool) : ℕ :=
  FiniteAnnihilatorTree.sourceHeight (D (original p)) (b (original p)) (count (original p))

theorem heightBudget_binary {count D b : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (heightBudget count D b) :=
  (FiniteAnnihilatorTree.sourceHeight_binary hD hb hn).comp BalancedParameterContext.original_FP

def preparedNode (count : List Bool → ℕ) (z : List Bool) : List Bool :=
  BalancedParameterContext.packet (pairSnd z) (CanonicalNodeContext.height count (pairFst z)) (CanonicalNodeContext.index count (pairFst z))

theorem preparedNode_FP {count : List Bool → ℕ} (hn : UnaryFn count) : preparedNode count ∈ FP := by
  have hi : UnaryFn (CanonicalNodeContext.index count ∘ pairFst) := (CanonicalNodeContext.index_unary hn).comp pairFst_mem_FP
  exact BalancedParameterContext.packet_FP pairSnd_mem_FP ((CanonicalNodeContext.height_unary hn).comp pairFst_mem_FP)
    (BinaryFn.of_bits (bits_mem_FP hi))

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

attribute [local irreducible] BalancedTablePolynomials.tree BalancedTablePolynomials.node BinaryNat.normalize BalancedMetadataTable.read

include hdegree hheight in
theorem prepared_node (p : List Bool) :
    BalancedTablePolynomials.node (PaddedAnnihilatorBits.family B count)
      (preparedNode count (pair p (PaddedAnnihilatorPreparation.prepare B count D b (original p)))) = (node B count hne p).polynomial := by
  simp only [preparedNode, pairFst_pair, pairSnd_pair, BalancedTablePolynomials.node_packet]
  have hc := PaddedAnnihilatorPreparation.prepare_consistent B count D b hne hdegree hheight (original p)
  have hs := BalancedTablePolynomials.Consistent.subtree _ _ _ _ hc _ _ (CanonicalNodeContext.height_le count p) (CanonicalNodeContext.index_lt count p)
  exact BalancedTablePolynomials.tree_eq_node _ _ _ _ _ hs

include hdegree hheight in
theorem coefficient_bound (p : List Bool) (k : ℕ) : ((node B count hne p).polynomial.coeff k).natAbs ≤ 2 ^ heightBudget count D b p := by
  have hm := (FiniteAnnihilatorTree.source_tree_bounds
    (fun j => B.polynomial (pair (original p) (BinaryNatCode.encode j))) (count (original p)) (hne (original p))
    (D (original p)) (b (original p)) (hdegree (original p)) (fun j hj l => (B.coefficient_bound _ l).trans
      (Nat.pow_le_pow_right (by decide) (hheight (original p) j hj)))
    (CanonicalNodeContext.height count p) (CanonicalNodeContext.index count p) (CanonicalNodeContext.height_le count p)).parameterMass
  exact (coeff_natAbs_le_coefficientMass _ k).trans hm

include hdegree hheight in
noncomputable def family : Family where
  polynomial p := (node B count hne p).polynomial
  height := heightBudget count D b
  coefficient_bound := coefficient_bound B count D b hne hdegree hheight

include hdegree hheight in
theorem degreeEvaluator (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (fun p => BinaryNatCode.encode (node B count hne p).polynomial.natDegree) := by
  have E := (PaddedAnnihilatorPreparation.prepareEvaluator B count D b hne hdegree A hn hD hb).precompose original BalancedParameterContext.original_FP
  have hf := mem_FP_comp (mem_FP_comp (preparedNode_FP hn) (BalancedMetadataTable.read_FP false)) BinaryNat.normalize_mem_FP
  have R := E.withInput.postcompose (fun z => BinaryNat.normalize (BalancedMetadataTable.read false (preparedNode count z))) hf
  exact R.congr (funext fun p => by
    simp only [Function.comp_apply, BinaryNat.normalize_eq_bits]
    have hr := (PaddedAnnihilatorPreparation.prepare_ready B count D b hne hdegree hheight (original p)).orders
      (CanonicalNodeContext.height count p) (CanonicalNodeContext.index count p)
      (CanonicalNodeContext.height_le count p) (CanonicalNodeContext.index_lt count p)
    simpa only [preparedNode, pairFst_pair, pairSnd_pair, BalancedMetadataTable.order, node, BinaryNatCode.encode] using congrArg BinaryNatCode.encode hr)

def coefficientQuery (count : List Bool → ℕ) (z : List Bool) : List Bool :=
  pair (pair (preparedNode count (pair (context (pairFst z)) (pairSnd z))) (selectedDegree (pairFst z))) (pairSnd (pairFst z))

theorem coefficientQuery_FP {count : List Bool → ℕ} (hn : UnaryFn count) : coefficientQuery count ∈ FP := by
  have hn' := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP) pairSnd_mem_FP)
    (preparedNode_FP hn)
  have hk := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hn' hk) hm

include hdegree hheight in
theorem coefficientEvaluator (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (PrimitivePairBits.coefficient (fun p => (node B count hne p).polynomial)) := by
  have hsource := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP BalancedParameterContext.original_FP
  have E := (PaddedAnnihilatorPreparation.prepareEvaluator B count D b hne hdegree A hn hD hb).precompose
    (original ∘ context) hsource
  have R := (E.withInput.postcompose (coefficientQuery count) (coefficientQuery_FP hn)).chain
    (BalancedTablePolynomials.evaluator (PaddedAnnihilatorBits.family B count) (PaddedAnnihilatorBits.readers B A count hn))
  exact R.congr (funext fun q => by
    simp only [Function.comp_apply, coefficientQuery, pairFst_pair, pairSnd_pair,
      BalancedTablePolynomials.nodeValue, CannyBalancedTaskRouting.nodeContext, CannyResultantBits.mValue]
    rw [prepared_node B count D b hne hdegree hheight]
    rfl)

include hdegree hheight in
noncomputable def checkedReaders (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    Readers (ValidatedDegreeBits.family (family B count D b hne hdegree hheight)) := by
  have E := (coefficientEvaluator B count D b hne hdegree hheight A hn hD hb).precompose
    PrimitivePairBits.modularCoefficientQuery PrimitivePairBits.modularCoefficientQuery_FP
  have E' : SpaceFunction (ValidatedDegreeBits.coefficient (family B count D b hne hdegree hheight).polynomial) :=
    E.congr (funext fun q => by
      simp only [Function.comp_apply, PrimitivePairBits.coefficient, PrimitivePairBits.modularCoefficientQuery,
        context, selectedDegree, mValue, pairFst_pair, pairSnd_pair, ValidatedDegreeBits.coefficient,
        ValidatedDegreeBits.context, ValidatedDegreeBits.modulus, family]
      rfl)
  exact ValidatedDegreeBits.readers _ (heightBudget_binary hn hD hb) E'
    (degreeEvaluator B count D b hne hdegree hheight A hn hD hb)

end LeanCanny.Algebra.CanonicalNodeBits
