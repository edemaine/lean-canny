/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveCoordinatePathSource
public import LeanCanny.ETR.CoerciveFormalLeafReader
public import LeanCanny.Algebra.SymbolicFixedTableTreeSource
public import LeanCanny.Algebra.SymbolicPreparedTable
public import LeanCanny.Algebra.SymbolicPrimitivePairSelectedSpace

/-! # Total native addressing of a prepared coordinate's ancestor pair -/

@[expose] public section
namespace LeanCanny.ETR.CoercivePairRouting
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveSourceSampling SymbolicPairRecoveryBits
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CoerciveSourceSampling.dimension
attribute [local irreducible] BalancedMetadataTable.read BinaryNat.div BinaryNat.mod

/-- Context: pair (pair suppliedTable leafIndex) stageIndex. -/
def table (p : List Bool) := pairFst (pairFst p)
def bits (p : List Bool) := pairFst (pairFst (BalancedMetadataTable.source (table p)))
def leafWord (p : List Bool) := pairSnd (pairFst p)

theorem table_FP : table ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem bits_FP : bits ∈ FP := mem_FP_comp
  (mem_FP_comp (mem_FP_comp table_FP BalancedMetadataTable.source_FP) pairFst_mem_FP) pairFst_mem_FP
theorem leafWord_FP : leafWord ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def leaf (p : List Bool) : ℕ := min (Nat.fromBitsLE (leafWord p)) (dimension (bits p))
noncomputable def height (p : List Bool) : ℕ := min (Nat.fromBitsLE (pairSnd p)) ((dimension (bits p) + 1).size - 1)
noncomputable def parentIndex (p : List Bool) : ℕ := leaf p / 2 ^ (height p + 1)
noncomputable def isRight (p : List Bool) : Prop := leaf p / 2 ^ height p % 2 = 1

noncomputable def parent (p : List Bool) : List Bool := BalancedParameterContext.packet (table p) (height p + 1) (parentIndex p)

theorem leaf_unary : UnaryFn leaf := UnaryFn.fromBitsLE_min leafWord_FP (dimension_unary.comp bits_FP)
theorem height_unary : UnaryFn height := UnaryFn.fromBitsLE_min pairSnd_mem_FP
  ((((dimension_unary.comp bits_FP).add (UnaryFn.const 1)).size).sub (UnaryFn.const 1))

attribute [local irreducible] leaf height parentIndex parent

theorem parentIndex_binary : BinaryFn parentIndex := by
  have hp : BinaryFn (fun p => 2 ^ (height p + 1)) :=
    (BinaryFn.const 2).powUnary (height_unary.add (UnaryFn.const 1))
  have h : (fun p => BinaryNat.div (pair (BinaryNatCode.encode (leaf p))
      (BinaryNatCode.encode (2 ^ (height p + 1))))) ∈ FP :=
    mem_FP_comp (mem_FP_pair (bits_mem_FP leaf_unary) hp.bits_mem_FP) BinaryNat.div_mem_FP
  apply BinaryFn.of_bits
  apply mem_FP_of_eq h
  intro p
  simp only [BinaryNat.div_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, parentIndex]

theorem parent_FP : parent ∈ FP := by
  unfold parent
  exact BalancedParameterContext.packet_FP table_FP (height_unary.add (UnaryFn.const 1)) parentIndex_binary

theorem isRight_fppred : FPPred isRight := by
  have hp : BinaryFn (fun p => 2 ^ height p) := (BinaryFn.const 2).powUnary height_unary
  let quotient (p : List Bool) := BinaryNat.div (pair (BinaryNatCode.encode (leaf p)) (BinaryNatCode.encode (2 ^ height p)))
  let remainder (p : List Bool) := BinaryNat.mod (pair (quotient p) [false, true])
  have hd : quotient ∈ FP := mem_FP_comp (mem_FP_pair (bits_mem_FP leaf_unary) hp.bits_mem_FP) BinaryNat.div_mem_FP
  have hm : remainder ∈ FP := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP [false, true])) BinaryNat.mod_mem_FP
  have h : FPPred (fun p => remainder p = [true]) :=
    LeanCanny.Encoding.Brackets.stringEq_fppred hm (constFn_mem_FP [true])
  apply h.of_iff
  intro p
  simp only [remainder, quotient, BinaryNat.div_pair, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    show Nat.fromBitsLE [false, true] = 2 from rfl]
  change (leaf p / 2 ^ height p % 2).bits = (1 : ℕ).bits ↔ leaf p / 2 ^ height p % 2 = 1
  exact ⟨fun h => by
    have he := congrArg Nat.fromBitsLE h
    simpa only [Nat.fromBitsLE_bits] using he, fun h => congrArg Nat.bits h⟩

noncomputable def pairFamily (L : List Bool → Polynomial (Polynomial ℤ)) : SymbolicFixedTableEntryBits.Family :=
  SymbolicFixedTablePolynomialTree.pairFamily L parent

noncomputable def bound (E : List Bool → ℕ) (p : List Bool) : ℕ :=
  SymbolicFixedTablePolynomialTree.nodeBound E (parent p)

theorem bound_binary (E : List Bool → ℕ) (hE : BinaryFn E) : BinaryFn (bound E) :=
  (SymbolicFixedTablePolynomialTree.nodeBound_binary E hE).comp parent_FP

theorem leftOrder_binary (L : List Bool → Polynomial (Polynomial ℤ)) : BinaryFn (pairFamily L).leftOrder := by
  change BinaryFn (fun p => Nat.fromBitsLE (BalancedMetadataTable.read false (BalancedParameterContext.child false (parent p))))
  exact BinaryFn.fromBits (mem_FP_comp
    (f := BalancedParameterContext.child false ∘ parent) (g := BalancedMetadataTable.read false)
    (mem_FP_comp parent_FP (BalancedParameterContext.child_FP false)) (BalancedMetadataTable.read_FP false))

theorem rightOrder_binary (L : List Bool → Polynomial (Polynomial ℤ)) : BinaryFn (pairFamily L).rightOrder := by
  change BinaryFn (fun p => Nat.fromBitsLE (BalancedMetadataTable.read false (BalancedParameterContext.child true (parent p))))
  exact BinaryFn.fromBits (mem_FP_comp
    (f := BalancedParameterContext.child true ∘ parent) (g := BalancedMetadataTable.read false)
    (mem_FP_comp parent_FP (BalancedParameterContext.child_FP true)) (BalancedMetadataTable.read_FP false))

theorem direction_binary (L : List Bool → Polynomial (Polynomial ℤ)) : BinaryFn (pairFamily L).direction := by
  change BinaryFn (fun p => Nat.fromBitsLE (BalancedMetadataTable.read true (parent p)))
  exact BinaryFn.fromBits (mem_FP_comp (f := parent) (g := BalancedMetadataTable.read true) parent_FP (BalancedMetadataTable.read_FP true))

theorem left_inner (L : List Bool → Polynomial (Polynomial ℤ)) (E : List Bool → ℕ)
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) (p : List Bool) (k : ℕ) :
    (((pairFamily L).left p).coeff k).natDegree ≤ bound E p :=
  (SymbolicFixedTablePolynomialTree.node_inner_degree L E hL _ k).trans
    (SymbolicFixedTableTreeSource.child_bound E false (parent p))

theorem right_inner (L : List Bool → Polynomial (Polynomial ℤ)) (E : List Bool → ℕ)
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) (p : List Bool) (k : ℕ) :
    (((pairFamily L).right p).coeff k).natDegree ≤ bound E p :=
  (SymbolicFixedTablePolynomialTree.node_inner_degree L E hL _ k).trans
    (SymbolicFixedTableTreeSource.child_bound E true (parent p))

theorem leftEvaluator (L : List Bool → Polynomial (Polynomial ℤ))
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicFixedTablePolynomialTree.node L))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (pairFamily L).left) :=
  SymbolicFixedTableEntryBits.withContextEvaluator (SymbolicFixedTablePolynomialTree.node L)
    (BalancedParameterContext.child false ∘ parent) (mem_FP_comp parent_FP (BalancedParameterContext.child_FP false)) P

theorem rightEvaluator (L : List Bool → Polynomial (Polynomial ℤ))
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicFixedTablePolynomialTree.node L))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (pairFamily L).right) :=
  SymbolicFixedTableEntryBits.withContextEvaluator (SymbolicFixedTablePolynomialTree.node L)
    (BalancedParameterContext.child true ∘ parent) (mem_FP_comp parent_FP (BalancedParameterContext.child_FP true)) P

theorem numeratorEvaluator (L : List Bool → Polynomial (Polynomial ℤ)) (E : List Bool → ℕ)
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (hE : BinaryFn E)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicFixedTablePolynomialTree.node L))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (fun p => SymbolicPairRecoveryBits.Family.numerator (pairFamily L) (decide (isRight p)) p)) :=
  SymbolicPairRecoveryBits.Family.selectedNumeratorEvaluator (pairFamily L) (bound E) (left_inner L E hL) (right_inner L E hL)
    (leftOrder_binary L) (rightOrder_binary L) (direction_binary L) (bound_binary E hE)
    (leftEvaluator L P) (rightEvaluator L P) (fun p => decide (isRight p)) isRight_fppred.flag_mem_FP

theorem denominatorEvaluator (L : List Bool → Polynomial (Polynomial ℤ)) (E : List Bool → ℕ)
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (hE : BinaryFn E)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicFixedTablePolynomialTree.node L))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicPairRecoveryBits.Family.denominator (pairFamily L))) :=
  SymbolicPairRecoveryBits.Family.denominatorEvaluator (pairFamily L) (bound E) (left_inner L E hL) (right_inner L E hL)
    (leftOrder_binary L) (rightOrder_binary L) (direction_binary L) (bound_binary E hE)
    (leftEvaluator L P) (rightEvaluator L P)

end LeanCanny.ETR.CoercivePairRouting
