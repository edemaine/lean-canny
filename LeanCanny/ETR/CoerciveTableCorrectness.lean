/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.CoerciveFormalLeafReader
public import LeanCanny.Algebra.SymbolicPreparedTable
public import LeanCanny.Algebra.BalancedTableSubtrees

/-! # Exact reference subtrees inside the enlarged native integer table -/
@[expose] public section
namespace LeanCanny.ETR.CoerciveTableCorrectness
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveIntegerPreparation CoerciveSourceSampling
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det
  CoerciveNativeAnnihilators.original CoerciveNativeAnnihilators.degreeBound
  CoerciveNativeAnnihilators.massExponent CoerciveSourceSampling.dimension
  CoercivePreparationControls.referenceExponent
set_option backward.isDefEq.respectTransparency false

noncomputable def referenceLeaves (bits : List Bool) : ℕ → SeparableIntegerPolynomial :=
  (CoercivePreparationControls.family bits).reference.leaves
    (CoercivePreparationControls.family bits).padded
    (CoercivePreparationControls.family bits).padded_controls
    (CoercivePreparationControls.family bits).padded_nonzero

noncomputable def integerLeaves (bits : List Bool) : ℕ → SeparableIntegerPolynomial :=
  PaddedAnnihilatorPreparation.leaves retainedFamily retainedCount retained_nonzero (prepare bits)

noncomputable def height (bits : List Bool) : ℕ := (dimension bits+1).size

theorem integerTable_source (p : List Bool) : BalancedMetadataTable.source (integerTable p)=p := by
  unfold integerTable PaddedAnnihilatorPreparation.prepare BalancedDirectionPreparation.directions
  rw [(BalancedDirectionPreparation.tableRun_fields _ _ _ _ _).1]
  exact BalancedDegreeTable.prepared_source _ _ _ _

theorem tablePrepare_source (bits : List Bool) : BalancedMetadataTable.source (tablePrepare bits)=prepare bits :=
  integerTable_source (prepare bits)

theorem reference_exponent (bits : List Bool) :
    (CoercivePreparationControls.family bits).reference.exponent=CoercivePreparationControls.referenceExponent bits := by
  rw [CoercivePreparationControls.referenceExponent, SymbolicFixedTableFinite.Family.exponent]

theorem reference_leaf_polynomial (bits : List Bool) (i : ℕ) :
    (referenceLeaves bits i).polynomial=ScaledSquarefree.polynomial
      (dyadicFamily.specialized (pair bits (BinaryNatCode.encode i))) := by
  rw [clear_eq]
  simp only [referenceLeaves, SymbolicFixedTable.Reference.leaves, SymbolicFixedTable.integerLeaves,
    SeparableIntegerPolynomial.squarefree, raw, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, reference_exponent]
  rfl

theorem integer_leaf_polynomial (bits : List Bool) (i : ℕ) (hi : i<count bits) :
    (integerLeaves bits i).polynomial=(referenceLeaves bits i).polynomial := by
  have hic : i<retainedCount (prepare bits) := by simpa only [retainedCount, prepare_source] using hi
  unfold integerLeaves PaddedAnnihilatorPreparation.leaves
  rw [FiniteAnnihilatorTree.leaf, dite_eq_left hic]
  change ScaledSquarefree.polynomial (retainedFamily.polynomial (pair (prepare bits) (BinaryNatCode.encode i))) = _
  rw [retained_prepared_polynomial bits i hi, reference_leaf_polynomial]

theorem height_le (bits : List Bool) : height bits≤(retainedCount (prepare bits)).size := by
  simp only [height, retainedCount, prepare_source]
  apply Nat.size_le_size
  unfold count
  omega

theorem table_consistent_integer (bits : List Bool) :
    BalancedTablePolynomials.Consistent (PaddedAnnihilatorBits.family retainedFamily retainedCount)
      (tablePrepare bits) (integerLeaves bits) (retainedCount (prepare bits)).size 0 :=
  PaddedAnnihilatorPreparation.prepare_consistent retainedFamily retainedCount retainedDegree retainedMass
    retained_nonzero retained_degree retained_height (prepare bits)

/-- The larger table contains the literal reference subtree. Every scalar
introduced while clearing padded X leaves is retained. -/
theorem table_consistent_reference (bits : List Bool) :
    BalancedTablePolynomials.Consistent (PaddedAnnihilatorBits.family retainedFamily retainedCount)
      (tablePrepare bits) (referenceLeaves bits) (height bits) 0 := by
  have H := BalancedSubtreeLocality.consistent_lower_zero _ _ _ _ _ (height_le bits) (table_consistent_integer bits)
  apply BalancedSubtreeLocality.consistent_congr _ _ (integerLeaves bits) (referenceLeaves bits) _ _ _ H
  intro j hj
  simp only [Nat.mul_zero, Nat.zero_add]
  apply integer_leaf_polynomial bits j
  exact hj.trans_le (FiniteAnnihilatorTree.width_bound (dimension bits+1))

theorem reference_node_degree (bits : List Bool) (h i : ℕ) (hh : h≤height bits) :
    (BalancedPrimitiveTree.node (referenceLeaves bits) h i).polynomial.natDegree =
      (SymbolicFixedTable.node (fun j => SymbolicScaledSquarefree.polynomial
        ((CoercivePreparationControls.family bits).padded j))
        (CoercivePreparationControls.family bits).directions h i).natDegree :=
  (CoercivePreparationControls.family bits).reference.node_degree _
    (CoercivePreparationControls.family bits).padded_controls
    (CoercivePreparationControls.family bits).padded_nonzero h i hh

theorem reference_direction (bits : List Bool) (h i : ℕ) :
    (CoercivePreparationControls.family bits).directions h i =
      PrimitivePair.select (BalancedPrimitiveTree.node (referenceLeaves bits) h (2*i)).polynomial
        (BalancedPrimitiveTree.node (referenceLeaves bits) h (2*i+1)).polynomial := by
  simp only [SymbolicFixedTableFinite.Family.directions, SymbolicFixedTable.Reference.directions,
    SymbolicFixedTable.integerDirections, referenceLeaves]

theorem table_consistent_subtree (bits : List Bool) (h i : ℕ)
    (hh : h≤height bits) (hi : i<2^(height bits-h)) :
    BalancedTablePolynomials.Consistent (PaddedAnnihilatorBits.family retainedFamily retainedCount)
      (tablePrepare bits) (referenceLeaves bits) h i :=
  BalancedSubtreeLocality.consistent_subtree _ _ _ _ _ _ hh hi (table_consistent_reference bits)

theorem interval_index_lt (bits : List Bool) (h i j : ℕ) (hh : h≤height bits)
    (hi : i<2^(height bits-h)) (hj : j<2^h) : 2^h*i+j<2^(height bits) :=
  BalancedSubtreeLocality.interval_index_lt (height bits) h i j hh hi hj

theorem leaf_eq_reference (bits : List Bool) (i : ℕ) (hi : i<count bits) :
    CoerciveFormalLeafReader.leaf (pair (tablePrepare bits) (BinaryNatCode.encode i)) =
      SymbolicScaledSquarefree.polynomial ((CoercivePreparationControls.family bits).padded i) := by
  unfold CoerciveFormalLeafReader.leaf CoerciveFormalLeafReader.payloadInput
  simp only [pairFst_pair, pairSnd_pair, tablePrepare_source]
  rw [CoerciveFormalLeafReader.payloadLeaf_prepare bits i hi]
  simp only [raw, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

/-- Every used node, including both children of every coordinate-path edge,
is literally the actual symbolic reference node. -/
theorem tree_eq_reference (bits : List Bool) (h i : ℕ)
    (hh : h≤height bits) (hi : i<2^(height bits-h)) :
    SymbolicFixedTablePolynomialTree.tree CoerciveFormalLeafReader.leaf (tablePrepare bits) h i =
      SymbolicFixedTable.node (fun j => SymbolicScaledSquarefree.polynomial
        ((CoercivePreparationControls.family bits).padded j))
        (CoercivePreparationControls.family bits).directions h i := by
  apply SymbolicFixedTablePolynomialTree.tree_eq_of_consistent
    CoerciveFormalLeafReader.leaf _ (tablePrepare bits) (referenceLeaves bits) _ _ (height bits) h i hh
    (table_consistent_subtree bits h i hh hi)
    (fun h i hh => reference_node_degree bits h i hh) (reference_direction bits)
  intro j hj
  exact leaf_eq_reference bits _ ((interval_index_lt bits h i j hh hi hj).trans_le
    (FiniteAnnihilatorTree.width_bound (dimension bits+1)))

theorem table_direction_reference (bits : List Bool) (h i : ℕ)
    (hh : h+1≤height bits) (hi : i<2^(height bits-(h+1))) :
    BalancedMetadataTable.direction (BalancedParameterContext.packet (tablePrepare bits) (h+1) i) =
      (CoercivePreparationControls.family bits).directions h i :=
  (table_consistent_subtree bits (h+1) i hh hi).2.2.2.2.trans (reference_direction bits h i).symm

/-- Preparation retains exact orders, including its root. Literal retained-leaf
equality transports those orders to the symbolic reference subtree. -/
theorem table_order_reference (bits : List Bool) (h i : ℕ)
    (hh : h≤height bits) (hi : i<2^(height bits-h)) :
    BalancedMetadataTable.order (BalancedParameterContext.packet (tablePrepare bits) h i) =
      (SymbolicFixedTable.node (fun j => SymbolicScaledSquarefree.polynomial
        ((CoercivePreparationControls.family bits).padded j))
        (CoercivePreparationControls.family bits).directions h i).natDegree := by
  let H := (retainedCount (prepare bits)).size
  have hiH : i<2^(H-h) := hi.trans_le (Nat.pow_le_pow_right (by decide) (by
    have ht := height_le bits; dsimp [H]; omega))
  have ho := (PaddedAnnihilatorPreparation.prepare_ready retainedFamily retainedCount retainedDegree retainedMass
    retained_nonzero retained_degree retained_height (prepare bits)).orders h i (hh.trans (height_le bits)) hiH
  have hn := BalancedSubtreeLocality.node_polynomial_congr (integerLeaves bits) (referenceLeaves bits) h i
    (fun j hj => integer_leaf_polynomial bits _ ((interval_index_lt bits h i j hh hi hj).trans_le
      (FiniteAnnihilatorTree.width_bound (dimension bits+1))))
  exact ho.trans ((congrArg Polynomial.natDegree hn).trans (reference_node_degree bits h i hh))

/-- One prepared ancestor pair exposes its child polynomials, exact orders,
and actual selected direction through the generic table interface. -/
theorem pair_spec (bits : List Bool) (h i : ℕ) (hh : h + 1 ≤ height bits)
    (hi : i < 2 ^ (height bits - (h + 1))) :
    SymbolicFixedTablePolynomialTree.PairSpec CoerciveFormalLeafReader.leaf (tablePrepare bits)
      (fun j => SymbolicScaledSquarefree.polynomial ((CoercivePreparationControls.family bits).padded j))
      (CoercivePreparationControls.family bits).directions h i := by
  obtain ⟨hl, hr⟩ := BalancedTablePolynomials.child_index_lt (height bits) h i hh hi
  exact ⟨⟨tree_eq_reference bits h (2 * i) (by omega) hl,
      table_order_reference bits h (2 * i) (by omega) hl⟩,
    ⟨tree_eq_reference bits h (2 * i + 1) (by omega) hr,
      table_order_reference bits h (2 * i + 1) (by omega) hr⟩,
    table_direction_reference bits h i hh hi⟩

/-- The polynomial computed by the total malformed-frame scheduler is the
actual source reference parameter on the concrete native prepared table. -/
theorem tree_eq_parameter (bits : List Bool) :
    SymbolicFixedTablePolynomialTree.tree CoerciveFormalLeafReader.leaf (tablePrepare bits) (height bits) 0 =
      (CoercivePreparationControls.family bits).parameter := by
  exact tree_eq_reference bits (height bits) 0 le_rfl (by simp)

end LeanCanny.ETR.CoerciveTableCorrectness
