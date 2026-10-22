/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.CoerciveFormalLeafReader
public import LeanCanny.Algebra.BalancedSubtreeLocality
public import LeanCanny.Algebra.SymbolicFixedTablePolynomialTree

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

private theorem symbolic_tree_eq (bits : List Bool) (h i : ℕ) (hh : h≤height bits)
    (hc : BalancedTablePolynomials.Consistent (PaddedAnnihilatorBits.family retainedFamily retainedCount)
      (tablePrepare bits) (referenceLeaves bits) h i)
    (hl : ∀ j<2^h, CoerciveFormalLeafReader.leaf
      (pair (tablePrepare bits) (BinaryNatCode.encode (2^h*i+j))) =
        SymbolicScaledSquarefree.polynomial ((CoercivePreparationControls.family bits).padded (2^h*i+j))) :
    SymbolicFixedTablePolynomialTree.tree CoerciveFormalLeafReader.leaf (tablePrepare bits) h i =
      SymbolicFixedTable.node (fun j => SymbolicScaledSquarefree.polynomial
        ((CoercivePreparationControls.family bits).padded j))
        (CoercivePreparationControls.family bits).directions h i := by
  induction h generalizing i with
  | zero =>
    simpa only [pow_zero, one_mul, Nat.add_zero, SymbolicFixedTablePolynomialTree.tree, SymbolicFixedTable.node]
      using hl 0 (by decide)
  | succ h ih =>
    obtain ⟨hcl,hcr,hdl,hdr,hd⟩ := hc
    have hhl : h≤height bits := by omega
    have hL := ih (2*i) hhl hcl (fun j hj => by
      have he : 2^h*(2*i)+j=2^(h+1)*i+j := by rw [pow_succ]; ring
      rw [he]
      exact hl j (hj.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    have hR := ih (2*i+1) hhl hcr (fun j hj => by
      have he : 2^h*(2*i+1)+j=2^(h+1)*i+(2^h+j) := by rw [pow_succ]; ring
      rw [he]
      exact hl (2^h+j) (by rw [pow_succ]; omega))
    rw [SymbolicFixedTablePolynomialTree.tree, hL, hR, hdl, hdr, hd,
      reference_node_degree bits h (2*i) hhl, reference_node_degree bits h (2*i+1) hhl,
      ← reference_direction bits h i, cannyResultantWithDegrees_exact]
    simp only [SymbolicFixedTable.node]

theorem table_consistent_subtree (bits : List Bool) (h i : ℕ)
    (hh : h≤height bits) (hi : i<2^(height bits-h)) :
    BalancedTablePolynomials.Consistent (PaddedAnnihilatorBits.family retainedFamily retainedCount)
      (tablePrepare bits) (referenceLeaves bits) h i :=
  BalancedSubtreeLocality.consistent_subtree _ _ _ _ _ _ hh hi (table_consistent_reference bits)

theorem interval_index_lt (bits : List Bool) (h i j : ℕ) (hh : h≤height bits)
    (hi : i<2^(height bits-h)) (hj : j<2^h) : 2^h*i+j<2^(height bits) := by
  have hp : 2^h*2^(height bits-h)=2^(height bits) := by
    rw [← pow_add, Nat.add_sub_of_le hh]
  have hx : 2^h*i+j<2^h*(i+1) := by nlinarith
  exact hx.trans_le ((Nat.mul_le_mul_left (2^h) (Nat.succ_le_of_lt hi)).trans_eq hp)

theorem index_lt_of_interval (bits : List Bool) (h i : ℕ) (hh : h≤height bits)
    (hi : 2^h*(i+1)≤2^(height bits)) : i<2^(height bits-h) := by
  have hp : 2^h*2^(height bits-h)=2^(height bits) := by
    rw [← pow_add, Nat.add_sub_of_le hh]
  by_contra hn
  have hI : 2^(height bits-h) ≤ i := by omega
  have hm := Nat.mul_le_mul_left (2^h) hI
  have hz := Nat.two_pow_pos h
  rw [← hp] at hi
  nlinarith

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
  apply symbolic_tree_eq bits h i hh (table_consistent_subtree bits h i hh hi)
  intro j hj
  exact leaf_eq_reference bits _ ((interval_index_lt bits h i j hh hi hj).trans_le
    (FiniteAnnihilatorTree.width_bound (dimension bits+1)))

theorem table_direction_reference (bits : List Bool) (h i : ℕ)
    (hh : h+1≤height bits) (hi : i<2^(height bits-(h+1))) :
    BalancedMetadataTable.direction (BalancedParameterContext.packet (tablePrepare bits) (h+1) i) =
      (CoercivePreparationControls.family bits).directions h i :=
  (table_consistent_subtree bits (h+1) i hh hi).2.2.2.2.trans (reference_direction bits h i).symm

theorem height_lt (bits : List Bool) : height bits<(retainedCount (prepare bits)).size := by
  apply Nat.lt_size.mpr
  simpa only [height, retainedCount, prepare_source, count] using
    FiniteAnnihilatorTree.width_bound (dimension bits+1)

/-- Root-inclusive order metadata is exact. Its parent exists in the enlarged
integer table even at the original symbolic root. -/
theorem table_order_reference (bits : List Bool) (h i : ℕ)
    (hh : h≤height bits) (hi : i<2^(height bits-h)) :
    BalancedMetadataTable.order (BalancedParameterContext.packet (tablePrepare bits) h i) =
      (SymbolicFixedTable.node (fun j => SymbolicScaledSquarefree.polynomial
        ((CoercivePreparationControls.family bits).padded j))
        (CoercivePreparationControls.family bits).directions h i).natDegree := by
  let H := (retainedCount (prepare bits)).size
  have hhH : h+1≤H := by have ht := height_lt bits; dsimp [H]; omega
  have hiH : i<2^(H-h) := hi.trans_le (Nat.pow_le_pow_right (by decide) (by
    have ht := height_lt bits; dsimp [H]; omega))
  have hp : i/2<2^(H-(h+1)) := by
    have he : H-h=(H-(h+1))+1 := by omega
    rw [he, pow_succ] at hiH
    omega
  have hc := BalancedSubtreeLocality.consistent_subtree
    (PaddedAnnihilatorBits.family retainedFamily retainedCount) (tablePrepare bits)
    (integerLeaves bits) H (h+1) (i/2) hhH hp (table_consistent_integer bits)
  have ho : BalancedMetadataTable.order (BalancedParameterContext.packet (tablePrepare bits) h i) =
      (BalancedPrimitiveTree.node (integerLeaves bits) h i).polynomial.natDegree := by
    by_cases he : i%2=0
    · have hi0 : 2*(i/2)=i := by have hm := Nat.mod_add_div i 2; omega
      simpa only [hi0] using hc.2.2.1
    · have hi1 : 2*(i/2)+1=i := by
        have hm := Nat.mod_add_div i 2
        have hb := Nat.mod_lt i (by decide : 0<2)
        omega
      simpa only [hi1] using hc.2.2.2.1
  have hn := BalancedSubtreeLocality.node_polynomial_congr (integerLeaves bits) (referenceLeaves bits) h i
    (fun j hj => integer_leaf_polynomial bits _ ((interval_index_lt bits h i j hh hi hj).trans_le
      (FiniteAnnihilatorTree.width_bound (dimension bits+1))))
  exact ho.trans ((congrArg Polynomial.natDegree hn).trans (reference_node_degree bits h i hh))

/-- The polynomial computed by the total malformed-frame scheduler is the
actual source reference parameter on the concrete native prepared table. -/
theorem tree_eq_parameter (bits : List Bool) :
    SymbolicFixedTablePolynomialTree.tree CoerciveFormalLeafReader.leaf (tablePrepare bits) (height bits) 0 =
      (CoercivePreparationControls.family bits).parameter := by
  apply symbolic_tree_eq bits (height bits) 0 le_rfl (table_consistent_reference bits)
  intro j hj
  have hi : j<count bits := hj.trans_le (FiniteAnnihilatorTree.width_bound (dimension bits+1))
  simp only [Nat.mul_zero, Nat.zero_add]
  unfold CoerciveFormalLeafReader.leaf CoerciveFormalLeafReader.payloadInput
  simp only [pairFst_pair, pairSnd_pair, tablePrepare_source]
  rw [CoerciveFormalLeafReader.payloadLeaf_prepare bits j hi]
  simp only [raw, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.ETR.CoerciveTableCorrectness
