/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildProbeEntries
public import LeanCanny.Encoding.BoundedFullSampleChildPointProbe

/-! # Correctness of native constant entries at regular-child descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildIndexedProbeFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedFullSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

noncomputable def context (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) : List Bool :=
  pair (BoundedFullSampleChildHashChoice.value P c) (pair (SignStatisticBits.integerCode h) d)

theorem hash_original (P : Inputs) (c : List Bool) :
    BoundedFullSampleChildWeightedMoments.original (BoundedFullSampleChildHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedFullSampleChildHashChoice.value_spec P c
  rw [hv]
  simp only [BoundedFullSampleChildWeightedMoments.original, BoundedFullSampleChildWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) :
    BoundedFullSampleChildProbeEntries.dimension (context P c h d) = BoundedFullSampleChildRegularCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedFullSampleChildHashChoice.value_spec P c
  simp only [BoundedFullSampleChildProbeEntries.dimension, context,
    BoundedFullSampleChildProbeEntries.hashContext, pairFst_pair]
  rw [hv, BoundedFullSampleChildPencilSource.dimension_context]

noncomputable def indexEquiv (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) :
    Fin (BoundedFullSampleChildRegularCount.count P c) ≃ Fin (BoundedFullSampleChildProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool)
    (i : Fin (BoundedFullSampleChildRegularCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    BoundedFullSampleChildProbeEntries.entryQuery (row P c h d i j) = pair (BoundedFullSampleChildHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [BoundedFullSampleChildProbeEntries.entryQuery, row, context,
    BoundedFullSampleChildProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] BoundedFullSampleChildProbeEntries.gram BoundedFullSampleChildProbeEntries.weighted
  BoundedFullSampleChildProbeEntries.constant BoundedFullSampleChildWeightedMoments.entry

theorem gram_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (BoundedFullSampleChildProbeEntries.gram P (row P c h d i j) : ℚ) = BoundedFullSampleChildBasisGram.gram P c i j := by
  have hq : BoundedFullSampleChildPencilEntries.gramQuery (BoundedFullSampleChildProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [BoundedFullSampleChildPencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [BoundedFullSampleChildProbeEntries.gram, BoundedFullSampleChildPencilEntries.gram, hq]
  exact BoundedFullSampleChildBasisGram.entry_packet P c i j

theorem weighted_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (BoundedFullSampleChildProbeEntries.weighted P (row P c h d i j) : ℚ) =
      BoundedFullSampleChildBasisPencil.weighted P c (BoundedFullSampleChildPointProbe.hashFunction P c) i j := by
  rw [BoundedFullSampleChildProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedFullSampleChildHashChoice.value_spec P c
  have hh : BoundedFullSampleChildPointProbe.hashFunction P c =
      fun x => (BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold BoundedFullSampleChildPointProbe.hashFunction BoundedFullSampleChildHashChoice.hash
    rw [hv]
    simp only [BoundedFullSampleChildWeightedMoments.context, BoundedFullSampleChildWeightedMoments.modulus,
      BoundedFullSampleChildWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact BoundedFullSampleChildWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (BoundedFullSampleChildProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * BoundedFullSampleChildBasisGram.gram P c i j -
        BoundedFullSampleChildBasisPencil.weighted P c (BoundedFullSampleChildPointProbe.hashFunction P c) i j := by
  have hp : BoundedFullSampleChildProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, BoundedFullSampleChildProbeEntries.pointValue,
      BoundedFullSampleChildProbeEntries.pointCode, pairSnd_pair, SignedIntegerArithmetic.value_packet]
  rw [BoundedFullSampleChildProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

end LeanCanny.Encoding.BoundedFullSampleChildIndexedProbeFrame
