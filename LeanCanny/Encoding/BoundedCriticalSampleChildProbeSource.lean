/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildProbeEntries
public import LeanCanny.Encoding.BoundedCriticalSampleChildPointProbe

/-! # Correctness of native constant entries at regular-child descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  BoundedCriticalSampleChildProbeEntries.context (BoundedCriticalSampleChildHashChoice.value P c) h d

theorem hash_original (P : Inputs) (c : List Bool) :
    BoundedCriticalSampleChildWeightedMoments.original (BoundedCriticalSampleChildHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleChildHashChoice.value_spec P c
  rw [hv]
  simp only [BoundedCriticalSampleChildWeightedMoments.original, BoundedCriticalSampleChildWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    BoundedCriticalSampleChildProbeEntries.dimension (context P c h d) = BoundedCriticalSampleChildRegularCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleChildHashChoice.value_spec P c
  simp only [BoundedCriticalSampleChildProbeEntries.dimension, context, BoundedCriticalSampleChildProbeEntries.context,
    BoundedCriticalSampleChildProbeEntries.hashContext, pairFst_pair]
  rw [hv, BoundedCriticalSampleChildPencilSource.dimension_context]

noncomputable def indexEquiv (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    Fin (BoundedCriticalSampleChildRegularCount.count P c) ≃ Fin (BoundedCriticalSampleChildProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i : Fin (BoundedCriticalSampleChildRegularCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    BoundedCriticalSampleChildProbeEntries.entryQuery (row P c h d i j) = pair (BoundedCriticalSampleChildHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [BoundedCriticalSampleChildProbeEntries.entryQuery, row, context, BoundedCriticalSampleChildProbeEntries.context,
    BoundedCriticalSampleChildProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] BoundedCriticalSampleChildProbeEntries.gram BoundedCriticalSampleChildProbeEntries.weighted
  BoundedCriticalSampleChildProbeEntries.constant BoundedCriticalSampleChildWeightedMoments.entry

theorem gram_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (BoundedCriticalSampleChildProbeEntries.gram P (row P c h d i j) : ℚ) = BoundedCriticalSampleChildBasisGram.gram P c i j := by
  have hq : BoundedCriticalSampleChildPencilEntries.gramQuery (BoundedCriticalSampleChildProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [BoundedCriticalSampleChildPencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [BoundedCriticalSampleChildProbeEntries.gram, BoundedCriticalSampleChildPencilEntries.gram, hq]
  exact BoundedCriticalSampleChildBasisGram.entry_packet P c i j

theorem weighted_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (BoundedCriticalSampleChildProbeEntries.weighted P (row P c h d i j) : ℚ) =
      BoundedCriticalSampleChildBasisPencil.weighted P c (BoundedCriticalSampleChildPointProbe.hashFunction P c) i j := by
  rw [BoundedCriticalSampleChildProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleChildHashChoice.value_spec P c
  have hh : BoundedCriticalSampleChildPointProbe.hashFunction P c =
      fun x => (BoundedCriticalSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold BoundedCriticalSampleChildPointProbe.hashFunction BoundedCriticalSampleChildHashChoice.hash
    rw [hv]
    simp only [BoundedCriticalSampleChildWeightedMoments.context, BoundedCriticalSampleChildWeightedMoments.modulus,
      BoundedCriticalSampleChildWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact BoundedCriticalSampleChildWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (BoundedCriticalSampleChildProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * BoundedCriticalSampleChildBasisGram.gram P c i j -
        BoundedCriticalSampleChildBasisPencil.weighted P c (BoundedCriticalSampleChildPointProbe.hashFunction P c) i j := by
  have hp : BoundedCriticalSampleChildProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, BoundedCriticalSampleChildProbeEntries.pointValue_packet]
  rw [BoundedCriticalSampleChildProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

end LeanCanny.Encoding.BoundedCriticalSampleChildProbeSource
