/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleProbeEntries
public import LeanCanny.Encoding.BoundedCriticalSamplePointProbe

/-! # Correctness of native constant entries at actual-sample descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleIndexedProbeFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical BigOperators

noncomputable def context (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) : List Bool :=
  pair (BoundedCriticalSampleHashChoice.value P c) (pair (SignStatisticBits.integerCode h) d)

theorem hash_original (P : Readers) (c : List Bool) :
    BoundedCriticalSampleWeightedMoments.original (BoundedCriticalSampleHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleHashChoice.value_spec P c
  rw [hv]
  simp only [BoundedCriticalSampleWeightedMoments.original, BoundedCriticalSampleWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) :
    BoundedCriticalSampleProbeEntries.dimension (context P c h d) = BoundedCriticalSampleCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleHashChoice.value_spec P c
  simp only [BoundedCriticalSampleProbeEntries.dimension, context,
    BoundedCriticalSampleProbeEntries.hashContext, pairFst_pair]
  rw [hv, BoundedCriticalSamplePencilSource.dimension_context]

noncomputable def indexEquiv (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) :
    Fin (BoundedCriticalSampleCount.count P c) ≃ Fin (BoundedCriticalSampleProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool)
    (i : Fin (BoundedCriticalSampleCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (BoundedCriticalSampleCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    BoundedCriticalSampleProbeEntries.entryQuery (row P c h d i j) = pair (BoundedCriticalSampleHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [BoundedCriticalSampleProbeEntries.entryQuery, row, context,
    BoundedCriticalSampleProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] BoundedCriticalSampleProbeEntries.gram BoundedCriticalSampleProbeEntries.weighted
  BoundedCriticalSampleProbeEntries.constant BoundedCriticalSampleWeightedMoments.entry

theorem gram_packet (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (BoundedCriticalSampleProbeEntries.gram P (row P c h d i j) : ℚ) = BoundedCriticalSampleBasisGram.gram P c i j := by
  have hq : BoundedCriticalSamplePencilEntries.gramQuery (BoundedCriticalSampleProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [BoundedCriticalSamplePencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [BoundedCriticalSampleProbeEntries.gram, BoundedCriticalSamplePencilEntries.gram, hq]
  exact BoundedCriticalSampleBasisGram.entry_packet P c i j

theorem weighted_packet (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (BoundedCriticalSampleProbeEntries.weighted P (row P c h d i j) : ℚ) =
      BoundedCriticalSampleBasisPencil.weighted P c (BoundedCriticalSamplePointProbe.hashFunction P c) i j := by
  rw [BoundedCriticalSampleProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleHashChoice.value_spec P c
  have hh : BoundedCriticalSamplePointProbe.hashFunction P c =
      fun x => (BoundedCriticalSampleRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold BoundedCriticalSamplePointProbe.hashFunction BoundedCriticalSampleHashChoice.hash
    rw [hv]
    simp only [BoundedCriticalSampleWeightedMoments.context, BoundedCriticalSampleWeightedMoments.modulus,
      BoundedCriticalSampleWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact BoundedCriticalSampleWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Readers) (c : List Bool) (h : ℤ) (d : List Bool) (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (BoundedCriticalSampleProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * BoundedCriticalSampleBasisGram.gram P c i j -
        BoundedCriticalSampleBasisPencil.weighted P c (BoundedCriticalSamplePointProbe.hashFunction P c) i j := by
  have hp : BoundedCriticalSampleProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, BoundedCriticalSampleProbeEntries.pointValue,
      BoundedCriticalSampleProbeEntries.pointCode, pairSnd_pair, SignedIntegerArithmetic.value_packet]
  rw [BoundedCriticalSampleProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

end LeanCanny.Encoding.BoundedCriticalSampleIndexedProbeFrame
