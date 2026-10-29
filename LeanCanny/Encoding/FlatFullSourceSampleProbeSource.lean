/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleProbeEntries
public import LeanCanny.Encoding.FlatFullSourceSamplePointProbe

/-! # Correctness of native constant entries at regular flat descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

noncomputable def context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  FlatFullSourceSampleProbeEntries.context (FlatFullSourceSampleHashChoice.value P c) h d

theorem hash_original (P : Inputs) (c : List Bool) :
    FlatFullSourceSampleWeightedMoments.original (FlatFullSourceSampleHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := FlatFullSourceSampleHashChoice.value_spec P c
  rw [hv]
  simp only [FlatFullSourceSampleWeightedMoments.original, FlatFullSourceSampleWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    FlatFullSourceSampleProbeEntries.dimension (context P c h d) = FlatFullSourceSampleRegularCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := FlatFullSourceSampleHashChoice.value_spec P c
  simp only [FlatFullSourceSampleProbeEntries.dimension, context, FlatFullSourceSampleProbeEntries.context,
    FlatFullSourceSampleProbeEntries.hashContext, pairFst_pair]
  rw [hv, FlatFullSourceSamplePencilSource.dimension_context]

noncomputable def indexEquiv (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    Fin (FlatFullSourceSampleRegularCount.count P c) ≃ Fin (FlatFullSourceSampleProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i : Fin (FlatFullSourceSampleRegularCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    FlatFullSourceSampleProbeEntries.entryQuery (row P c h d i j) = pair (FlatFullSourceSampleHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [FlatFullSourceSampleProbeEntries.entryQuery, row, context, FlatFullSourceSampleProbeEntries.context,
    FlatFullSourceSampleProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] FlatFullSourceSampleProbeEntries.gram FlatFullSourceSampleProbeEntries.weighted
  FlatFullSourceSampleProbeEntries.constant FlatFullSourceSampleWeightedMoments.entry

theorem gram_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (FlatFullSourceSampleProbeEntries.gram P (row P c h d i j) : ℚ) = FlatFullSourceSampleBasisGram.gram P c i j := by
  have hq : FlatFullSourceSamplePencilEntries.gramQuery (FlatFullSourceSampleProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [FlatFullSourceSamplePencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [FlatFullSourceSampleProbeEntries.gram, FlatFullSourceSamplePencilEntries.gram, hq]
  exact FlatFullSourceSampleBasisGram.entry_packet P c i j

theorem weighted_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (FlatFullSourceSampleProbeEntries.weighted P (row P c h d i j) : ℚ) =
      FlatFullSourceSampleBasisPencil.weighted P c (FlatFullSourceSamplePointProbe.hashFunction P c) i j := by
  rw [FlatFullSourceSampleProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := FlatFullSourceSampleHashChoice.value_spec P c
  have hh : FlatFullSourceSamplePointProbe.hashFunction P c =
      fun x => (FlatFullSourceSampleRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold FlatFullSourceSamplePointProbe.hashFunction FlatFullSourceSampleHashChoice.hash
    rw [hv]
    simp only [FlatFullSourceSampleWeightedMoments.context, FlatFullSourceSampleWeightedMoments.modulus,
      FlatFullSourceSampleWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact FlatFullSourceSampleWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (FlatFullSourceSampleProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * FlatFullSourceSampleBasisGram.gram P c i j -
        FlatFullSourceSampleBasisPencil.weighted P c (FlatFullSourceSamplePointProbe.hashFunction P c) i j := by
  have hp : FlatFullSourceSampleProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, FlatFullSourceSampleProbeEntries.pointValue_packet]
  rw [FlatFullSourceSampleProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

end LeanCanny.Encoding.FlatFullSourceSampleProbeSource
