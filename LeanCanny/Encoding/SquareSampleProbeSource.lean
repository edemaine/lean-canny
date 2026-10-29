/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProbeEntries
public import LeanCanny.Encoding.SquareSamplePointProbe

/-! # Correctness of native constant entries at regular square-system descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProbeSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open SquareSampleInput (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

noncomputable def context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  SquareSampleProbeEntries.context (SquareSampleHashChoice.value P c) h d

theorem hash_original (P : Inputs) (c : List Bool) :
    SquareSampleWeightedMoments.original (SquareSampleHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := SquareSampleHashChoice.value_spec P c
  rw [hv]
  simp only [SquareSampleWeightedMoments.original, SquareSampleWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    SquareSampleProbeEntries.dimension (context P c h d) = SquareSampleRegularCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := SquareSampleHashChoice.value_spec P c
  simp only [SquareSampleProbeEntries.dimension, context, SquareSampleProbeEntries.context,
    SquareSampleProbeEntries.hashContext, pairFst_pair]
  rw [hv, SquareSamplePencilSource.dimension_context]

noncomputable def indexEquiv (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    Fin (SquareSampleRegularCount.count P c) ≃ Fin (SquareSampleProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i : Fin (SquareSampleRegularCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i j : Fin (SquareSampleRegularCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (SquareSampleRegularCount.count P c)) :
    SquareSampleProbeEntries.entryQuery (row P c h d i j) = pair (SquareSampleHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [SquareSampleProbeEntries.entryQuery, row, context, SquareSampleProbeEntries.context,
    SquareSampleProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] SquareSampleProbeEntries.gram SquareSampleProbeEntries.weighted
  SquareSampleProbeEntries.constant SquareSampleWeightedMoments.entry

theorem gram_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (SquareSampleRegularCount.count P c)) :
    (SquareSampleProbeEntries.gram P (row P c h d i j) : ℚ) = SquareSampleBasisGram.gram P c i j := by
  have hq : SquareSamplePencilEntries.gramQuery (SquareSampleProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [SquareSamplePencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [SquareSampleProbeEntries.gram, SquareSamplePencilEntries.gram, hq]
  exact SquareSampleBasisGram.entry_packet P c i j

theorem weighted_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (SquareSampleRegularCount.count P c)) :
    (SquareSampleProbeEntries.weighted P (row P c h d i j) : ℚ) =
      SquareSampleBasisPencil.weighted P c (SquareSamplePointProbe.hashFunction P c) i j := by
  rw [SquareSampleProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := SquareSampleHashChoice.value_spec P c
  have hh : SquareSamplePointProbe.hashFunction P c =
      fun x => (SquareSampleRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold SquareSamplePointProbe.hashFunction SquareSampleHashChoice.hash
    rw [hv]
    simp only [SquareSampleWeightedMoments.context, SquareSampleWeightedMoments.modulus,
      SquareSampleWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact SquareSampleWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (SquareSampleRegularCount.count P c)) :
    (SquareSampleProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * SquareSampleBasisGram.gram P c i j -
        SquareSampleBasisPencil.weighted P c (SquareSamplePointProbe.hashFunction P c) i j := by
  have hp : SquareSampleProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, SquareSampleProbeEntries.pointValue_packet]
  rw [SquareSampleProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

end LeanCanny.Encoding.SquareSampleProbeSource
