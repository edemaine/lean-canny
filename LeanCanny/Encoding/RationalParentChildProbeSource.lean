/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildProbeEntries
public import LeanCanny.Encoding.RationalParentChildPointProbe

/-! # Correctness of native constant entries at regular-child descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalParentChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

noncomputable def context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  RationalParentChildProbeEntries.context (RationalParentChildHashChoice.value P c) h d

theorem hash_original (P : Inputs) (c : List Bool) :
    RationalParentChildWeightedMoments.original (RationalParentChildHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := RationalParentChildHashChoice.value_spec P c
  rw [hv]
  simp only [RationalParentChildWeightedMoments.original, RationalParentChildWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    RationalParentChildProbeEntries.dimension (context P c h d) = RationalParentChildRegularCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := RationalParentChildHashChoice.value_spec P c
  simp only [RationalParentChildProbeEntries.dimension, context, RationalParentChildProbeEntries.context,
    RationalParentChildProbeEntries.hashContext, pairFst_pair]
  rw [hv, RationalParentChildPencilSource.dimension_context]

noncomputable def indexEquiv (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) :
    Fin (RationalParentChildRegularCount.count P c) ≃ Fin (RationalParentChildProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i : Fin (RationalParentChildRegularCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ)
    (i j : Fin (RationalParentChildRegularCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (RationalParentChildRegularCount.count P c)) :
    RationalParentChildProbeEntries.entryQuery (row P c h d i j) = pair (RationalParentChildHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [RationalParentChildProbeEntries.entryQuery, row, context, RationalParentChildProbeEntries.context,
    RationalParentChildProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] RationalParentChildProbeEntries.gram RationalParentChildProbeEntries.weighted
  RationalParentChildProbeEntries.constant RationalParentChildWeightedMoments.entry

theorem gram_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (RationalParentChildRegularCount.count P c)) :
    (RationalParentChildProbeEntries.gram P (row P c h d i j) : ℚ) = RationalParentChildBasisGram.gram P c i j := by
  have hq : RationalParentChildPencilEntries.gramQuery (RationalParentChildProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [RationalParentChildPencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [RationalParentChildProbeEntries.gram, RationalParentChildPencilEntries.gram, hq]
  exact RationalParentChildBasisGram.entry_packet P c i j

theorem weighted_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (RationalParentChildRegularCount.count P c)) :
    (RationalParentChildProbeEntries.weighted P (row P c h d i j) : ℚ) =
      RationalParentChildBasisPencil.weighted P c (RationalParentChildPointProbe.hashFunction P c) i j := by
  rw [RationalParentChildProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := RationalParentChildHashChoice.value_spec P c
  have hh : RationalParentChildPointProbe.hashFunction P c =
      fun x => (RationalParentChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold RationalParentChildPointProbe.hashFunction RationalParentChildHashChoice.hash
    rw [hv]
    simp only [RationalParentChildWeightedMoments.context, RationalParentChildWeightedMoments.modulus,
      RationalParentChildWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact RationalParentChildWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Inputs) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (RationalParentChildRegularCount.count P c)) :
    (RationalParentChildProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * RationalParentChildBasisGram.gram P c i j -
        RationalParentChildBasisPencil.weighted P c (RationalParentChildPointProbe.hashFunction P c) i j := by
  have hp : RationalParentChildProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, RationalParentChildProbeEntries.pointValue_packet]
  rw [RationalParentChildProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

end LeanCanny.Encoding.RationalParentChildProbeSource
