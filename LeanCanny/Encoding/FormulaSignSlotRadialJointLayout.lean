/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels
public import LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
public import LeanCanny.Encoding.FrozenCoordinatePermutationFP
/-! # Literal joint coordinates for two component lifts and one radial anchor

The input is pair original (pair firstBitLabel secondBitLabel). The three
integer source blocks occupy residue classes zero, one and two modulo four.
Reference tables contain actual chronological original-coordinate producers.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def original (q : List Bool) := pairFst q
def label (side : Bool) (q : List Bool) := if side then pairSnd (pairSnd q) else pairFst (pairSnd q)
def labelQuery (side : Bool) (q : List Bool) := pair (original q) (label side q)
noncomputable def source (side : Bool) (q : List Bool) := CanonicalAuxiliaryCandidateLabels.source (labelQuery side q)
theorem labelQuery_FP (side : Bool) : labelQuery side ∈ FP := by
  cases side <;> polytime [labelQuery, original, label]
theorem source_FP (side : Bool) : source side ∈ FP :=
  mem_FP_comp (labelQuery_FP side) CanonicalAuxiliaryCandidateLabels.source_FP

theorem source_original (side : Bool) (q : List Bool) : pairFst (source side q) = original q := by
  simp only [source, CanonicalAuxiliaryCandidateLabels.source, labelQuery, pairFst_pair]
theorem original_dimension_eq (q : List Bool) :
    FormulaSignSlotSource.dimension (source false q) = FormulaSignSlotSource.dimension (source true q) := by
  simp only [FormulaSignSlotSource.dimension, source_original]

noncomputable def circleCount (side : Bool) (q : List Bool) := CanonicalAuxiliaryCandidateCover.dimension (source side q)
noncomputable def spatialCount (q : List Bool) := FormulaSignSlotRadialFormalInput.spatial (source true q)
noncomputable def formalCount (q : List Bool) := FormulaSignSlotRadialFormalInput.dimension (source true q)
noncomputable def centerCount (q : List Bool) := FormulaSignSlotSource.dimension (source true q)
noncomputable def slots (q : List Bool) := max 3 (max (circleCount false q) (max (circleCount true q) (formalCount q)))
noncomputable def dimension (q : List Bool) := 4 * slots q

theorem circleCount_unary (side : Bool) : UnaryFn (circleCount side) :=
  CanonicalAuxiliaryCandidateCover.dimension_unary.comp (source_FP side)
theorem spatialCount_unary : UnaryFn spatialCount :=
  FormulaSignSlotRadialFormalInput.spatial_unary.comp (source_FP true)
theorem formalCount_unary : UnaryFn formalCount :=
  FormulaSignSlotRadialFormalInput.dimension_unary.comp (source_FP true)
theorem centerCount_unary : UnaryFn centerCount := FormulaSignSlotSource.dimension_unary.comp (source_FP true)
theorem slots_unary : UnaryFn slots := (UnaryFn.const 3).max
  ((circleCount_unary false).max ((circleCount_unary true).max formalCount_unary))
theorem dimension_unary : UnaryFn dimension := (UnaryFn.const 4).mul slots_unary

def column (tag i : ℕ) := 4 * i + tag
noncomputable def centerVariable (q : List Bool) (i : ℕ) := column 2 (spatialCount q + i)
noncomputable def radiusVariable (q : List Bool) := column 2 (spatialCount q + centerCount q)
def boundVariable : ℕ := 3
def radiusWitness : ℕ := 7
def gapWitness : ℕ := 11

theorem column_lt (q : List Bool) (tag i : ℕ) (ht : tag < 4) (hi : i < slots q) :
    column tag i < dimension q := by unfold column dimension; omega

theorem circle_lt_slots (side : Bool) (q : List Bool) : circleCount side q ≤ slots q := by
  cases side <;> unfold slots <;> omega
theorem formal_le_slots (q : List Bool) : formalCount q ≤ slots q := by unfold slots; omega
theorem centerVariable_lt (q : List Bool) (i : Fin (centerCount q)) : centerVariable q i.val < dimension q := by
  apply column_lt q 2 _ (by decide)
  have H := i.isLt
  have HF := formal_le_slots q
  change spatialCount q + (centerCount q + 1) ≤ slots q at HF
  omega
theorem radiusVariable_lt (q : List Bool) : radiusVariable q < dimension q := by
  apply column_lt q 2 _ (by decide)
  have H := formal_le_slots q
  change spatialCount q + (centerCount q + 1) ≤ slots q at H
  omega
theorem boundVariable_lt (q : List Bool) : boundVariable < dimension q := by unfold boundVariable dimension slots; omega
theorem radiusWitness_lt (q : List Bool) : radiusWitness < dimension q := by unfold radiusWitness dimension slots; omega
theorem gapWitness_lt (q : List Bool) : gapWitness < dimension q := by unfold gapWitness dimension slots; omega

def references (count tag : ℕ) := WordList.encode ((List.range count).map (fun i => BinaryNatCode.encode (column tag i)))
theorem references_FP {count tag : List Bool → ℕ} (hN : UnaryFn count) (hT : UnaryFn tag) :
    (fun q => references (count q) (tag q)) ∈ FP := by
  have HI := (BinaryFn.const 4).mul (BinaryFn.ofUnary UnaryFn.index)
  have HT : BinaryFn (fun q => tag (pairFst q)) := BinaryFn.ofUnary (hT.comp pairFst_mem_FP)
  have HE := mem_FP_pair (HI.add HT).bits_mem_FP (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (hN.replicate_mem_FP true))
  intro q
  simp only [references, FrozenCoordinatePermutationBits.encode_flatMap, List.flatMap_map,
    pairFst_pair, pairSnd_pair, List.length_replicate, column]
theorem references_lookup (count tag i : ℕ) (hi : i < count) :
    Nat.fromBitsLE (WordList.get (references count tag) i) = column tag i := by
  simp only [references, WordList.get_encode, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def centerRefs (q : List Bool) := references (centerCount q) 0
noncomputable def anchorRefs (q : List Bool) := references (spatialCount q) 2
noncomputable def circleRefs (side : Bool) (q : List Bool) := references (circleCount side q) (if side then 1 else 0)
theorem centerRefs_FP : centerRefs ∈ FP := references_FP centerCount_unary (UnaryFn.const 0)
theorem anchorRefs_FP : anchorRefs ∈ FP := references_FP spatialCount_unary (UnaryFn.const 2)
theorem circleRefs_FP (side : Bool) : circleRefs side ∈ FP := references_FP (circleCount_unary side) (UnaryFn.const _)
theorem centerRefs_lookup (q : List Bool) (i : Fin (centerCount q)) :
    Nat.fromBitsLE (WordList.get (centerRefs q) i.val) = column 0 i.val := references_lookup _ _ _ i.isLt
theorem anchorRefs_lookup (q : List Bool) (i : Fin (spatialCount q)) :
    Nat.fromBitsLE (WordList.get (anchorRefs q) i.val) = column 2 i.val := references_lookup _ _ _ i.isLt

end LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
