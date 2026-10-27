/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FormulaCriticalSampleLine
public import LeanCanny.Geometry.CoordinateLine

/-! # Formula line queries in the actual sample's tuple space

Scalar line parameters and updated sample tuples have identical connectivity.
These packets concern the formula's intersection with this coordinate line.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaCriticalSampleLine
open Set LeanCanny.ETR LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedCriticalSampleSlice
open scoped Classical

noncomputable def tupleSolutionSet (P : Readers) (read : List Bool → List Bool) (c r : List Bool) :
    Set (Fin (P.dim c + 4) → ℝ) :=
  {y | (FormulaView.formula (read (pair c r))).Holds (Formula.extend y)}

theorem connected_tuple_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    sampleWord P c r x ∈ connectedLanguage P f read ↔
      IsPreconnected (Geometry.CoordinateLine.piece (tupleSolutionSet P read c r) x.val ⟨f (pair c r), hi⟩) := by
  rw [Geometry.CoordinateLine.preconnected_iff]
  exact connected_sample P f read c r x hi

theorem reachable_tuple_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4)
    (a b : CriticalSampleSliceCellCover.Index P (family P f read) (sampleWord P c r x)) (s t : ℝ)
    (hs : Function.update x.val ⟨f (pair c r), hi⟩ s ∈ tupleSolutionSet P read c r)
    (ht : Function.update x.val ⟨f (pair c r), hi⟩ t ∈ tupleSolutionSet P read c r)
    (hsa : s ∈ CriticalSampleSliceCellCover.piece P (family P f read) (sampleWord P c r x) a)
    (htb : t ∈ CriticalSampleSliceCellCover.piece P (family P f read) (sampleWord P c r x) b) :
    pair (sampleWord P c r x)
      (pair (CriticalSampleSliceCellLabels.label P (family P f read) (sampleWord P c r x) a)
        (CriticalSampleSliceCellLabels.label P (family P f read) (sampleWord P c r x) b)) ∈ reachableLanguage P f read ↔
      JoinedIn (Geometry.CoordinateLine.piece (tupleSolutionSet P read c r) x.val ⟨f (pair c r), hi⟩)
        (Function.update x.val ⟨f (pair c r), hi⟩ s) (Function.update x.val ⟨f (pair c r), hi⟩ t) := by
  have hs' : s ∈ solutionSet P f read (sampleWord P c r x) := by
    rw [solutionSet_finite_sample P f read c r x hi]
    exact hs
  have ht' : t ∈ solutionSet P f read (sampleWord P c r x) := by
    rw [solutionSet_finite_sample P f read c r x hi]
    exact ht
  have hc : coordinateValid P f (sampleWord P c r x) := by
    simpa only [coordinateValid, sampleWord, context, pairFst_pair, pairSnd_pair] using hi
  rw [reachable_packet P f read _ (sampleWord_valid P c r x) hc a b s t hs' ht' hsa htb,
    solutionSet_finite_sample P f read c r x hi]
  exact (Geometry.CoordinateLine.joinedIn_iff (tupleSolutionSet P read c r) x.val ⟨f (pair c r), hi⟩ s t hs ht).symm

end LeanCanny.Connectivity.FormulaCriticalSampleLine
