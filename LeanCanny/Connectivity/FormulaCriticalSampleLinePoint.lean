/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FormulaCriticalSampleLineGeometry
public import LeanCanny.Connectivity.CriticalSampleSlicePointReachability
public import LeanCanny.Encoding.BoundedCriticalSampleTermCut

/-! # Native paths between arithmetic endpoints on sample coordinate lines

Endpoint terms are evaluated at the original actual sample. Their comparison
polynomials construct both cell labels internally. The query validates the
sample and free coordinate, and rejects endpoints outside the formula set.
Correctness is path connection in the formula's intersection with this line.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaCriticalSampleLinePoint
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open BoundedFullWriter BoundedCriticalSampleSlice
open scoped Classical

noncomputable def query (P : Readers) (f : List Bool → ℕ)
    (read left right : List Bool → List Bool) : List Bool → List Bool :=
  CriticalSampleSlicePointReachability.query P (FormulaCriticalSampleLine.family P f read)
    (BoundedCriticalSampleTermCut.family P left) (BoundedCriticalSampleTermCut.family P right)

theorem query_evaluator {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read left right : List Bool → List Bool) (hr : read ∈ FP) (hl : left ∈ FP) (hd : right ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (query P f read left right) :=
  CriticalSampleSlicePointReachability.query_evaluator h (FormulaCriticalSampleLine.access h hf read hr ha)
    (BoundedCriticalSampleTermCut.access h left hl ha) (BoundedCriticalSampleTermCut.access h right hd ha) ha

noncomputable def language (P : Readers) (f : List Bool → ℕ)
    (read left right : List Bool → List Bool) : Language :=
  query P f read left right ⁻¹' FormulaCriticalSampleLine.reachableLanguage P f read

theorem decider {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read left right : List Bool → List Bool) (hr : read ∈ FP) (hl : left ∈ FP) (hd : right ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P f read left right) := by
  apply SpaceDecider.of_computable ((FormulaCriticalSampleLine.reachable_decider h hf read hr ha).computable.comp
    (query_evaluator h hf read left right hr hl hd ha).computable)
  intro u
  simp only [language, Set.mem_preimage, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read left right : List Bool → List Bool) (hr : read ∈ FP) (hl : left ∈ FP) (hd : right ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : language P f read left right ∈ PSPACE :=
  (decider h hf read left right hr hl hd ha).mem_PSPACE

theorem sample_packet (P : Readers) (f : List Bool → ℕ) (read left right : List Bool → List Bool)
    (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    FormulaCriticalSampleLine.sampleWord P c r x ∈ language P f read left right ↔
      JoinedIn (FormulaCriticalSampleLine.solutionSet P f read (FormulaCriticalSampleLine.sampleWord P c r x))
        (BoundedCriticalSampleTermCut.value P left c r x) (BoundedCriticalSampleTermCut.value P right c r x) := by
  let u := FormulaCriticalSampleLine.sampleWord P c r x
  have hu : u ∈ valid P := FormulaCriticalSampleLine.sampleWord_valid P c r x
  have hc : FormulaCriticalSampleLine.coordinateValid P f u := by
    simpa only [u, FormulaCriticalSampleLine.coordinateValid, FormulaCriticalSampleLine.sampleWord,
      context, pairFst_pair, pairSnd_pair] using hi
  have hcut (endpoint : List Bool → List Bool) (t : ℝ) :
      SignType.sign ((specialized P (BoundedCriticalSampleTermCut.family P endpoint) u).eval t) =
        SignType.sign (t - BoundedCriticalSampleTermCut.value P endpoint c r x) := by
    dsimp only [u, FormulaCriticalSampleLine.sampleWord]
    rw [specialized_sample]
    exact BoundedCriticalSampleTermCut.sign_sample P endpoint c r x t
  have he : CriticalSampleSliceCellCover.solutionSet P (FormulaCriticalSampleLine.family P f read) u
      (CriticalSampleSliceBooleanCells.truth (FormulaRationalSource.source read) (context u)) =
        FormulaCriticalSampleLine.solutionSet P f read u :=
    FormulaCriticalSampleRationalSlice.solutionSet_eq P read _ _ u hu
  change (FormulaCriticalSampleLine.coordinateValid P f
    (pairFst (CriticalSampleSlicePointReachability.query P (FormulaCriticalSampleLine.family P f read)
      (BoundedCriticalSampleTermCut.family P left) (BoundedCriticalSampleTermCut.family P right) u)) ∧
      u ∈ CriticalSampleSlicePointReachability.language P (FormulaCriticalSampleLine.family P f read)
        (BoundedCriticalSampleTermCut.family P left) (BoundedCriticalSampleTermCut.family P right)
        (FormulaRationalSource.source read)) ↔ _
  rw [CriticalSampleSlicePointReachability.query, pairFst_pair, and_iff_right hc]
  rw [← he]
  exact CriticalSampleSlicePointReachability.packet P (FormulaCriticalSampleLine.family P f read)
    (BoundedCriticalSampleTermCut.family P left) (BoundedCriticalSampleTermCut.family P right)
    (FormulaRationalSource.source read) u hu _ _ (hcut left) (hcut right)

theorem tuple_sample_packet (P : Readers) (f : List Bool → ℕ) (read left right : List Bool → List Bool)
    (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (hi : f (pair c r) < P.dim c + 4) :
    FormulaCriticalSampleLine.sampleWord P c r x ∈ language P f read left right ↔
      JoinedIn (Geometry.CoordinateLine.piece (FormulaCriticalSampleLine.tupleSolutionSet P read c r)
        x.val ⟨f (pair c r), hi⟩)
        (Function.update x.val ⟨f (pair c r), hi⟩ (BoundedCriticalSampleTermCut.value P left c r x))
        (Function.update x.val ⟨f (pair c r), hi⟩ (BoundedCriticalSampleTermCut.value P right c r x)) := by
  rw [sample_packet P f read left right c r x hi,
    FormulaCriticalSampleLine.solutionSet_finite_sample P f read c r x hi]
  let S := FormulaCriticalSampleLine.tupleSolutionSet P read c r
  let j : Fin (P.dim c + 4) := ⟨f (pair c r), hi⟩
  let a := BoundedCriticalSampleTermCut.value P left c r x
  let b := BoundedCriticalSampleTermCut.value P right c r x
  constructor
  · intro h
    exact (Geometry.CoordinateLine.joinedIn_iff S x.val j a b h.source_mem h.target_mem).mpr h
  · intro h
    have ha : Function.update x.val j a ∈ S := h.source_mem.1
    have hb : Function.update x.val j b ∈ S := h.target_mem.1
    exact (Geometry.CoordinateLine.joinedIn_iff S x.val j a b ha hb).mp h

theorem invalid_base (P : Readers) (f : List Bool → ℕ) (read left right : List Bool → List Bool)
    (u : List Bool) (hu : u ∉ valid P) : u ∉ language P f read left right := by
  intro h
  exact CriticalSampleSliceBooleanReachability.invalid_base P _ _ u _ _ hu h.2

theorem invalid_coordinate (P : Readers) (f : List Bool → ℕ) (read left right : List Bool → List Bool)
    (u : List Bool) (hi : ¬ FormulaCriticalSampleLine.coordinateValid P f u) : u ∉ language P f read left right := by
  intro h
  exact hi (by simpa only [query, CriticalSampleSlicePointReachability.query, pairFst_pair] using h.1)

end LeanCanny.Connectivity.FormulaCriticalSampleLinePoint
