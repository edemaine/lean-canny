/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateAffineTerminalSamples
public import LeanCanny.Encoding.FlatAffineChildSpatialEquality

/-! # Native reachability at the terminal coordinate slice

The query contains a source, a complete parent label, and two complete child
labels. Native guards check the terminal coordinate selection and both exact
ancestries. The finite slice has no paths between distinct points, so native
spatial equality decides its actual point-to-point reachability.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateAffineTerminalReachability
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open CoordinateAffinePrefix (inputs)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def parent (q : List Bool) : List Bool := pairSnd (pairFst q)
def word (right : Bool) (q : List Bool) : List Bool := if right then pairSnd (pairSnd q) else pairFst (pairSnd q)
theorem source_FP : source ∈ FP := by polytime [source]
def childQuery (right : Bool) (q : List Bool) : List Bool := pair (source q) (pair (word right q) (parent q))
def equalityQuery (q : List Bool) : List Bool := pair (source q) (pair (word false q) (word true q))
theorem childQuery_FP (right : Bool) : childQuery right ∈ FP := by cases right <;> polytime [childQuery, source, word, parent]
theorem equalityQuery_FP : equalityQuery ∈ FP := by polytime [equalityQuery, source, word]

def terminal (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ) (q : List Bool) : Prop :=
  P.dim (source q) + 3 ≤ objective (FlatAffineFullSourceTower.stage (source q) (depth (source q)))

theorem terminal_pred {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn objective) : FPPred (terminal P depth objective) := by
  have Q : (fun q => FlatAffineFullSourceTower.stage (source q) (depth (source q))) ∈ FP :=
    mem_FP_pair source_FP (BinaryFn.ofUnary (hd.comp source_FP)).bits_mem_FP
  exact FPPred.le ((hP.dim.comp source_FP).add (UnaryFn.const 3)) (ho.comp Q)

noncomputable def language (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | terminal P depth objective q ∧
    childQuery false q ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) ∧
    childQuery true q ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) ∧
    equalityQuery q ∈ FlatAffineChildSpatialEquality.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)}

theorem decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (language P depth objective level) := by
  have A := CoordinateAffinePrefix.access hP hd ho hl hA
  let C := CoordinateAffineSliceRegularity.cone P depth objective level
  have D := FlatAffineCompleteChildLabels.decider A C
  have L := (D.precompose (childQuery false) (childQuery_FP false)).flagEvaluator
  have R := (D.precompose (childQuery true) (childQuery_FP true)).flagEvaluator
  have E := ((FlatAffineChildSpatialEquality.decider A C).precompose equalityQuery equalityQuery_FP).flagEvaluator
  have T := SpaceFunction.ofFP _ (terminal_pred hP hd ho).flag_mem_FP
  apply (T.andFlags (L.andFlags (R.andFlags E))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    language P depth objective level ∈ PSPACE := (decider hP hd ho hl hA).mem_PSPACE

theorem packet (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v w z : List Bool)
    (hmax : P.dim u + 3 ≤ objective (FlatAffineFullSourceTower.stage u (depth u)))
    (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
      (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u v)
    (hw : FlatAffineCompleteVertices.Valid (next (inputs P depth objective level)) (CoordinateAffineSliceRegularity.cone P depth objective level) u w)
    (hz : FlatAffineCompleteVertices.Valid (next (inputs P depth objective level)) (CoordinateAffineSliceRegularity.cone P depth objective level) u z) :
    pair (pair u v) (pair w z) ∈ language P depth objective level ↔
      pair u (pair w v) ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) ∧
      pair u (pair z v) ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) ∧
      JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P depth objective level) u
        (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level)
          (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u ⟨v, hv⟩))
        (newest (inputs P depth objective level) u (FlatAffineCompleteVertices.vertexEquiv (next (inputs P depth objective level))
          (CoordinateAffineSliceRegularity.cone P depth objective level) u ⟨w, hw⟩).val ∘ Sum.inl)
        (newest (inputs P depth objective level) u (FlatAffineCompleteVertices.vertexEquiv (next (inputs P depth objective level))
          (CoordinateAffineSliceRegularity.cone P depth objective level) u ⟨z, hz⟩).val ∘ Sum.inl) := by
  let F := inputs P depth objective level
  let C := CoordinateAffineSliceRegularity.cone P depth objective level
  let x := FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) u ⟨v, hv⟩
  have IN (a : List Bool) (ha : FlatAffineCompleteVertices.Valid (next F) C u a)
      (HA : pair u (pair a v) ∈ FlatAffineCompleteChildLabels.language F C) :
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) C u ⟨a, ha⟩).val ∘ Sum.inl ∈ FlatAffineCompleteComponentSamples.slice F u x := by
    have HP := (FlatAffineCompleteChildLabels.packet F C u a v ha hv).mp HA
    have H := FlatAffineCompleteChildGeometry.newest_slice F u (FlatAffineCompleteVertices.vertexEquiv (next F) C u ⟨a, ha⟩)
    rwa [HP] at H
  simp only [language, Set.mem_ofPred_eq, terminal, source, childQuery, equalityQuery, word, parent,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true, hmax, true_and]
  rw [FlatAffineChildSpatialEquality.packet _ _ u w z hw hz]
  constructor
  · rintro ⟨HA, HB, HE⟩
    exact ⟨HA, HB, (CoordinateAffineTerminalSamples.joined_iff_eq P depth objective level u x hmax _ _ (IN w hw HA)).mpr HE.symm⟩
  · rintro ⟨HA, HB, HE⟩
    exact ⟨HA, HB, ((CoordinateAffineTerminalSamples.joined_iff_eq P depth objective level u x hmax _ _ (IN w hw HA)).mp HE).symm⟩

end LeanCanny.Connectivity.CoordinateAffineTerminalReachability
