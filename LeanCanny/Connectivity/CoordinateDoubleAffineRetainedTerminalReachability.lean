/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRetainedPointChildMatch
public import LeanCanny.Connectivity.CoordinateDoubleAffineTerminalReachability

/-! # Native terminal paths between retained ancestor points

A terminal coordinate slice is finite, not necessarily a singleton. A valid
stage reference need not lie in the current slice. The algorithm searches
complete terminal child labels for one actual slice point equal to both
references. This simultaneously checks endpoint membership and equality.
Terminal completeness and finiteness make acceptance exactly `JoinedIn`.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineRetainedTerminalReachability
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open CoordinateDoubleAffinePrefix (inputs)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineRetainedPointChildMatch (record point)
open scoped Classical

noncomputable def language (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | CoordinateDoubleAffineTerminalReachability.terminal P depth objective q ∧
    q ∈ FlatAffineRetainedPointChildMatch.hits (inputs P depth objective level)
      (CoordinateDoubleAffineSliceRegularity.cone P depth objective level)}

theorem decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (language P depth objective level) := by
  have A := CoordinateDoubleAffinePrefix.access hP hd ho hl hA
  have T := SpaceFunction.ofFP _ (CoordinateDoubleAffineTerminalReachability.terminal_pred hP hd ho).flag_mem_FP
  have E := (FlatAffineRetainedPointChildMatch.hits_decider A
    (CoordinateDoubleAffineSliceRegularity.cone P depth objective level)).flagEvaluator
  apply (T.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    language P depth objective level ∈ PSPACE := (decider hP hd ho hl hA).mem_PSPACE

theorem packet (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v : List Bool)
    (hmax : P.dim u + 3 ≤ objective (FlatAffineFullSourceTower.stage u (depth u)))
    (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
      (FlatAffineCompleteChildLabels.parentCone (inputs P depth objective level)
        (CoordinateDoubleAffineSliceRegularity.cone P depth objective level)) u v)
    (a b : Fin (depth u)) :
    record u v a.val b.val ∈ language P depth objective level ↔
      JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P depth objective level) u
        (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level)
          (FlatAffineCompleteChildLabels.parentCone (inputs P depth objective level)
            (CoordinateDoubleAffineSliceRegularity.cone P depth objective level)) u ⟨v, hv⟩))
        (point (inputs P depth objective level) u
          (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level)
            (FlatAffineCompleteChildLabels.parentCone (inputs P depth objective level)
              (CoordinateDoubleAffineSliceRegularity.cone P depth objective level)) u ⟨v, hv⟩) a)
        (point (inputs P depth objective level) u
          (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level)
            (FlatAffineCompleteChildLabels.parentCone (inputs P depth objective level)
              (CoordinateDoubleAffineSliceRegularity.cone P depth objective level)) u ⟨v, hv⟩) b) := by
  let F := inputs P depth objective level
  let cone := CoordinateDoubleAffineSliceRegularity.cone P depth objective level
  let x := FlatAffineCompleteVertices.vertexEquiv F (FlatAffineCompleteChildLabels.parentCone F cone) u ⟨v, hv⟩
  have HT : CoordinateDoubleAffineTerminalReachability.terminal P depth objective (record u v a.val b.val) := by
    simpa only [CoordinateDoubleAffineTerminalReachability.terminal,
      CoordinateDoubleAffineTerminalReachability.source, record, pairFst_pair] using hmax
  change (CoordinateDoubleAffineTerminalReachability.terminal P depth objective (record u v a.val b.val) ∧
    record u v a.val b.val ∈ FlatAffineRetainedPointChildMatch.hits F cone) ↔
      JoinedIn (FlatAffineCompleteComponentSamples.slice F u x) (point F u x a) (point F u x b)
  rw [and_iff_right HT]
  constructor
  · rintro ⟨z, _, hmatch⟩
    have hz : FlatAffineCompleteVertices.Valid (next F) cone u z := by
      simpa only [FlatAffineRetainedPointChildMatch.source, record, pairFst_pair] using
        (FlatAffineRetainedPointChildMatch.valid F cone (record u v a.val b.val) z hmatch).1
    obtain ⟨hp, ha, hb⟩ := (FlatAffineRetainedPointChildMatch.packet F cone u v z a b hv hz).mp hmatch
    let y := newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩).val ∘ Sum.inl
    have Hmem := FlatAffineCompleteChildGeometry.newest_slice F u
      (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨z, hz⟩)
    have hmem : y ∈ FlatAffineCompleteComponentSamples.slice F u x :=
      (Iff.of_eq (congrArg (fun root => y ∈ FlatAffineCompleteComponentSamples.slice F u root) hp)).mp Hmem
    rw [ha, hb]
    exact JoinedIn.refl hmem
  · intro hpath
    have he : point F u x b = point F u x a :=
      (CoordinateDoubleAffineTerminalSamples.joined_iff_eq P depth objective level u x hmax
        (point F u x a) (point F u x b) hpath.source_mem).mp hpath
    obtain ⟨z, hp, hzpoint⟩ := CoordinateDoubleAffineTerminalSamples.exists_label P depth objective level u x hmax
      (point F u x a) hpath.source_mem
    refine ⟨z.val, ?_, (FlatAffineRetainedPointChildMatch.packet F cone u v z.val a b hv z.property).mpr
      ⟨hp, hzpoint.symm, he.trans hzpoint.symm⟩⟩
    simpa only [FlatAffineRetainedPointChildMatch.source, record, pairFst_pair] using
      FlatAffineCompleteVertices.word_length (next F) cone u z.val z.property

end LeanCanny.Connectivity.CoordinateDoubleAffineRetainedTerminalReachability
