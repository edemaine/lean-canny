/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CoordinateAffineTerminalCover

/-! # Native whole-set connectivity of actual terminal coordinate slices

The original readers supply complete children, their graph, and the constructed
accessible cover. The native algorithm validates the parent and terminal flag
and decides connectivity of the actual slice, including the empty slice.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open CoordinateAffinePrefix (inputs)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def normalize (q : List Bool) : List Bool := pair (pairFst q) (pairSnd q)
theorem normalize_FP : normalize ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP
def terminal (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ) (q : List Bool) : Prop :=
  P.dim (pairFst q) + 3 ≤ objective (FlatAffineFullSourceTower.stage (pairFst q) (depth (pairFst q)))

theorem terminal_pred {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn objective) : FPPred (terminal P depth objective) := by
  have H := (CoordinateAffineTerminalReachability.terminal_pred hP hd ho).comp (mem_FP_pair id_mem_FP (constFn_mem_FP []))
  apply H.of_iff
  intro q
  simp only [CoordinateAffineTerminalReachability.terminal, CoordinateAffineTerminalReachability.source, pairFst_pair]
  rfl

noncomputable def conditions (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v : List Bool) : Prop :=
  P.dim u + 3 ≤ objective (FlatAffineFullSourceTower.stage u (depth u)) ∧
    ∃ hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
      (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u v,
      IsPreconnected (FlatAffineCompactComponentCover.Slice (inputs P depth objective level)
        (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv)

noncomputable def language (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | conditions P depth objective level (pairFst q) (pairSnd q)}

attribute [local irreducible] CoordinateAffineTerminalGraph.connectedLanguage

theorem decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : SpaceDecider (language P depth objective level) := by
  let F := inputs P depth objective level
  let C := CoordinateAffineSliceRegularity.cone P depth objective level
  have T := SpaceFunction.ofFP _ (terminal_pred hP hd ho).flag_mem_FP
  have V := (SpaceDecider.ofPSPACE (FlatAffineCompleteVertices.mem_PSPACE (CoordinateAffinePrefix.access hP hd ho hl hA) (parentCone F C))).flagEvaluator
  have G := ((CoordinateAffineTerminalGraph.connectedDecider hP hd ho hl hA).precompose normalize normalize_FP).flagEvaluator
  apply (T.andFlags (V.andFlags G)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, conditions, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]
  constructor
  · rintro ⟨Ht, hv, HC⟩
    refine ⟨Ht, ?_, ?_⟩
    · change FlatAffineCompleteVertices.Valid F (parentCone F C) (pairFst q) (pairSnd q)
      exact hv
    · exact (CoordinateAffineTerminalCover.connected_iff P depth objective level (pairFst q) (pairSnd q) hv Ht).mp HC
  · rintro ⟨Ht, HV, HG⟩
    have hv : FlatAffineCompleteVertices.Valid F (parentCone F C) (pairFst q) (pairSnd q) := HV
    exact ⟨Ht, hv, (CoordinateAffineTerminalCover.connected_iff P depth objective level (pairFst q) (pairSnd q) hv Ht).mpr HG⟩

theorem mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : language P depth objective level ∈ PSPACE :=
  (decider hP hd ho hl hA).mem_PSPACE

theorem packet (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v : List Bool)
    (hmax : P.dim u + 3 ≤ objective (FlatAffineFullSourceTower.stage u (depth u)))
    (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
      (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u v) :
    pair u v ∈ language P depth objective level ↔
      IsPreconnected (FlatAffineCompactComponentCover.Slice (inputs P depth objective level)
        (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) := by
  change conditions P depth objective level (pairFst (pair u v)) (pairSnd (pair u v)) ↔ _
  rw [pairFst_pair, pairSnd_pair]
  simp only [conditions, hmax, true_and]
  exact ⟨fun ⟨_, H⟩ => H, fun H => ⟨hv, H⟩⟩

end LeanCanny.Connectivity.CoordinateAffineTerminalConnectivity
