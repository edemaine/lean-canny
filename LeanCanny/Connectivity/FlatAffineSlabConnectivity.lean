/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphCover

/-! # Native PSPACE connectivity for actual checked affine root slabs

The original source supplies the complete accessible cover. The algorithm
validates the scalar context and runs the native finite graph algorithm;
neither a geometric cover nor its adjacency is an oracle input.

This is the finite root-curve slab result. Recursive connections inside
positive-dimensional hypersurface slices remain separate obligations.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabConnectivity
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem exists_cover (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) :
    Nonempty (BitFrontierCover (FlatAffineSlabGraphBranches.Space F cone height c)
      (FlatAffineSlabGraphCodes.width F cone height c)
      (FlatAffineSlabGraph.edge F cone height c) (FlatAffineSlabGraph.valid F cone height c)) := by
  obtain ⟨hfin, ⟨B⟩⟩ := FlatAffineSlabGraphBranches.exists_family F cone height c hc
  let : Finite (FlatAffineSlabGraphArcs.Index F cone height c) := hfin
  let : Fintype (FlatAffineSlabGraphArcs.Index F cone height c) := Fintype.ofFinite _
  let : LinearOrder (FlatAffineSlabGraphArcs.Index F cone height c) := linearOrderOfSTO WellOrderingRel
  exact ⟨B.cover hc⟩

theorem connected_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) :
    IsPreconnected (univ : Set (FlatAffineSlabGraphBranches.Space F cone height c)) ↔
      c ∈ FlatAffineSlabGraph.connectedLanguage F cone height := by
  obtain ⟨C⟩ := exists_cover F cone height c hc
  exact C.isPreconnected_iff_connected

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {c | c ∈ FlatAffineSlabGraphContext.language F cone height ∧
    IsPreconnected (univ : Set (FlatAffineSlabGraphBranches.Space F cone height c))}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (language F cone height) := by
  have V := (FlatAffineSlabGraphContext.decider h cone height hh).flagEvaluator
  have C := (FlatAffineSlabGraph.connectedDecider h cone height hh).flagEvaluator
  apply (V.andFlags C).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro c
  simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]
  exact and_congr_right (fun hc => connected_iff F cone height c hc)

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

end LeanCanny.Connectivity.FlatAffineSlabConnectivity
