/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacentComplete

/-! # Native endpoint-edge queries with checked adjacent heights

One input contains a joint tuple and both scalar height labels. The query
checks their equality, validates exact adjacency, and scans all endpoint
candidates for midpoint matching.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteEdges
open LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) : Language :=
  {q | q ∈ FlatAffineEndpointFiniteAdjacent.language F cone height right ∧
    pairFst q ∈ FlatAffineEndpointFiniteMatching.language F cone height}

attribute [local irreducible] FlatAffineEndpointFiniteAdjacent.language FlatAffineEndpointFiniteMatching.language

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    SpaceDecider (language F cone height right) := by
  have A := (FlatAffineEndpointFiniteAdjacent.decider h cone height hh right).flagEvaluator
  have M := ((FlatAffineEndpointFiniteMatching.decider h cone height hh).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (A.andFlags M).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    language F cone height right ∈ PSPACE := (decider h cone height hh right).mem_PSPACE

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (s w aWord tWord : List Bool)
    (hq : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height right) :
    pair (pair s w) (pair aWord tWord) ∈ language F cone height right ↔
      pair s w ∈ FlatAffineEndpointFiniteMatching.language F cone height := by
  simp only [language, Set.mem_ofPred_eq, hq, pairFst_pair, true_and]

end LeanCanny.Encoding.FlatAffineEndpointFiniteEdges
