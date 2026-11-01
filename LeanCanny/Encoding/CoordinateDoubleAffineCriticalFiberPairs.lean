/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointWordGeometry
public import LeanCanny.Encoding.FlatAffineChildSpatialEquality

/-! # Native equality of the heights of a critical pair

The two original member words are computed from the paired sampler. One
coordinate Thom comparison decides equality of their actual spatial heights,
including singular roots. No fiber connection test is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalFiberPairs
open LeanCanny.Algebra LeanCanny.Computation
open CoordinateDoubleAffineChildRecords (coordinate coordinateFin retainedCoordinate criticalInput)
open CoordinateDoubleAffineCriticalPairs (input memberWord memberWord_valid memberRoot)
open scoped Classical

noncomputable def members (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (memberWord P depth old level false q) (memberWord P depth old level true q))

noncomputable def query (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) : List Bool :=
  FlatAffineChildSpatialEquality.query (CoordinateDoubleAffinePrefix.inputs P depth old level)
    (pair (members P depth old level q) (BinaryNatCode.encode (coordinate P depth old (pairFst q))))

noncomputable def language (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | query P depth old level q ∈ SquareSampleCompleteCoordinateEquality.language (criticalInput P depth old level)}

theorem query_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (query P depth old level) := by
  have M := (SpaceFunction.ofFP pairFst pairFst_mem_FP).pairOutputs
    ((CoordinateDoubleAffineCriticalPairs.memberWord_evaluator hP hd ho hl hA false).pairOutputs
      (CoordinateDoubleAffineCriticalPairs.memberWord_evaluator hP hd ho hl hA true))
  have I := SpaceFunction.ofFP _
    ((BinaryFn.ofUnary ((CoordinateDoubleAffineChildRecords.coordinate_unary hP hd ho).comp pairFst_mem_FP)).bits_mem_FP)
  exact ((M.pairOutputs I).postcompose _
    (FlatAffineChildSpatialEquality.query_FP (CoordinateDoubleAffinePrefix.access hP hd ho hl hA))).congr
      (funext fun _ => rfl)

theorem decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (language P depth old level) := by
  have E := (query_evaluator hP hd ho hl hA).chain
    (SquareSampleCompleteCoordinateEquality.decider
      (CoordinateDoubleAffineCriticalPairs.critical_access hP hd ho hl hA)).flagEvaluator
  apply E.decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Function.comp_apply,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem packet (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    pair u w ∈ language P depth old level ↔
      retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩
        (memberRoot P depth old level false u w hw).val =
      retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩
        (memberRoot P depth old level true u w hw).val := by
  let F := CoordinateDoubleAffinePrefix.inputs P depth old level
  let cone := CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level
  have HL := FlatAffineChildSpatialEquality.point_coordinate F cone u
    (memberWord P depth old level false (pair u w)) (memberWord_valid P depth old level false u w hw)
      (coordinateFin P depth old u)
  have HR := FlatAffineChildSpatialEquality.point_coordinate F cone u
    (memberWord P depth old level true (pair u w)) (memberWord_valid P depth old level true u w hw)
      (coordinateFin P depth old u)
  have HE := SquareSampleCompleteCoordinateEquality.packet (criticalInput P depth old level)
    (CoordinateDoubleAffineCriticalPairs.critical_complete P depth old level) u
    (memberWord P depth old level false (pair u w)) (memberWord P depth old level true (pair u w))
    (memberWord_valid P depth old level false u w hw) (memberWord_valid P depth old level true u w hw)
    (FlatAffineChildSpatialEquality.slot F u (coordinateFin P depth old u))
  change (query P depth old level (pair u w) ∈
    SquareSampleCompleteCoordinateEquality.language (criticalInput P depth old level)) ↔ _
  have HQ : query P depth old level (pair u w) =
      pair (pair u (pair (memberWord P depth old level false (pair u w))
        (memberWord P depth old level true (pair u w))))
          (BinaryNatCode.encode (FlatAffineChildSpatialEquality.slot F u (coordinateFin P depth old u)).val) := by
    simp only [query, members, pairFst_pair]
    exact FlatAffineChildSpatialEquality.query_packet F u _ _ (coordinateFin P depth old u)
  dsimp only [F] at HL HR HE HQ
  rw [HQ, HE]
  constructor
  · intro h
    exact HL.trans (h.trans HR.symm)
  · intro h
    exact HL.symm.trans (h.trans HR)

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalFiberPairs
