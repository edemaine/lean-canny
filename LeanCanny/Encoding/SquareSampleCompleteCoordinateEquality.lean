/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteCoordinateThom
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Native equality of projected coordinates across complete root labels

Stream all derivative signs of one coordinate annihilator at each root.
Thom uniqueness makes equality exact, including at singular system roots.
Only a binary derivative counter is stored; neither signature is materialized.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def word (right : Bool) (q : List Bool) : List Bool :=
  if right then pairSnd (pairSnd (pairFst q)) else pairFst (pairSnd (pairFst q))
def vertex (right : Bool) (q : List Bool) : List Bool := pair (source q) (word right q)
def probe (right : Bool) (q : List Bool) : List Bool :=
  pair (vertex right (pairFst q)) (pair (pairSnd (pairFst q)) (pairSnd q))

theorem source_FP : source ∈ FP := by polytime [source]
theorem vertex_FP (right : Bool) : vertex right ∈ FP := by
  cases right <;> polytime [vertex, source, word]
theorem probe_FP (right : Bool) : probe right ∈ FP := by
  cases right <;> polytime [probe, vertex, source, word]

noncomputable def signaturesEqual (F : Inputs) (q : List Bool) : Prop :=
  ∀ k < F.annDegree (source q) + 1,
    SquareSampleCompleteCoordinateThom.value F (probe false (pair q (BinaryNatCode.encode k))) =
      SquareSampleCompleteCoordinateThom.value F (probe true (pair q (BinaryNatCode.encode k)))

noncomputable def language (F : Inputs) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (source q) (word false q) ∧
    SquareSampleCompleteVertices.Valid F (source q) (word true q) ∧ signaturesEqual F q}

theorem scanEvaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun q => [decide (signaturesEqual F q)]) := by
  have L := (SquareSampleCompleteCoordinateThom.evaluator h).precompose (probe false) (probe_FP false)
  have R := (SquareSampleCompleteCoordinateThom.evaluator h).precompose (probe true) (probe_FP true)
  have E := (L.pairOutputs R).postcompose
    (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D : BinaryFn (fun q => F.annDegree (source q)) := h.annDegree.comp source_FP
  have N : BinaryFn (fun q => F.annDegree (source q) + 1) := D.add (BinaryFn.const 1)
  exact (E.forall_binary N).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [signaturesEqual, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have L := ((SquareSampleCompleteVertices.decider h).precompose (vertex false) (vertex_FP false)).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider h).precompose (vertex true) (vertex_FP true)).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator h))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language,
    vertex, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

theorem packet (F : Inputs) (hF : SquareSampleComplete.Complete F) (c w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid F c v)
    (i : Fin (F.count c)) :
    pair (pair c (pair w v)) (BinaryNatCode.encode i.val) ∈ language F ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val i =
        (SquareSampleCompleteVertices.candidate F c v hv).val i := by
  simp only [language, Set.mem_ofPred_eq, source, word, Bool.false_eq_true, ite_false, ite_true,
    pairFst_pair, pairSnd_pair, hw, hv, true_and, signaturesEqual, probe, vertex]
  simp_rw [SquareSampleCompleteCoordinateThom.packet F c w hw i,
    SquareSampleCompleteCoordinateThom.packet F c v hv i, SquareSampleTestSign.encode_eq_iff]
  constructor
  · intro hs
    apply ThomEncoding.root_eq ((F.annihilator c i).map (Int.castRingHom ℝ))
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (F.ann_nonzero c i)) (F.annDegree c)
      (Polynomial.natDegree_map_le.trans (F.ann_degree c i))
    · rw [Polynomial.eval_map]
      exact hF c _ (SquareSampleCompleteVertices.candidate F c w hw).property i
    · rw [Polynomial.eval_map]
      exact hF c _ (SquareSampleCompleteVertices.candidate F c v hv).property i
    · intro k hk
      exact hs k (by omega)
  · intro he k _
    rw [he]

end LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality
