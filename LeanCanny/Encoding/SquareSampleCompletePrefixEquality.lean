/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality

/-! # Native agreement on an initial coordinate block

The two complete labels retain the same original source. Repeated coordinate
Thom scans identify exactly a specified prefix without storing its values.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompletePrefixEquality
open LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def vertex (right : Bool) (q : List Bool) : List Bool :=
  pair (pairFst q) (if right then pairSnd (pairSnd q) else pairFst (pairSnd q))

theorem vertex_FP (right : Bool) : vertex right ∈ FP := by
  cases right <;> polytime [vertex]

noncomputable def agrees (F : Inputs) (m : List Bool → ℕ) (q : List Bool) : Prop :=
  ∀ k < m (pairFst q), pair q (BinaryNatCode.encode k) ∈ SquareSampleCompleteCoordinateEquality.language F

noncomputable def language (F : Inputs) (m : List Bool → ℕ) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (pairFst q) (pairFst (pairSnd q)) ∧
    SquareSampleCompleteVertices.Valid F (pairFst q) (pairSnd (pairSnd q)) ∧ agrees F m q}

theorem scanEvaluator {F : Inputs} (h : F.Access) {m : List Bool → ℕ} (hm : BinaryFn m) :
    SpaceFunction (fun q => [decide (agrees F m q)]) := by
  have E := (SquareSampleCompleteCoordinateEquality.decider h).flagEvaluator.forall_binary (hm.comp pairFst_mem_FP)
  exact E.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F : Inputs} (h : F.Access) {m : List Bool → ℕ} (hm : BinaryFn m) :
    SpaceDecider (language F m) := by
  have L := ((SquareSampleCompleteVertices.decider h).precompose (vertex false) (vertex_FP false)).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider h).precompose (vertex true) (vertex_FP true)).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator h hm))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language,
    vertex, Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) {m : List Bool → ℕ} (hm : BinaryFn m) :
    language F m ∈ PSPACE := (decider h hm).mem_PSPACE

theorem packet (F : Inputs) (hF : SquareSampleComplete.Complete F) (m : List Bool → ℕ)
    (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid F c v)
    (hm : m c ≤ F.count c) :
    pair c (pair w v) ∈ language F m ↔
      ∀ i : Fin (F.count c), i.val < m c →
        (SquareSampleCompleteVertices.candidate F c w hw).val i = (SquareSampleCompleteVertices.candidate F c v hv).val i := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hw, hv, true_and, agrees]
  constructor
  · intro hp i hi
    exact (SquareSampleCompleteCoordinateEquality.packet F hF c w v hw hv i).mp
      (hp i.val (by simpa only [pairFst_pair] using hi))
  · intro hp k hk
    have hk' : k < m c := by simpa only [pairFst_pair] using hk
    let i : Fin (F.count c) := ⟨k, hk'.trans_le hm⟩
    exact (SquareSampleCompleteCoordinateEquality.packet F hF c w v hw hv i).mpr (hp i hk')

end LeanCanny.Encoding.SquareSampleCompletePrefixEquality
