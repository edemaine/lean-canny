/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProjectedThom
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality

/-! # Native equality of coordinates across two complete samplers

Target-annihilator Thom signs are streamed at the projected source point and
the target point. Order zero also proves that the projected coordinate is a
target-annihilator root. No projection-preservation premise is needed for the
equality test itself.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProjectedCoordinateEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteCoordinateEquality (source word vertex probe source_FP vertex_FP probe_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def signaturesEqual (F G : Inputs)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) (q : List Bool) : Prop :=
  ∀ k < G.annDegree (source q) + 1,
    SquareSampleProjectedThom.value F G projection (probe false (pair q (BinaryNatCode.encode k))) =
      SquareSampleCompleteCoordinateThom.value G (probe true (pair q (BinaryNatCode.encode k)))

noncomputable def language (F G : Inputs)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (source q) (word false q) ∧
    SquareSampleCompleteVertices.Valid G (source q) (word true q) ∧ signaturesEqual F G projection q}

theorem scanEvaluator {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    SpaceFunction (fun q => [decide (signaturesEqual F G projection q)]) := by
  have L := (SquareSampleProjectedThom.evaluator hF hG projection hi).precompose (probe false) (probe_FP false)
  have R := (SquareSampleCompleteCoordinateThom.evaluator hG).precompose (probe true) (probe_FP true)
  have E := (L.pairOutputs R).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have DG : BinaryFn (fun q => G.annDegree (source q)) := hG.annDegree.comp source_FP
  have D := DG.add (BinaryFn.const 1)
  exact (E.forall_binary D).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [signaturesEqual, Function.comp_apply, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    SpaceDecider (language F G projection) := by
  have L := ((SquareSampleCompleteVertices.decider hF).precompose (vertex false) (vertex_FP false)).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider hG).precompose (vertex true) (vertex_FP true)).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator hF hG projection hi))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language,
    vertex, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    language F G projection ∈ PSPACE := (decider hF hG projection hi).mem_PSPACE

theorem packet (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid G c v)
    (i : Fin (G.count c)) :
    pair (pair c (pair w v)) (BinaryNatCode.encode i.val) ∈ language F G projection ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val (projection c i) =
        (SquareSampleCompleteVertices.candidate G c v hv).val i := by
  simp only [language, Set.mem_ofPred_eq, source, word, Bool.false_eq_true, ite_false, ite_true,
    pairFst_pair, pairSnd_pair, hw, hv, true_and, signaturesEqual, probe, vertex]
  simp_rw [SquareSampleProjectedThom.packet F G projection c w hw i,
    SquareSampleCompleteCoordinateThom.packet G c v hv i, SquareSampleTestSign.encode_eq_iff]
  let p := (G.annihilator c i).map (Int.castRingHom ℝ)
  let a := (SquareSampleCompleteVertices.candidate F c w hw).val (projection c i)
  let b := (SquareSampleCompleteVertices.candidate G c v hv).val i
  have HB : p.eval b = 0 := by
    rw [Polynomial.eval_map]
    exact completeG c _ (SquareSampleCompleteVertices.candidate G c v hv).property i
  constructor
  · intro hs
    have H0 : SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
      simpa only [ThomEncoding.sign, Function.iterate_zero_apply] using hs 0 (by omega)
    rw [HB, sign_zero] at H0
    have HA : p.eval a = 0 := sign_eq_zero_iff.mp H0
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (G.ann_nonzero c i))
      (G.annDegree c) (Polynomial.natDegree_map_le.trans (G.ann_degree c i)) a b HA HB (fun k hk => hs k (by omega))
  · intro he k _
    rw [he]

end LeanCanny.Encoding.SquareSampleProjectedCoordinateEquality
