/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextThom
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality

/-! # Native coordinate equality across different sampling contexts

Target-annihilator Thom signs are streamed at the projected source point and
the target point. Order zero also proves that the projected coordinate is a
target-annihilator root. No projection-preservation premise is needed for the
equality test itself.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleContextCoordinateEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteCoordinateEquality (source word source_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def vertex (target : List Bool → List Bool) (right : Bool) (q : List Bool) : List Bool :=
  pair (if right then target (source q) else source q) (word right q)
def probe (target : List Bool → List Bool) (right : Bool) (r : List Bool) : List Bool :=
  pair (vertex target right (pairFst r))
    (if right then pair (pairSnd (pairFst r)) (pairSnd r)
      else pair (source (pairFst r)) (pair (pairSnd (pairFst r)) (pairSnd r)))
theorem vertex_FP {target : List Bool → List Bool} (ht : target ∈ FP) (right : Bool) : vertex target right ∈ FP := by
  cases right <;> polytime [vertex, source, word]
theorem probe_FP {target : List Bool → List Bool} (ht : target ∈ FP) (right : Bool) : probe target right ∈ FP := by
  cases right <;> polytime [probe, vertex, source, word]

noncomputable def signaturesEqual (F G : Inputs)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) (q : List Bool) : Prop :=
  ∀ k < G.annDegree (target (source q)) + 1,
    SquareSampleContextThom.value F G target projection (probe target false (pair q (BinaryNatCode.encode k))) =
      SquareSampleCompleteCoordinateThom.value G (probe target true (pair q (BinaryNatCode.encode k)))

noncomputable def language (F G : Inputs)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (source q) (word false q) ∧
    SquareSampleCompleteVertices.Valid G (target (source q)) (word true q) ∧ signaturesEqual F G target projection q}

theorem scanEvaluator {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    SpaceFunction (fun q => [decide (signaturesEqual F G target projection q)]) := by
  have L := (SquareSampleContextThom.evaluator hF hG ht projection hi).precompose (probe target false) (probe_FP ht false)
  have R := (SquareSampleCompleteCoordinateThom.evaluator hG).precompose (probe target true) (probe_FP ht true)
  have E := (L.pairOutputs R).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have DG : BinaryFn (fun q => G.annDegree (target (source q))) := hG.annDegree.comp (mem_FP_comp source_FP ht)
  have D := DG.add (BinaryFn.const 1)
  exact (E.forall_binary D).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [signaturesEqual, Function.comp_apply, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    SpaceDecider (language F G target projection) := by
  have L := ((SquareSampleCompleteVertices.decider hF).precompose (vertex target false) (vertex_FP ht false)).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider hG).precompose (vertex target true) (vertex_FP ht true)).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator hF hG ht projection hi))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language,
    vertex, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq,
    Bool.false_eq_true, ite_false, ite_true]

theorem mem_PSPACE {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    language F G target projection ∈ PSPACE := (decider hF hG ht projection hi).mem_PSPACE

theorem packet (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid G (target c) v)
    (i : Fin (G.count (target c))) :
    pair (pair c (pair w v)) (BinaryNatCode.encode i.val) ∈ language F G target projection ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val (projection c i) =
        (SquareSampleCompleteVertices.candidate G (target c) v hv).val i := by
  simp only [language, Set.mem_ofPred_eq, source, word, Bool.false_eq_true, ite_false, ite_true,
    pairFst_pair, pairSnd_pair, hw, hv, true_and, signaturesEqual, probe, vertex]
  simp_rw [SquareSampleContextThom.packet F G target projection c w hw i,
    SquareSampleCompleteCoordinateThom.packet G (target c) v hv i, SquareSampleTestSign.encode_eq_iff]
  let p := (G.annihilator (target c) i).map (Int.castRingHom ℝ)
  let a := (SquareSampleCompleteVertices.candidate F c w hw).val (projection c i)
  let b := (SquareSampleCompleteVertices.candidate G (target c) v hv).val i
  have HB : p.eval b = 0 := by
    rw [Polynomial.eval_map]
    exact completeG (target c) _ (SquareSampleCompleteVertices.candidate G (target c) v hv).property i
  constructor
  · intro hs
    have H0 : SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
      simpa only [ThomEncoding.sign, Function.iterate_zero_apply] using hs 0 (by omega)
    rw [HB, sign_zero] at H0
    have HA : p.eval a = 0 := sign_eq_zero_iff.mp H0
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (G.ann_nonzero (target c) i))
      (G.annDegree (target c)) (Polynomial.natDegree_map_le.trans (G.ann_degree (target c) i)) a b HA HB (fun k hk => hs k (by omega))
  · intro he k _
    rw [he]

end LeanCanny.Encoding.SquareSampleContextCoordinateEquality
