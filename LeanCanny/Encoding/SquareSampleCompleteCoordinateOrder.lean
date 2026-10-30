/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality
public import LeanCanny.Algebra.ThomOrderSpace

/-! # Native ordering of projected coordinates of complete root labels

The highest differing derivative sign gives the real order. A streamed scan
uses one comparison bit, retaining singular roots and tied coordinates.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteCoordinateOrder
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteCoordinateEquality (source word probe vertex)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
attribute [local irreducible] SquareSampleCompleteCoordinateThom.value

noncomputable def read (F : Inputs) (q : List Bool) : List Bool := pair
  (SquareSampleCompleteCoordinateThom.value F (probe false q))
  (SquareSampleCompleteCoordinateThom.value F (probe true q))

theorem readEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (read F) :=
  ((SquareSampleCompleteCoordinateThom.evaluator h).precompose (probe false) (SquareSampleCompleteCoordinateEquality.probe_FP false)).pairOutputs
    ((SquareSampleCompleteCoordinateThom.evaluator h).precompose (probe true) (SquareSampleCompleteCoordinateEquality.probe_FP true))

def bound (F : Inputs) (q : List Bool) : List Bool := BinaryNatCode.encode (F.annDegree (source q) + 1)
theorem bound_FP {F : Inputs} (h : F.Access) : bound F ∈ FP := by
  have D : BinaryFn (fun q => F.annDegree (source q)) := h.annDegree.comp SquareSampleCompleteCoordinateEquality.source_FP
  exact (D.add (BinaryFn.const 1)).bits_mem_FP

noncomputable def value (F : Inputs) : List Bool → List Bool := ThomOrderBits.value (read F) (bound F)
theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) :=
  ThomOrderBits.evaluator (readEvaluator h) (bound_FP h)

theorem packet (F : Inputs) (hF : SquareSampleComplete.Complete F) (c w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid F c v)
    (i : Fin (F.count c)) : value F (pair (pair c (pair w v)) (BinaryNatCode.encode i.val)) =
      [decide ((SquareSampleCompleteVertices.candidate F c w hw).val i < (SquareSampleCompleteVertices.candidate F c v hv).val i)] := by
  let p := (F.annihilator c i).map (Int.castRingHom ℝ)
  let x := (SquareSampleCompleteVertices.candidate F c w hw).val i
  let y := (SquareSampleCompleteVertices.candidate F c v hv).val i
  have hx : p.IsRoot x := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hF c _ (SquareSampleCompleteVertices.candidate F c w hw).property i
  have hy : p.IsRoot y := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hF c _ (SquareSampleCompleteVertices.candidate F c v hv).property i
  have hr (k : ℕ) : read F (pair (pair (pair c (pair w v)) (BinaryNatCode.encode i.val)) (BinaryNatCode.encode k)) =
      pair (InfinitesimalSign.encode (ThomEncoding.sign p x k)) (InfinitesimalSign.encode (ThomEncoding.sign p y k)) := by
    simp only [read, probe, vertex, source, word, Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair]
    rw [SquareSampleCompleteCoordinateThom.packet F c w hw i k, SquareSampleCompleteCoordinateThom.packet F c v hv i k]
  have hb : Nat.fromBitsLE (bound F (pair (pair c (pair w v)) (BinaryNatCode.encode i.val))) = F.annDegree c + 1 := by
    simp only [bound, source, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, ThomOrderBits.value, hb]
  rw [ThomOrderBits.fold_packet (read F) _ (ThomEncoding.sign p x) (ThomEncoding.sign p y) hr]
  rw [ThomEncoding.orderScan_roots p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (F.ann_nonzero c i))
    (F.annDegree c) (Polynomial.natDegree_map_le.trans (F.ann_degree c i)) x y hx hy]

noncomputable def language (F : Inputs) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (source q) (word false q) ∧
    SquareSampleCompleteVertices.Valid F (source q) (word true q) ∧ value F q = [true]}

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have L := ((SquareSampleCompleteVertices.decider h).precompose (vertex false) (SquareSampleCompleteCoordinateEquality.vertex_FP false)).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider h).precompose (vertex true) (SquareSampleCompleteCoordinateEquality.vertex_FP true)).flagEvaluator
  apply (L.andFlags (R.andFlags (evaluator h))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language,
    vertex, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

end LeanCanny.Encoding.SquareSampleCompleteCoordinateOrder
