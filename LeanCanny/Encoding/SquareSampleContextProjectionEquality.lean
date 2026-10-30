/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextCoordinateEquality
public import LeanCanny.Computation.BoundedScanPSPACE

/-! # Native equality of a projected complete point and another complete point

The target coordinate count is unary; each coordinate's derivative signature
is streamed with its binary degree bound. Neither coordinate arrays nor
numerical root approximations are stored.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleContextProjectionEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def language (F G : Inputs)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c)) : Language :=
  BoundedScan.language (SquareSampleContextCoordinateEquality.language F G target projection) (fun q => G.count (target (pairFst q)))

theorem decider {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    SpaceDecider (language F G target projection) := by
  have N : BinaryFn (fun q => G.count (target (pairFst q))) := (BinaryFn.ofUnary hG.count).comp (mem_FP_comp pairFst_mem_FP ht)
  exact BoundedScan.decider (SquareSampleContextCoordinateEquality.decider hF hG ht projection hi)
    (fun q => BinaryNatCode.encode (G.count (target (pairFst q)))) N.bits_mem_FP
    (fun q => G.count (target (pairFst q))) (fun _ => rfl)

theorem mem_PSPACE {F G : Inputs} (hF : F.Access) (hG : G.Access)
    {target : List Bool → List Bool} (ht : target ∈ FP)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleContextThom.coordinate F G target projection (pairFst z) (pairSnd z)).val)) :
    language F G target projection ∈ PSPACE := (decider hF hG ht projection hi).mem_PSPACE

theorem packet (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (target : List Bool → List Bool)
    (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid G (target c) v) :
    pair c (pair w v) ∈ language F G target projection ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c =
        (SquareSampleCompleteVertices.candidate G (target c) v hv).val := by
  simp only [language, BoundedScan.language, Set.mem_ofPred_eq, pairFst_pair]
  constructor
  · intro H
    funext i
    exact (SquareSampleContextCoordinateEquality.packet F G completeG target projection c w v hw hv i).mp (H i.val i.isLt)
  · intro H i hi
    apply (SquareSampleContextCoordinateEquality.packet F G completeG target projection c w v hw hv ⟨i, hi⟩).mpr
    exact congrFun H ⟨i, hi⟩

theorem valid (F G : Inputs) (target : List Bool → List Bool) (projection : (c : List Bool) → Fin (G.count (target c)) → Fin (F.count c))
    (c w v : List Bool) (h : pair c (pair w v) ∈ language F G target projection) :
    SquareSampleCompleteVertices.Valid F c w ∧ SquareSampleCompleteVertices.Valid G (target c) v := by
  have HH : ∀ i < G.count (target c), pair (pair c (pair w v)) (BinaryNatCode.encode i) ∈
      SquareSampleContextCoordinateEquality.language F G target projection := by
    simpa only [language, BoundedScan.language, Set.mem_ofPred_eq, pairFst_pair] using h
  have H := HH 0 (G.count_pos (target c))
  change SquareSampleCompleteVertices.Valid F
    (SquareSampleCompleteCoordinateEquality.source (pair (pair c (pair w v)) (BinaryNatCode.encode 0)))
    (SquareSampleCompleteCoordinateEquality.word false (pair (pair c (pair w v)) (BinaryNatCode.encode 0))) ∧ _ at H
  have P := And.intro H.1 H.2.1
  simpa only [SquareSampleCompleteCoordinateEquality.source, SquareSampleCompleteCoordinateEquality.word,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true] using P

end LeanCanny.Encoding.SquareSampleContextProjectionEquality
