/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProjectedCoordinateEquality
public import LeanCanny.Computation.BoundedScanPSPACE

/-! # Native equality of a projected complete point and another complete point

The target coordinate count is unary; each coordinate's derivative signature
is streamed with its binary degree bound. Neither coordinate arrays nor
numerical root approximations are stored.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProjectionEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def language (F G : Inputs)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c)) : Language :=
  BoundedScan.language (SquareSampleProjectedCoordinateEquality.language F G projection) (fun q => G.count (pairFst q))

theorem decider {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    SpaceDecider (language F G projection) := by
  have N : BinaryFn (fun q => G.count (pairFst q)) := (BinaryFn.ofUnary hG.count).comp pairFst_mem_FP
  exact BoundedScan.decider (SquareSampleProjectedCoordinateEquality.decider hF hG projection hi)
    (fun q => BinaryNatCode.encode (G.count (pairFst q))) N.bits_mem_FP
    (fun q => G.count (pairFst q)) (fun _ => rfl)

theorem mem_PSPACE {F G : Inputs} (hF : F.Access) (hG : G.Access)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (hi : UnaryFn (fun z => (SquareSampleProjectedThom.coordinate F G projection (pairFst z) (pairSnd z)).val)) :
    language F G projection ∈ PSPACE := (decider hF hG projection hi).mem_PSPACE

theorem packet (F G : Inputs) (completeG : SquareSampleComplete.Complete G)
    (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) (hv : SquareSampleCompleteVertices.Valid G c v) :
    pair c (pair w v) ∈ language F G projection ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val ∘ projection c =
        (SquareSampleCompleteVertices.candidate G c v hv).val := by
  simp only [language, BoundedScan.language, Set.mem_ofPred_eq, pairFst_pair]
  constructor
  · intro H
    funext i
    exact (SquareSampleProjectedCoordinateEquality.packet F G completeG projection c w v hw hv i).mp (H i.val i.isLt)
  · intro H i hi
    apply (SquareSampleProjectedCoordinateEquality.packet F G completeG projection c w v hw hv ⟨i, hi⟩).mpr
    exact congrFun H ⟨i, hi⟩

theorem valid (F G : Inputs) (projection : (c : List Bool) → Fin (G.count c) → Fin (F.count c))
    (c w v : List Bool) (h : pair c (pair w v) ∈ language F G projection) :
    SquareSampleCompleteVertices.Valid F c w ∧ SquareSampleCompleteVertices.Valid G c v := by
  have HH : ∀ i < G.count c, pair (pair c (pair w v)) (BinaryNatCode.encode i) ∈
      SquareSampleProjectedCoordinateEquality.language F G projection := by
    simpa only [language, BoundedScan.language, Set.mem_ofPred_eq, pairFst_pair] using h
  have H := HH 0 (G.count_pos c)
  change SquareSampleCompleteVertices.Valid F
    (SquareSampleCompleteCoordinateEquality.source (pair (pair c (pair w v)) (BinaryNatCode.encode 0)))
    (SquareSampleCompleteCoordinateEquality.word false (pair (pair c (pair w v)) (BinaryNatCode.encode 0))) ∧ _ at H
  have P := And.intro H.1 H.2.1
  simpa only [SquareSampleCompleteCoordinateEquality.source, SquareSampleCompleteCoordinateEquality.word,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true] using P

end LeanCanny.Encoding.SquareSampleProjectionEquality
