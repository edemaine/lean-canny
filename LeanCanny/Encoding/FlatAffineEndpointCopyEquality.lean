/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRankWordEquality
public import LeanCanny.Encoding.FlatAffineEndpointFiniteHeights

/-! # Native identity of a projected spatial point and its retained height

Complete joint labels may differ in all auxiliary copies. Streamed coordinate
Thom comparisons identify just the selected spatial copy and its own height.
Endpoint copies use the retained exceptional height, including singular fibers.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointCopyEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def slotWord (F : Inputs) (k : Fin 3) (s d : List Bool) : List Bool :=
  BinaryNatCode.encode (FlatAffineEndpointFiniteProjection.slot F s k (FlatAffineEndpointFiniteSide.coordinate F s d)).val

theorem slotWord_FP {F : Inputs} (h : F.Access) (k : Fin 3) : (fun z => slotWord F k (pairFst z) (pairSnd z)) ∈ FP := by
  have N := (FlatAffineEndpointFiniteSide.originalCount_unary h).comp pairFst_mem_FP
  have C := FlatAffineEndpointFiniteSide.coordinate_unary h
  have H : UnaryFn (fun z => (FlatAffineEndpointFiniteProjection.slot F (pairFst z) k
      (FlatAffineEndpointFiniteSide.coordinate F (pairFst z) (pairSnd z))).val) :=
    ((C.add (N.mul (UnaryFn.const k.val))).add (UnaryFn.const 2)).of_eq
      (fun z => (FlatAffineEndpointFiniteProjection.slot_val F (pairFst z) k _).symm)
  exact (BinaryFn.ofUnary H).bits_mem_FP

def slotContext (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd r)
theorem slotContext_FP : slotContext ∈ FP := by polytime [slotContext]
def pointQuery (F : Inputs) (k : Fin 3) (r : List Bool) : List Bool :=
  pair (pairFst r) (slotWord F k (pairFst (pairFst r)) (pairSnd r))
theorem pointQuery_FP {F : Inputs} (h : F.Access) (k : Fin 3) : pointQuery F k ∈ FP := by
  have H := mem_FP_comp slotContext_FP (slotWord_FP h k)
  exact mem_FP_pair pairFst_mem_FP (mem_FP_of_eq H (fun r => by simp only [slotContext, Function.comp_apply, pairFst_pair, pairSnd_pair]))

theorem pointQuery_packet (F : Inputs) (k : Fin 3) (s w v : List Bool) (i : Fin (FlatAffineEndpointFiniteSide.originalCount F s)) :
    pointQuery F k (pair (pair s (pair w v)) (BinaryNatCode.encode i.val)) =
      pair (pair s (pair w v)) (BinaryNatCode.encode (FlatAffineEndpointFiniteProjection.slot F s k i).val) := by
  simp only [pointQuery, pairFst_pair, pairSnd_pair]
  rw [slotWord, FlatAffineEndpointFiniteSide.coordinate_encode]

def heightIndex (F : Inputs) (k : Fin 3) (s : List Bool) : Fin (FlatAffineEndpointFiniteFrame.arity F s) :=
  if k = 0 then FlatAffineEndpointFiniteHeights.sampleIndex F s else FlatAffineEndpointFiniteHeights.endpointIndex F s

def level (F : Inputs) (k : Fin 3) (s : List Bool) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) : ℝ :=
  if k = 0 then FlatAffineEndpointFiniteProjection.sample F s z else FlatAffineEndpointFiniteProjection.endpoint F s z

theorem heightIndex_val (F : Inputs) (k : Fin 3) (s : List Bool) : (heightIndex F k s).val = if k = 0 then 0 else 1 := by
  by_cases hk : k = 0
  · simp only [heightIndex, hk, ite_true, FlatAffineEndpointFiniteHeights.sampleIndex]
  · simp only [heightIndex, hk, ite_false, FlatAffineEndpointFiniteHeights.endpointIndex]
    change 0 + FlatAffineEndpointRows.arity F (pairFst s) * 0 + 1 = 1
    omega

theorem level_eq (F : Inputs) (k : Fin 3) (s : List Bool) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) :
    z (heightIndex F k s) = level F k s z := by
  by_cases hk : k = 0
  · simp only [heightIndex, level, hk, ite_true, FlatAffineEndpointFiniteHeights.sampleIndex, FlatAffineEndpointFiniteProjection.sample]
  · simp only [heightIndex, level, hk, ite_false, FlatAffineEndpointFiniteHeights.endpointIndex, FlatAffineEndpointFiniteProjection.endpoint]

def heightQuery (k : Fin 3) (q : List Bool) : List Bool := pair q (BinaryNatCode.encode (if k = 0 then 0 else 1))
theorem heightQuery_FP (k : Fin 3) : heightQuery k ∈ FP := mem_FP_pair id_mem_FP (constFn_mem_FP _)

noncomputable def scan (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (q : List Bool) : Prop :=
  ∀ i < FlatAffineEndpointFiniteSide.originalCount F (pairFst q),
    pointQuery F k (pair q (BinaryNatCode.encode i)) ∈ SquareSampleCompleteCoordinateEquality.language
      (FlatAffineEndpointFiniteSample.input F cone height)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) : Language :=
  {q | FlatAffineEndpointRankWordEquality.left q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    FlatAffineEndpointRankWordEquality.right q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    heightQuery k q ∈ SquareSampleCompleteCoordinateEquality.language (FlatAffineEndpointFiniteSample.input F cone height) ∧ scan F cone height k q}

attribute [local irreducible] SquareSampleCompleteCoordinateEquality.language GuardedSquareSampleInput.language

theorem scanEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (k : Fin 3) :
    SpaceFunction (fun q => [decide (scan F cone height k q)]) := by
  have D := SquareSampleCompleteCoordinateEquality.decider (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)
  have E := (D.precompose (pointQuery F k) (pointQuery_FP h k)).flagEvaluator
  have N := BinaryFn.ofUnary ((FlatAffineEndpointFiniteSide.originalCount_unary h).comp pairFst_mem_FP)
  exact (E.forall_binary N).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [scan, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (k : Fin 3) : SpaceDecider (language F cone height k) := by
  have D := GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)
  have L := (D.precompose FlatAffineEndpointRankWordEquality.left FlatAffineEndpointRankWordEquality.left_FP).flagEvaluator
  have R := (D.precompose FlatAffineEndpointRankWordEquality.right FlatAffineEndpointRankWordEquality.right_FP).flagEvaluator
  have H := ((SquareSampleCompleteCoordinateEquality.decider (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)).precompose
    (heightQuery k) (heightQuery_FP k)).flagEvaluator
  apply (L.andFlags (R.andFlags (H.andFlags (scanEvaluator h cone height hh k)))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (k : Fin 3) :
    language F cone height k ∈ PSPACE := (decider h cone height hh k).mem_PSPACE

theorem scan_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v) :
    scan F cone height k (pair s (pair w v)) ↔
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val k =
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val k := by
  have H (i : Fin (FlatAffineEndpointFiniteSide.originalCount F s)) :=
    SquareSampleCompleteCoordinateEquality.packet (FlatAffineEndpointFiniteSample.input F cone height)
      (FlatAffineEndpointFiniteSample.complete F cone height) s w v hw hv (FlatAffineEndpointFiniteProjection.slot F s k i)
  constructor
  · intro hp
    funext i
    apply (H i).mp
    rw [← pointQuery_packet F k s w v i]
    exact hp i.val (by simpa only [pairFst_pair, FlatAffineEndpointFiniteSide.originalCount] using i.isLt)
  · intro hp i hi
    have hi' : i < FlatAffineEndpointFiniteSide.originalCount F s := by simpa only [pairFst_pair] using hi
    rw [pointQuery_packet F k s w v ⟨i, hi'⟩]
    exact (H ⟨i, hi'⟩).mpr (congrFun hp ⟨i, hi'⟩)

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s w v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v) :
    let z := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
    let x := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val
    pair s (pair w v) ∈ language F cone height k ↔
      level F k s z = level F k s x ∧ FlatAffineEndpointFiniteProjection.copy F s z k = FlatAffineEndpointFiniteProjection.copy F s x k := by
  have good (a : List Bool) (ha : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s a) :
      pair s a ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
    unfold GuardedSquareSampleInput.language
    change pairFst (pair s a) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst (pair s a)) (pairSnd (pair s a))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, ha⟩
  have H := SquareSampleCompleteCoordinateEquality.packet (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointFiniteSample.complete F cone height) s w v hw hv (heightIndex F k s)
  rw [heightIndex_val] at H
  simp only [level_eq] at H
  simp only [language, Set.mem_ofPred_eq, FlatAffineEndpointRankWordEquality.left, FlatAffineEndpointRankWordEquality.right,
    pairFst_pair, pairSnd_pair, good w hw, good v hv, true_and]
  rw [scan_packet F cone height k s w v hw hv]
  exact and_congr H Iff.rfl

end LeanCanny.Encoding.FlatAffineEndpointCopyEquality
