/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteProjectionRank
public import LeanCanny.Encoding.FlatAffineEndpointFiniteMatching

/-! # Native ranks of actual current coordinates at fixed joint heights

A context contains a frame and an anchor label. Native prefix comparisons
fix its two retained heights while allowing every spatial copy to vary.
Distinct projection ranks then count actual current-coordinate values.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def frame (c : List Bool) : List Bool := pairFst c
def anchor (c : List Bool) : List Bool := pairFst (pairSnd c)
theorem frame_FP : frame ∈ FP := pairFst_mem_FP

def query (q : List Bool) : List Bool := pair (frame (pairFst q)) (pair (anchor (pairFst q)) (pairSnd q))
theorem query_FP : query ∈ FP := by polytime [query, frame, anchor]

noncomputable def allowed (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | FlatAffineEndpointFiniteFrame.Valid F height (frame (pairFst q)) ∧
    query q ∈ SquareSampleCompletePrefixEquality.language (FlatAffineEndpointFiniteSample.input F cone height) (fun _ => 2)}

theorem allowed_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w : List Bool) :
    pair c w ∈ allowed F cone height ↔ FlatAffineEndpointFiniteFrame.Valid F height (frame c) ∧
      pair (frame c) (pair (anchor c) w) ∈ SquareSampleCompletePrefixEquality.language
        (FlatAffineEndpointFiniteSample.input F cone height) (fun _ => 2) := by
  simp only [allowed, Set.mem_ofPred_eq, query, pairFst_pair, pairSnd_pair]

theorem allowed_good (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w : List Bool) (hw : pair c w ∈ allowed F cone height) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (frame c) w := by
  have H := ((allowed_packet F cone height c w).mp hw).2.2.1
  simpa only [pairFst_pair, pairSnd_pair] using H

theorem allowedDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (allowed F cone height) := by
  have V := ((FlatAffineEndpointFiniteFrame.validDecider h cone height hh).precompose (frame ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP frame_FP)).flagEvaluator
  have P := ((SquareSampleCompletePrefixEquality.decider (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)
    (BinaryFn.const 2)).precompose query query_FP).flagEvaluator
  apply (V.andFlags P).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [allowed, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq]

def coordinate (F : Inputs)
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (c : List Bool) :
    Fin (FlatAffineEndpointFiniteFrame.arity F (frame c)) := FlatAffineEndpointFiniteProjection.slot F (frame c) 0 (index c)

theorem coordinate_unary (F : Inputs)
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (hi : UnaryFn (fun c => (index c).val)) :
    UnaryFn (fun c => (coordinate F index c).val) :=
  (hi.add (UnaryFn.const 2)).of_eq (fun c => by
    rw [coordinate, FlatAffineEndpointFiniteProjection.slot_val]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero])

noncomputable def data (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) : FiniteWordProjectionRank.Data :=
  SquareSampleCompleteProjectionRank.data (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointFiniteSample.complete F cone height) frame (coordinate F index) (allowed F cone height)
    (allowed_good F cone height)

theorem access {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (hi : UnaryFn (fun c => (index c).val)) :
    (data F cone height index).Access :=
  SquareSampleCompleteProjectionRank.access (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)
    (FlatAffineEndpointFiniteSample.complete F cone height) frame_FP (coordinate F index) (coordinate_unary F index hi)
    (allowedDecider h cone height hh) (allowed_good F cone height)

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (hi : UnaryFn (fun c => (index c).val)) :
    SpaceFunction (fun q => BinaryNatCode.encode (FiniteWordProjectionRank.rank (data F cone height index) q)) :=
  FiniteWordProjectionRank.evaluator (access h cone height hh index hi)

theorem height_prefix_iff (F : Inputs) (s : List Bool) (z v : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) :
    (∀ i, i.val < 2 → z i = v i) ↔
      FlatAffineEndpointFiniteProjection.sample F s z = FlatAffineEndpointFiniteProjection.sample F s v ∧
        FlatAffineEndpointFiniteProjection.endpoint F s z = FlatAffineEndpointFiniteProjection.endpoint F s v := by
  constructor
  · intro hp
    exact ⟨hp _ (by change 0 < 2; decide), hp _ (by change 1 < 2; decide)⟩
  · rintro ⟨ht, ha⟩ j hj
    by_cases h0 : j.val = 0
    · have he : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext h0
      subst j
      exact ht
    · have h1 : j.val = 1 := by omega
      have he : j = FrozenAffineCopies.block (0 : Fin 1) (FlatAffineEndpointRows.zero F (pairFst s)) := Fin.ext h1
      subst j
      exact ha

theorem allowed_heights (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w : List Bool)
    (ha : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c))
    (hw : pair c w ∈ allowed F cone height) :
    let z := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c) ha).val
    let v := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) w (allowed_good F cone height c w hw)).val
    FlatAffineEndpointFiniteProjection.sample F (frame c) z = FlatAffineEndpointFiniteProjection.sample F (frame c) v ∧
      FlatAffineEndpointFiniteProjection.endpoint F (frame c) z = FlatAffineEndpointFiniteProjection.endpoint F (frame c) v := by
  have hp := ((allowed_packet F cone height c w).mp hw).2
  apply (height_prefix_iff F (frame c) _ _).mp
  exact (SquareSampleCompletePrefixEquality.packet (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointFiniteSample.complete F cone height) (fun _ => 2) (frame c) (anchor c) w ha
    (allowed_good F cone height c w hw) (by
      change 2 ≤ FlatAffineEndpointFiniteFrame.arity F (frame c)
      dsimp only [FlatAffineEndpointFiniteFrame.arity, FlatAffineEndpointRows.arity]
      omega)).mp hp

end LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
