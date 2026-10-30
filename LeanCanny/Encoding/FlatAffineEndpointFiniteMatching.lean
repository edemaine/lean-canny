/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteSide
public import LeanCanny.Encoding.SquareSampleCompletePrefixEquality
public import LeanCanny.Geometry.FlatAffineEndpointFiniteProjection
public import LeanCanny.Computation.SpaceFunctionWordQuantifiers

/-! # Native matching against every endpoint candidate

A streamed scan ranges over the complete joint labels. Coordinate Thom
comparisons fix both heights, the current point, and the chosen endpoint.
The remaining endpoint copy ranges over every actual endpoint root. Side
tests therefore decide the geometric midpoint matching predicate exactly.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteMatching
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointFiniteProjection (sample endpoint copy prefixCount)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def jointQuery (r : List Bool) : List Bool :=
  pair (pairFst (pairFst r)) (pair (pairSnd (pairFst r)) (pairSnd r))
def candidateQuery (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd r)
theorem jointQuery_FP : jointQuery ∈ FP := by polytime [jointQuery]
theorem candidateQuery_FP : candidateQuery ∈ FP := by polytime [candidateQuery]

noncomputable def shares (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  SquareSampleCompletePrefixEquality.language (FlatAffineEndpointFiniteSample.input F cone height) (prefixCount F)

noncomputable def passes (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : Prop :=
  ∀ v : List Bool, v.length = SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (pairFst q) →
    pair (pairFst q) (pair (pairSnd q) v) ∈ shares F cone height →
      FlatAffineEndpointFiniteSide.passes F cone height (pair (pairFst q) v)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧ passes F cone height q}

section native
attribute [local irreducible] FlatAffineEndpointFiniteSample.input FlatAffineEndpointFiniteSample.data
  FlatAffineEndpointFiniteSide.passes SquareSampleCompletePrefixEquality.language SquareSampleCompleteVertices.width

theorem scanEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun q => [decide (passes F cone height q)]) := by
  have A := FlatAffineEndpointFiniteSample.sampleAccess h cone height hh
  have P := ((SquareSampleCompletePrefixEquality.decider A
    (BinaryFn.ofUnary (FlatAffineEndpointFiniteProjection.prefixCount_unary h))).precompose jointQuery jointQuery_FP).flagEvaluator
  have S := (FlatAffineEndpointFiniteSide.scanEvaluator h cone height hh).precompose candidateQuery candidateQuery_FP
  have hp := (Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).not.or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))
  have E := (P.pairOutputs S).postcompose _ hp.flag_mem_FP
  have H := E.forall_words ((FlatAffineEndpointFiniteSample.width_unary h cone height hh).comp pairFst_mem_FP)
  exact H.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [passes, shares, Function.comp_apply, Set.mem_preimage, jointQuery, candidateQuery, pairFst_pair, pairSnd_pair,
      List.cons.injEq, and_true, decide_eq_true_eq]
    constructor
    · intro hall v hv hs
      exact (hall v hv).resolve_left (not_not_intro hs)
    · intro hall v hv
      by_cases hs : pair (pairFst q) (pair (pairSnd q) v) ∈
          SquareSampleCompletePrefixEquality.language (FlatAffineEndpointFiniteSample.input F cone height) (prefixCount F)
      · exact Or.inr (hall v hv hs)
      · exact Or.inl hs)

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (language F cone height) := by
  have V := (GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)).flagEvaluator
  apply (V.andFlags (scanEvaluator h cone height hh)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

end native

noncomputable def endpointFiber (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (a : ℝ) :
    Set (Fin (count F (pairFst (pairFst s))) → ℝ) :=
  {y | ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) y =
    if i = height (pairFst (pairFst s)) then a else 0}

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w) :
    let z := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
    pair s w ∈ language F cone height ↔ EndpointMidpoint.Matches
      (endpointFiber F height s (endpoint F s z)) (copy F s z 1) (copy F s z 0) := by
  let I := FlatAffineEndpointFiniteSample.input F cone height
  let z := (SquareSampleCompleteVertices.candidate I s w hw).val
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs z).mp
    (SquareSampleCompleteVertices.candidate I s w hw).property
  have H := FlatAffineEndpointFiniteProjection.equations F height s z hz
  have hg : pair s w ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
    change pairFst (pair s w) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid I (pairFst (pair s w)) (pairSnd (pair s w))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, hw⟩
  change pair s w ∈ language F cone height ↔ EndpointMidpoint.Matches (endpointFiber F height s (endpoint F s z))
    (copy F s z 1) (copy F s z 0)
  simp only [language, Set.mem_ofPred_eq, hg, true_and]
  simp only [passes, pairFst_pair, pairSnd_pair]
  constructor
  · intro hp y hy
    obtain ⟨v, hv, _, he⟩ := FlatAffineEndpointFiniteSample.tuple_label_exists F cone height s hs
      (endpoint F s z) (sample F s z) (copy F s z 0) (copy F s z 1) y H.2.1 H.1
      (by intro i; simpa using H.2.2 (0 : Fin 3) i)
      (by intro i; simpa using H.2.2 (1 : Fin 3) i) hy
    have hvlen : v.length = SquareSampleCompleteVertices.width I s := (Classical.choose hv).1
    have hf : pair s (pair w v) ∈ shares F cone height := by
      apply (SquareSampleCompletePrefixEquality.packet I (FlatAffineEndpointFiniteSample.complete F cone height)
        (prefixCount F) s w v hw hv (FlatAffineEndpointFiniteProjection.prefixCount_le F s)).mpr
      intro i hi
      change z i = (SquareSampleCompleteVertices.candidate I s v hv).val i
      rw [he]
      calc
        z i = FlatAffineEndpointFiniteLift.point F s (endpoint F s z) (sample F s z)
            (copy F s z 0) (copy F s z 1) (copy F s z 2) i :=
          congrFun (FlatAffineEndpointFiniteProjection.reconstruct F s z).symm i
        _ = _ := FlatAffineEndpointFiniteProjection.prefix_point F s (endpoint F s z) (sample F s z)
          (copy F s z 0) (copy F s z 1) (copy F s z 2) y i hi
    have hpv := hp v hvlen hf
    exact (FlatAffineEndpointFiniteSide.tuple_side F cone height s v hv (endpoint F s z) (sample F s z)
      (copy F s z 0) (copy F s z 1) y he).mp hpv
  · intro hm v _ hf
    have hv : SquareSampleCompleteVertices.Valid I s v := by
      have HV := hf.2.1
      simpa only [pairFst_pair, pairSnd_pair] using HV
    let zv := (SquareSampleCompleteVertices.candidate I s v hv).val
    have hev := (SquareSampleCompletePrefixEquality.packet I (FlatAffineEndpointFiniteSample.complete F cone height)
      (prefixCount F) s w v hw hv (FlatAffineEndpointFiniteProjection.prefixCount_le F s)).mp hf
    have hc := (FlatAffineEndpointFiniteProjection.prefix_iff F s z zv).mp hev
    have hvroot := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs zv).mp
      (SquareSampleCompleteVertices.candidate I s v hv).property
    have HV := FlatAffineEndpointFiniteProjection.equations F height s zv hvroot
    have hy : copy F s zv 2 ∈ endpointFiber F height s (endpoint F s z) := by
      intro i
      rw [hc.2.1]
      simpa using HV.2.2 (2 : Fin 3) i
    have hside := hm (copy F s zv 2) hy
    rw [hc.2.2.1, hc.2.2.2] at hside
    have hpass := (FlatAffineEndpointFiniteSide.tuple_side F cone height s v hv
      (endpoint F s zv) (sample F s zv) (copy F s zv 0) (copy F s zv 1) (copy F s zv 2)
      (FlatAffineEndpointFiniteProjection.reconstruct F s zv).symm).mpr hside
    simpa only [pairFst_pair] using hpass

theorem tuple_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (a t : ℝ) (current left right : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s a t current left right) :
    pair s w ∈ language F cone height ↔ EndpointMidpoint.Matches (endpointFiber F height s a) left current := by
  have H := packet F cone height s w hs hw
  dsimp only at H
  rw [he, FlatAffineEndpointFiniteProjection.endpoint_point, FlatAffineEndpointFiniteProjection.copy_point,
    FlatAffineEndpointFiniteProjection.copy_point] at H
  exact H

end LeanCanny.Encoding.FlatAffineEndpointFiniteMatching
