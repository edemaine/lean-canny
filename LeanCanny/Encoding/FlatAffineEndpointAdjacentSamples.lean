/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointSamples
public import LeanCanny.Encoding.IntegerPolynomialAdjacentSamples

/-! # Native adjacent-gap sample validation for actual affine endpoints

The original source computes the endpoint-height polynomial, the refined
matching polynomial, and its derivative sample candidates. A native language
checks the prepared degree record, both complete scalar labels, and exact
adjacency on either side. Repeated endpoint heights and sample roots remain
included; no separating rational coordinates are input.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointAdjacentSamples
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open IntegerPolynomialAdjacentSamples (endpointRecord sampleRecord)
open Geometry.OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def heightSource (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : IntegerPolynomialRootQueriesBits.Source where
  polynomial r := FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)
  degree r := FlatAffineHeightSlabExceptional.degreeBound F (pairFst r)
  mass r := FlatAffineHeightSlabExceptional.massBound F (pairFst r)
  degree_bound r := FlatAffineHeightSlabExceptional.degree_bound F hcone height (pairFst r)
  mass_bound r := FlatAffineHeightSlabExceptional.mass_bound F height (pairFst r)

theorem heightAccess {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.Access (heightSource F hcone height) :=
  ⟨FlatAffineEndpointPreparation.coefficientEvaluator h height hh,
    (FlatAffineHeightSlabExceptional.degreeBound_binary h height).comp pairFst_mem_FP,
    (FlatAffineHeightSlabExceptional.massBound_binary h height).comp pairFst_mem_FP⟩

noncomputable def language (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) : Language :=
  {q | FlatAffineEndpointValidity.Valid F height (pairFst (pairFst q)) ∧ q ∈
    IntegerPolynomialAdjacentSamples.language (heightSource F hcone height)
      (FlatAffineEndpointSamples.source F hcone height) (FlatAffineEndpointCells.source F hcone height) right}

theorem decider {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    SpaceDecider (language F hcone height right) := by
  have R := ((FlatAffineEndpointValidity.decider h hcone height hh).precompose (pairFst ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).flagEvaluator
  have E := (IntegerPolynomialAdjacentSamples.decider (heightAccess h hcone height hh)
    (FlatAffineEndpointSamples.access h hcone height hh) (FlatAffineEndpointCells.access h hcone height hh) right).flagEvaluator
  apply (R.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    language F hcone height right ∈ PSPACE := (decider h hcone height hh right).mem_PSPACE

theorem gap_packet (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (q : List Bool)
    (hr : FlatAffineEndpointValidity.Valid F height (pairFst (pairFst q)))
    (ha : endpointRecord q ∈ IntegerPolynomialSampleSlice.valid (heightSource F hcone height))
    (ht : sampleRecord q ∈ IntegerPolynomialSampleSlice.valid (FlatAffineEndpointSamples.source F hcone height))
    (i : Fin (FlatAffineEndpointCells.roots F hcone height (pairFst (pairFst q))).card)
    (hi : root (FlatAffineEndpointCells.roots F hcone height (pairFst (pairFst q))) i =
      IntegerPolynomialSampleSlice.point (heightSource F hcone height) (endpointRecord q)) :
    q ∈ language F hcone height right ↔
      IntegerPolynomialSampleSlice.point (FlatAffineEndpointSamples.source F hcone height) (sampleRecord q) ∈
        gap (FlatAffineEndpointCells.roots F hcone height (pairFst (pairFst q)))
          (if right then rightGap _ i else leftGap _ i) := by
  simp only [language, Set.mem_ofPred_eq, hr, true_and]
  exact IntegerPolynomialAdjacentSamples.gap_packet _ _ _ right q ha ht i hi

end LeanCanny.Encoding.FlatAffineEndpointAdjacentSamples
