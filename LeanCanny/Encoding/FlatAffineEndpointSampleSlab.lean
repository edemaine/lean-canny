/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteHeights
public import LeanCanny.Geometry.OrderedRealCellRank

/-! # Native original-slab codes for jointly labeled algebraic samples

The scalar derivative-root label is bound to the joint sample height. Two
native cuts of the original exceptional polynomial check nonmembership and
the exact lower-root count. The binary code therefore denotes its actual
original gap, including either exterior gap.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointSampleSlab
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def sampleWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def gapWord (q : List Bool) : List Bool := pairSnd (pairSnd q)
def identityQuery (q : List Bool) : List Bool := pair (pairFst q) (sampleWord q)
def record (q : List Bool) : List Bool := pair (pair (pairFst (pairFst (pairFst q))) (sampleWord q)) []
theorem gapWord_FP : gapWord ∈ FP := by polytime [gapWord]
theorem identityQuery_FP : identityQuery ∈ FP := by polytime [identityQuery, sampleWord]
theorem record_FP : record ∈ FP := by polytime [record, sampleWord]

noncomputable def roots (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) : Finset ℝ :=
  IntegerPolynomialRootQueriesBits.rootSet (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (pairFst s)

noncomputable def numeric (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : Prop :=
  IntegerPolynomialAlgebraicCut.count (FlatAffineEndpointSamples.source F cone height)
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (record q) = Nat.fromBitsLE (gapWord q) ∧
    IntegerPolynomialAlgebraicCut.zeroCount (FlatAffineEndpointSamples.source F cone height)
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (record q) = 0

def compare (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairFst (pairSnd z)) = Nat.fromBitsLE (gapWord (pairFst z)) ∧ Nat.fromBitsLE (pairSnd (pairSnd z)) = 0)
theorem compare_FP : (fun z => [compare z]) ∈ FP :=
  (((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).eq
    (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP gapWord_FP))).and
    ((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)).eq (BinaryFn.const 0))).flag_mem_FP

attribute [local irreducible] IntegerPolynomialAlgebraicCut.count IntegerPolynomialAlgebraicCut.zeroCount
  FlatAffineEndpointFiniteHeights.sampleLanguage GuardedSquareSampleInput.language

theorem numericDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider {q | numeric F cone height q} := by
  have A := FlatAffineEndpointSamples.access h cone height hh
  have B := FlatAffineEndpointAdjacentSamples.heightAccess h cone height hh
  have C := (IntegerPolynomialAlgebraicCut.evaluator A B).precompose record record_FP
  have Z := (IntegerPolynomialAlgebraicCut.zeroEvaluator A B).precompose record record_FP
  apply (C.pairOutputs Z).withInput.decider compare compare_FP
  intro q
  simp only [numeric, Set.mem_ofPred_eq, compare, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | pairFst q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    identityQuery q ∈ FlatAffineEndpointFiniteHeights.sampleLanguage F cone height ∧ numeric F cone height q}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have V := ((GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)).precompose pairFst pairFst_mem_FP).flagEvaluator
  have I := ((FlatAffineEndpointFiniteHeights.sampleDecider h cone height hh).precompose identityQuery identityQuery_FP).flagEvaluator
  apply (V.andFlags (I.andFlags (numericDecider h cone height hh).flagEvaluator)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

theorem joint_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height)
      (pairFst (pairFst q)) (pairSnd (pairFst q)) := by
  have H := hq.1
  unfold GuardedSquareSampleInput.language at H
  exact H.2

theorem sample_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height)
      (pairFst (pairFst (pairFst q))) (sampleWord q) := by
  have H := hq.2.1
  unfold FlatAffineEndpointFiniteHeights.sampleLanguage SquareSampleScalarCoordinateEquality.language at H
  have HV := H.2.1
  simpa only [FlatAffineEndpointSamples.input, SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, SquareSampleScalarCoordinateEquality.scalarVertex,
    SquareSampleScalarCoordinateEquality.source, identityQuery, pairFst_pair, pairSnd_pair] using HV

theorem numeric_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w tWord : List Bool)
    (ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (k : Fin ((roots F cone height s).card + 1)) :
    numeric F cone height (pair (pair s w) (pair tWord (BinaryNatCode.encode k.val))) ↔
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord ht).val (0 : Fin 1) ∉
          roots F cone height s ∧
        OrderedRealCells.lowerCount (roots F cone height s)
          ((SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord ht).val (0 : Fin 1)) = k.val := by
  let S := FlatAffineEndpointSamples.source F cone height
  let Q := FlatAffineEndpointAdjacentSamples.heightSource F cone height
  let u := pair (pair (pairFst s) tWord) []
  have hu : u ∈ IntegerPolynomialSampleSlice.valid S := (IntegerPolynomialSampleSlice.valid_packet S _ _ []).mpr ht
  have HC := IntegerPolynomialAlgebraicCut.count_below S Q u hu
  have HZ := IntegerPolynomialAlgebraicCut.zeroCount_eq_zero_iff S Q u hu
  have HP := IntegerPolynomialSampleSlice.point_packet S (pairFst s) tWord [] ht
  simp only [u, pairFst_pair] at HC HZ
  simp only [numeric, record, sampleWord, gapWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [HC, HZ, HP]
  exact and_comm

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w tWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (k : Fin ((roots F cone height s).card + 1)) :
    pair (pair s w) (pair tWord (BinaryNatCode.encode k.val)) ∈ language F cone height ↔
      FlatAffineEndpointFiniteProjection.sample F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord ht).val (0 : Fin 1) ∧
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord ht).val (0 : Fin 1) ∈
        OrderedRealCells.gap (roots F cone height s) k := by
  have hg : pair s w ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
    unfold GuardedSquareSampleInput.language
    change pairFst (pair s w) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst (pair s w)) (pairSnd (pair s w))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, hw⟩
  simp only [language, Set.mem_ofPred_eq, identityQuery, sampleWord, pairFst_pair, pairSnd_pair, hg, true_and]
  rw [FlatAffineEndpointFiniteHeights.sample_packet F cone height s w tWord hs hw ht, numeric_packet F cone height s w tWord ht k,
    OrderedRealCells.mem_gap_iff_rank]

theorem gap_of_mem (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w tWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (k : Fin ((roots F cone height s).card + 1))
    (hq : pair (pair s w) (pair tWord (BinaryNatCode.encode k.val)) ∈ language F cone height) :
    FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val ∈
        OrderedRealCells.gap (roots F cone height s) k := by
  have ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord := by
    simpa only [sampleWord, pairFst_pair, pairSnd_pair] using sample_valid F cone height _ hq
  have H := (packet F cone height s w tWord hs hw ht k).mp hq
  exact (congrArg (fun t : ℝ => t ∈ OrderedRealCells.gap (roots F cone height s) k) H.1.symm).mp H.2

end LeanCanny.Encoding.FlatAffineEndpointSampleSlab
