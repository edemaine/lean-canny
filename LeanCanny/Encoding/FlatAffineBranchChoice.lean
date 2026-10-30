/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointBranchLabels
public import LeanCanny.Encoding.FlatAffineCurrentNamedParents
public import LeanCanny.Computation.BoundedChoice

/-! # Computing actual sample-point parents from short branch descriptors

The bounded native search chooses a complete joint label with the requested
sample, gap, and descriptor. Its current spatial copy becomes a named rational
parent for recursive queries. No branch reference table is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointBranchLabels (source slabQuery descriptor)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def width (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q)
theorem width_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (width F cone height) :=
  (FlatAffineEndpointFiniteSample.width_unary h cone height hh).comp FlatAffineEndpointBranchLabels.source_FP

noncomputable def word (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool :=
  ImplicitGraph.word (width F cone height (pairFst r)) (Nat.fromBitsLE (pairSnd r))
theorem word_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : word F cone height ∈ FP :=
  ImplicitGraph.word_computable ((width_unary h cone height hh).comp pairFst_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP)
noncomputable def candidate (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool := pair (pairFst r) (word F cone height r)
theorem candidate_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : candidate F cone height ∈ FP :=
  mem_FP_pair pairFst_mem_FP (word_FP h cone height hh)

attribute [local irreducible] word width FlatAffineEndpointSampleSlab.language FlatAffineEndpointRankWord.word

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {r | FlatAffineEndpointBranchLabels.test F cone height (candidate F cone height r) = [true]}
theorem language_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    r ∈ language F cone height ↔ FlatAffineEndpointBranchLabels.test F cone height (candidate F cone height r) = [true] := Iff.rfl
theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  apply ((FlatAffineEndpointBranchLabels.testEvaluator h cone height hh).precompose (candidate F cone height) (candidate_FP h cone height hh)).decider
    (fun z => decide (z = [true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro r
  simp only [language, Set.mem_ofPred_eq, Function.comp_apply, decide_eq_true_eq]

noncomputable def bound (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ := 2 ^ width F cone height q
theorem bound_binary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : BinaryFn (bound F cone height) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (width_unary h cone height hh)

theorem exists_candidate (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    ∃ n < bound F cone height q, pair q (BinaryNatCode.encode n) ∈ language F cone height := by
  obtain ⟨w, hw, hs, he⟩ := hq
  have HL : w.length = width F cone height q := by unfold width; exact hw
  refine ⟨Nat.fromBitsLE w, ?_, ?_⟩
  · unfold bound
    rw [← HL]
    exact Nat.fromBitsLE_lt_pow_length w
  · have HW : word F cone height (pair q (BinaryNatCode.encode (Nat.fromBitsLE w))) = w := by
      unfold word
      rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ← HL, ImplicitGraph.word_fromBitsLE]
    simp only [language, Set.mem_ofPred_eq, candidate, pairFst_pair, HW, FlatAffineEndpointBranchLabels.test,
      FlatAffineEndpointBranchLabels.targetQuery, pairFst_pair, List.cons.injEq, and_true, decide_eq_true_eq]
    exact ⟨hs, he⟩

noncomputable def index (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ :=
  BoundedChoice.search (language F cone height) q (bound F cone height q) - 1
noncomputable def value (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  word F cone height (pair q (BinaryNatCode.encode (index F cone height q)))

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (value F cone height) := by
  have E := BoundedChoice.evaluator (decider h cone height hh) (fun q => BinaryNatCode.encode (bound F cone height q))
    (bound_binary h cone height hh).bits_mem_FP
  exact (E.withInput.postcompose (word F cone height) (word_FP h cone height hh)).congr (funext fun q => by
    simp only [value, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])

attribute [local irreducible] language bound

theorem value_spec (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    slabQuery (pair q (value F cone height q)) ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
      FlatAffineEndpointRankWord.word F cone height (pair (source q) (value F cone height q)) = descriptor q := by
  have H := (BoundedChoice.witness (language F cone height) q _ (exists_candidate F cone height q hq)).2
  have T := (language_packet F cone height _).mp H
  simp only [candidate, pairFst_pair] at T
  change FlatAffineEndpointBranchLabels.test F cone height (pair q (value F cone height q)) = [true] at T
  simpa only [FlatAffineEndpointBranchLabels.test, FlatAffineEndpointBranchLabels.targetQuery,
    FlatAffineEndpointBranchLabels.candidateQuery, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq] using T

theorem joint_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source q) (value F cone height q) := by
  simpa only [slabQuery, FlatAffineEndpointBranchLabels.candidateQuery, pairFst_pair, pairSnd_pair] using
    FlatAffineEndpointSampleSlab.joint_valid F cone height _ (value_spec F cone height q hq).1

theorem frame_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) : FlatAffineEndpointFiniteFrame.Valid F height (source q) := by
  have H := (value_spec F cone height q hq).1
  unfold FlatAffineEndpointSampleSlab.language at H
  have G := H.1
  unfold GuardedSquareSampleInput.language at G
  have HS := G.1
  change FlatAffineEndpointFiniteFrame.Valid F height (pairFst (pairFst (slabQuery (pair q (value F cone height q))))) at HS
  simpa only [slabQuery, FlatAffineEndpointBranchLabels.candidateQuery, pairFst_pair] using HS

noncomputable def parentRecord (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool := pair (source q) (value F cone height q)

theorem parentEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (parentRecord F cone height) := by
  have E := (evaluator h cone height hh).withInput.postcompose (fun r => pair (source (pairFst r)) (pairSnd r))
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := source) pairFst_mem_FP FlatAffineEndpointBranchLabels.source_FP) pairSnd_mem_FP)
  exact E.congr (funext fun q => by simp only [parentRecord, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem parent_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    parentRecord F cone height q ∈ NamedRationalParents.language (FlatAffineCurrentNamedParents.source F cone height) := by
  have H := NamedRationalParents.descriptor_valid (FlatAffineCurrentNamedParents.source F cone height) (source q)
    (FlatAffineCurrentNamedParents.root F cone height (source q) (value F cone height q)
      (frame_valid F cone height q hq) (joint_valid F cone height q hq))
  rw [FlatAffineCurrentNamedParents.root_name] at H
  exact H

noncomputable def parent (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    NamedRationalParents.Root (FlatAffineCurrentNamedParents.source F cone height) (source q) :=
  FlatAffineCurrentNamedParents.root F cone height (source q) (value F cone height q)
    (frame_valid F cone height q hq) (joint_valid F cone height q hq)

theorem parent_name (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height) :
    (FlatAffineCurrentNamedParents.source F cone height).descriptor (source q) (parent F cone height q hq) = value F cone height q :=
  FlatAffineCurrentNamedParents.root_name F cone height (source q) (value F cone height q)
    (frame_valid F cone height q hq) (joint_valid F cone height q hq)

theorem parent_point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F (source q))) :
    RationalCoordinateFamily.point (FlatAffineCurrentNamedParents.source F cone height).coordinates (source q)
      (parent F cone height q hq).val i.val = FlatAffineEndpointRankWord.currentValue F cone height (source q) (value F cone height q) i :=
  FlatAffineCurrentNamedParents.root_point F cone height (source q) (value F cone height q)
    (frame_valid F cone height q hq) (joint_valid F cone height q hq) i

end LeanCanny.Encoding.FlatAffineBranchChoice
