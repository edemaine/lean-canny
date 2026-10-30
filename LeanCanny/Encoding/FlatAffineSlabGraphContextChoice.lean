/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphContextComplete
public import LeanCanny.Computation.BoundedChoice

/-! # Computing an accepted context for a bounded original gap

Input is a prepared finite frame paired with the binary gap code. The search
enumerates full context records at their derived unary width and validates
every candidate with the native scalar routines. No algebraic labels are
supplied by the caller.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphContextChoice
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphContext (record)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def endpointWidth (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (IntegerPolynomialSampleInput.input (FlatAffineEndpointAdjacentSamples.heightSource F cone height))
    (pairFst (pairFst q))
noncomputable def sampleWidth (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (FlatAffineEndpointSamples.input F cone height) (pairFst (pairFst q))
noncomputable def width (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ :=
  4 * (pairFst q).length + 2 * (pairSnd q).length +
    6 * endpointWidth F cone height q + 3 * sampleWidth F cone height q + 14

theorem width_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (width F cone height) := by
  have P := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have A := (IntegerPolynomialSampleInput.width_unary (FlatAffineEndpointAdjacentSamples.heightAccess h cone height hh)).comp P
  have T := (FlatAffineEndpointSamples.vertexWidth_unary h cone height hh).comp P
  exact ((((UnaryFn.const 4).mul (UnaryFn.length pairFst_mem_FP)).add
    ((UnaryFn.const 2).mul (UnaryFn.length pairSnd_mem_FP))).add
    ((UnaryFn.const 6).mul A)).add ((UnaryFn.const 3).mul T) |>.add (UnaryFn.const 14)

noncomputable def candidate (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool :=
  ImplicitGraph.word (width F cone height (pairFst r)) (Nat.fromBitsLE (pairSnd r))
theorem candidate_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : candidate F cone height ∈ FP :=
  ImplicitGraph.word_computable ((width_unary h cone height hh).comp pairFst_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP)

attribute [local irreducible] candidate width endpointWidth sampleWidth FlatAffineSlabGraphContext.language

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {r | candidate F cone height r ∈ FlatAffineSlabGraphContext.language F cone height ∧
    FlatAffineSlabGraphCodes.source (candidate F cone height r) = pairFst (pairFst r) ∧
    FlatAffineSlabGraphCodes.gapWord (candidate F cone height r) = pairSnd (pairFst r)}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have C := candidate_FP h cone height hh
  have V := ((FlatAffineSlabGraphContext.decider h cone height hh).precompose (candidate F cone height) C).flagEvaluator
  have P := (Brackets.stringEq_fppred (mem_FP_comp C FlatAffineSlabGraphCodes.source_FP)
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).and
    (Brackets.stringEq_fppred (mem_FP_comp C FlatAffineSlabGraphCodes.gapWord_FP)
      (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
  apply (V.andFlags (SpaceFunction.ofFP _ P.flag_mem_FP)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro r
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq]

noncomputable def bound (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ := 2 ^ width F cone height q
theorem bound_binary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : BinaryFn (bound F cone height) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (width_unary h cone height hh)

attribute [local irreducible] bound

theorem exists_candidate (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointSampleSlab.roots F cone height s).card) :
    ∃ n < bound F cone height (pair s (BinaryNatCode.encode k.val)),
      pair (pair s (BinaryNatCode.encode k.val)) (BinaryNatCode.encode n) ∈ language F cone height := by
  obtain ⟨a, t, b, u, hc⟩ := FlatAffineSlabGraphContext.complete_record F cone height s hs k h0 hk
  let c := record s (BinaryNatCode.encode k.val) a t b u
  let q := pair s (BinaryNatCode.encode k.val)
  have HA (side : Bool) := (Classical.choose (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc)).1
  have HT (side : Bool) := (Classical.choose (FlatAffineSlabGraphContext.sample_label_valid F cone height side c hc)).1
  simp only [c, FlatAffineSlabGraphContext.record_source, FlatAffineSlabGraphContext.record_endpoint,
    FlatAffineSlabGraphContext.record_sample] at HA HT
  have HL : c.length = width F cone height q := by
    have A := HA false
    have B := HA true
    have T := HT false
    have U := HT true
    change a.length = _ at A
    change b.length = _ at B
    change t.length = _ at T
    change u.length = _ at U
    simp only [c, record, pair_length, width, endpointWidth, sampleWidth, q, pairFst_pair, pairSnd_pair]
    rw [A, B, T, U]
    simp only [SquareSampleCompleteVertices.width]
    omega
  refine ⟨Nat.fromBitsLE c, ?_, ?_⟩
  · unfold bound
    change Nat.fromBitsLE c < 2 ^ width F cone height q
    rw [← HL]
    exact Nat.fromBitsLE_lt_pow_length c
  · have H : candidate F cone height (pair q (BinaryNatCode.encode (Nat.fromBitsLE c))) = c := by
      simp only [candidate, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      rw [← HL, ImplicitGraph.word_fromBitsLE]
    change candidate F cone height _ ∈ FlatAffineSlabGraphContext.language F cone height ∧ _
    simp only [H, pairFst_pair, pairSnd_pair, q]
    exact ⟨hc, FlatAffineSlabGraphContext.record_source _ _ _ _ _ _, FlatAffineSlabGraphContext.record_gap _ _ _ _ _ _⟩

noncomputable def index (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℕ :=
  BoundedChoice.search (language F cone height) q (bound F cone height q) - 1
noncomputable def value (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  candidate F cone height (pair q (BinaryNatCode.encode (index F cone height q)))

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (value F cone height) := by
  have E := BoundedChoice.evaluator (decider h cone height hh) (fun q => BinaryNatCode.encode (bound F cone height q))
    (bound_binary h cone height hh).bits_mem_FP
  exact (E.withInput.postcompose (candidate F cone height) (candidate_FP h cone height hh)).congr (funext fun q => by
    simp only [value, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem value_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointSampleSlab.roots F cone height s).card) :
    value F cone height (pair s (BinaryNatCode.encode k.val)) ∈ FlatAffineSlabGraphContext.language F cone height ∧
      FlatAffineSlabGraphCodes.source (value F cone height (pair s (BinaryNatCode.encode k.val))) = s ∧
      FlatAffineSlabGraphCodes.gapWord (value F cone height (pair s (BinaryNatCode.encode k.val))) = BinaryNatCode.encode k.val := by
  have H := (BoundedChoice.witness (language F cone height) (pair s (BinaryNatCode.encode k.val)) _
    (exists_candidate F cone height s hs k h0 hk)).2
  simpa only [language, Set.mem_ofPred_eq, value, index, pairFst_pair, pairSnd_pair] using H

end LeanCanny.Encoding.FlatAffineSlabGraphContextChoice
