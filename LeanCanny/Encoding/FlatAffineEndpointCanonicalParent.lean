/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextRebase
public import LeanCanny.Encoding.FlatAffineEndpointAncestorMatch
public import LeanCanny.Encoding.FlatAffineLastHeightRow

/-! # Original-context ancestor words for native endpoint markers

The marker's own endpoint copy supplies the ancestor. Native re-encoding
places its word in the original parent sampler, preserving its whole power
root. A native word comparison filters the exact decoded parent root.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointCanonicalParent
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open FlatAffineEndpointMarkers (source)
open FlatAffineJointPrefixChoice (original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineEndpointAncestorMatch.value SquareSampleContextRebase.value
  FlatAffineEndpointMarkers.language

def prepare (z : List Bool) : List Bool := pair (source (pairFst z)) (pairSnd z)
theorem prepare_FP : prepare ∈ FP := by polytime [prepare, source]

noncomputable def parentRecord (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : List Bool :=
  pair (source q) (FlatAffineEndpointAncestorMatch.value (next F) C (row F h) q)

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : List Bool → List Bool :=
  SquareSampleContextRebase.value (FlatAffinePowerSampleInput.input F (parentCone F C)) original ∘ parentRecord F C h

theorem evaluator {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : SpaceFunction (value F C h) := by
  have E := (FlatAffineEndpointAncestorMatch.evaluator
    (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) C
    (row F h) (FlatAffineLastHeightRow.row_unary hF h hh)).withInput.postcompose prepare prepare_FP
  have HE : SpaceFunction (parentRecord F C h) := E.congr (funext fun q => by
    simp only [Function.comp_apply, prepare, parentRecord, pairFst_pair, pairSnd_pair]
    rfl)
  exact HE.chain (SquareSampleContextRebase.evaluator (FlatAffinePowerSampleInput.access hF (parentCone F C))
    FlatAffineJointPrefixChoice.original_FP)

theorem raw_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    SquareSampleCompleteVertices.Valid (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (parentCone F C)) original)
      (source q) (FlatAffineEndpointAncestorMatch.value (next F) C (row F h) q) := by
  rw [← FlatAffineLastHeightRow.target_eq F C h]
  exact FlatAffineEndpointAncestorMatch.value_valid (next F) C (row F h) q hq
    (FlatAffineLastHeightRow.ordinary F h _)

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    FlatAffineCompleteVertices.Valid F (parentCone F C) (original (source q)) (value F C h q) :=
  SquareSampleContextRebase.value_valid _ (FlatAffinePowerSampleInput.complete F (parentCone F C))
    original (source q) _ (raw_valid F C h q hq)

theorem value_powerPoint (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C))
      (original (source q)) (value F C h q) (value_valid F C h q hq)).val =
    (SquareSampleCompleteVertices.candidate
      (SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (parentCone F C)) original) (source q)
      (FlatAffineEndpointAncestorMatch.value (next F) C (row F h) q) (raw_valid F C h q hq)).val :=
  SquareSampleContextRebase.value_point _ (FlatAffinePowerSampleInput.complete F (parentCone F C))
    original (source q) _ (raw_valid F C h q hq)

noncomputable def parent (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    FlatAffinePowerSampleInput.OriginalRoots F (original (source q)) :=
  FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original (source q)) ⟨value F C h q, value_valid F C h q hq⟩

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : Language :=
  {q | pairFst q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h) ∧ value F C h (pairFst q) = pairSnd q}

theorem decider {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : SpaceDecider (language F C h) := by
  have V := ((evaluator hF C h hh).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP pairSnd pairSnd_mem_FP)
  have E := V.postcompose (fun q => [decide (pairFst q = pairSnd q)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D := ((FlatAffineEndpointMarkers.decider
    (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) C (row F h)
    (FlatAffineLastHeightRow.row_unary hF h hh)).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (D.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]
  rfl

theorem mem_PSPACE {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : language F C h ∈ PSPACE :=
  (decider hF C h hh).mem_PSPACE

theorem packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language (next F) C (row F h))
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) (original (source q)) v) :
    pair q v ∈ language F C h ↔ parent F C h q hq =
      FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original (source q)) ⟨v, hv⟩ := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hq, true_and]
  constructor
  · intro he
    subst v
    rfl
  · intro he
    exact congrArg Subtype.val ((FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) (original (source q))).injective he)

end LeanCanny.Encoding.FlatAffineEndpointCanonicalParent
