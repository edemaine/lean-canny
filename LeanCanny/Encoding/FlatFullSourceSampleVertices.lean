/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleDescriptors
public import LeanCanny.Encoding.FlatFullSourceSampleTestSign

/-! # Fixed-width native vertices for regular original flat roots

Ordinal words have a native polynomial width. Validity uses the internally
computed regular-root count. Every valid word names exactly one regular
original root, and every such root has one word. These are sample vertices;
component-preserving edges and coverage of general fibers remain separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleVertices
open LeanCanny.Algebra LeanCanny.Computation
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def width (F : Inputs) := FlatFullSourceSampleParameters.labelWidth F
theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  FlatFullSourceSampleParameters.labelWidth_unary h

def Valid (F : Inputs) (u w : List Bool) : Prop :=
  w.length = width F u ∧ Nat.fromBitsLE w < FlatFullSourceSampleRegularCount.count F u

noncomputable def ordinalEquiv (F : Inputs) (u : List Bool) :
    Fin (FlatFullSourceSampleRegularCount.count F u) ≃ FlatFullSourceSampleParameters.OriginalCandidates F u :=
  (FlatFullSourceSampleHashEnumeration.candidateEquiv F u).trans (FlatFullSourceSampleParameters.paddingEquiv F u).symm

noncomputable def sample (F : Inputs) (u w : List Bool) (h : Valid F u w) :
    FlatFullSourceSampleParameters.OriginalCandidates F u :=
  ordinalEquiv F u ⟨Nat.fromBitsLE w, h.2⟩

private theorem word_value (w k : ℕ) (hk : k < 2 ^ w) : Nat.fromBitsLE (ImplicitGraph.word w k) = k := by
  have he := FixedWidthNatVector.decode_block 1 w (fun _ => k) 0 (by decide) hk
  simp only [Nat.zero_mul, List.drop_zero] at he
  change Nat.fromBitsLE ((ImplicitGraph.word w k).take w) = k at he
  simpa only [List.take_of_length_le (ImplicitGraph.length_word w k).le] using he

noncomputable def word (F : Inputs) (u : List Bool) (z : FlatFullSourceSampleParameters.OriginalCandidates F u) : List Bool :=
  ImplicitGraph.word (width F u) ((ordinalEquiv F u).symm z).val

theorem word_valid (F : Inputs) (u : List Bool) (z : FlatFullSourceSampleParameters.OriginalCandidates F u) :
    Valid F u (word F u z) := by
  have hr := ((ordinalEquiv F u).symm z).isLt
  have hb : ((ordinalEquiv F u).symm z).val < 2 ^ width F u :=
    hr.trans_le (FlatFullSourceSampleRegularCount.count_le F u)
  refine ⟨ImplicitGraph.length_word _ _, ?_⟩
  change Nat.fromBitsLE (ImplicitGraph.word (width F u) ((ordinalEquiv F u).symm z).val) < _
  rw [word_value _ _ hb]
  exact hr

theorem sample_word (F : Inputs) (u : List Bool) (z : FlatFullSourceSampleParameters.OriginalCandidates F u) :
    sample F u (word F u z) (word_valid F u z) = z := by
  have hr := ((ordinalEquiv F u).symm z).isLt
  have hb : ((ordinalEquiv F u).symm z).val < 2 ^ width F u :=
    hr.trans_le (FlatFullSourceSampleRegularCount.count_le F u)
  have hi : (⟨Nat.fromBitsLE (word F u z), (word_valid F u z).2⟩ : Fin (FlatFullSourceSampleRegularCount.count F u)) =
      (ordinalEquiv F u).symm z := by
    apply Fin.ext
    exact word_value _ _ hb
  rw [sample, hi, Equiv.apply_symm_apply]

theorem sample_injective (F : Inputs) (u w v : List Bool) (hw : Valid F u w) (hv : Valid F u v)
    (he : sample F u w hw = sample F u v hv) : w = v := by
  have hi := congrArg Fin.val ((ordinalEquiv F u).injective he)
  change Nat.fromBitsLE w = Nat.fromBitsLE v at hi
  calc
    w = ImplicitGraph.word (width F u) (Nat.fromBitsLE w) := by rw [← hw.1, ImplicitGraph.word_fromBitsLE]
    _ = ImplicitGraph.word (width F u) (Nat.fromBitsLE v) := by rw [hi]
    _ = v := by rw [← hv.1, ImplicitGraph.word_fromBitsLE]

noncomputable def vertexEquiv (F : Inputs) (u : List Bool) :
    {w : List Bool // Valid F u w} ≃ FlatFullSourceSampleParameters.OriginalCandidates F u :=
  Equiv.ofBijective (fun w => sample F u w.val w.property)
    ⟨fun w v he => Subtype.ext (sample_injective F u w.val v.val w.property v.property he),
      fun z => ⟨⟨word F u z, word_valid F u z⟩, sample_word F u z⟩⟩

def language (F : Inputs) : Language := {q | Valid F (pairFst q) (pairSnd q)}

noncomputable def accept (F : Inputs) (z : List Bool) : Bool := decide
  ((pairSnd (pairFst z)).length = width F (pairFst (pairFst z)) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairSnd z))

theorem accept_FP {F : Inputs} (h : F.Access) : (fun z => [accept F z]) ∈ FP := by
  have hs := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have he := FPPred.eq (UnaryFn.length hs) ((width_unary h).comp hc)
  have hi := (BinaryFn.fromBits hs).lt (BinaryFn.fromBits pairSnd_mem_FP)
  exact (he.and hi).flag_mem_FP

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have E := (FlatFullSourceSampleRegularCount.evaluator h).precompose pairFst pairFst_mem_FP
  apply E.withInput.decider (accept F) (accept_FP h)
  intro q
  simp only [language, Valid, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

def normalizeQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.normalize (pairSnd q))

theorem normalizeQuery_FP : normalizeQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def signValue (F : Inputs) (T : FlatFullSourceSampleTestMoments.Test) : List Bool → List Bool :=
  FlatFullSourceSampleTestSign.atOrdinal F T ∘ normalizeQuery

theorem sign_evaluator {F : Inputs} (h : F.Access) {T : FlatFullSourceSampleTestMoments.Test} (A : T.Access) :
    SpaceFunction (signValue F T) :=
  (FlatFullSourceSampleTestSign.ordinal_evaluator h A).precompose normalizeQuery normalizeQuery_FP

theorem sign_packet (F : Inputs) (T : FlatFullSourceSampleTestMoments.Test) (u w : List Bool) (h : Valid F u w) :
    signValue F T (pair u w) = InfinitesimalSign.encode
      (FlatFullSourceSampleTestMoments.sign T u
        (FlatFullSourceSampleHashEnumeration.root F u ⟨Nat.fromBitsLE w, h.2⟩).val) := by
  have H := FlatFullSourceSampleTestSign.ordinal_packet F T u ⟨Nat.fromBitsLE w, h.2⟩
  simpa only [signValue, Function.comp_apply, normalizeQuery, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode] using H

end LeanCanny.Encoding.FlatFullSourceSampleVertices
