/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPositiveSampling
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateDecode

/-! # Fixed-width native candidates meet every original clopen zero piece

The label contains bounded cut advice and the actual complete vertex, with
canonical zero padding. Decoding preserves the same packed source and joint
root word used by the bank-point coordinate readback.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open LeanCanny.Geometry LeanCanny.Geometry.CoerciveComponentSampling
open AuxiliaryTiltedTerm (polynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
theorem candidate_input_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegralMixedAuxiliaryCandidate.input hn ht ha=positiveInput hn ht ha := rfl

attribute [local irreducible] positiveInput positiveState planAt scalarWidth scalarCeiling root pair
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex

theorem exists_valid_candidate_sample {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool)
    (C : Set (Zeros (polynomial (n original) (t original)))) (hC : IsClopen C)
    (x0 : Zeros (polynomial (n original) (t original))) (hx0 : x0∈C) :
    ∃ labels : Fin (n original)→ℕ×ℕ,∃ advice w label : List Bool,
      (∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original) ∧
      label.length=IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original ∧
      IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label) ∧
      IntegralMixedAuxiliaryCandidate.source n t (pair original label)=root original labels advice ∧
      IntegralMixedAuxiliaryCandidate.vertex hn ht ha (pair original label)=w ∧
      ∃ p : Zeros (polynomial (n original) (t original)),p∈C ∧
      ∃ hw : SquareSampleCompleteVertices.Valid (positiveInput hn ht ha) (root original labels advice) w,
        ∀ i : Fin (n original),∃ j : Fin (((planAt hn ht ha).rules (root original labels advice)).length+1),
          j.val=n original-i.val ∧
          p.val i=IntegralMixedCanonicalBankPoint.point (positiveState hn ht ha (root original labels advice))
            (IntegralMixedCanonicalCompleteVertex.tuple (positiveInput hn ht ha) (root original labels advice) w hw
              (positive_count hn ht ha original labels advice)) j := by
  obtain ⟨_,_,H⟩:=exists_bounded_positive_vertex hn ht ha
  obtain ⟨labels,advice,_,hA,_,_,hprepare,hlabels,p,hp,w,hw,hwidth,hread⟩:=H original C hC x0 hx0
  have HA : advice.length=IntegralMixedAuxiliaryCandidate.adviceWidth n t original := hA
  have HW : w.length=SquareSampleCompleteVertices.width (IntegralMixedAuxiliaryCandidate.input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original advice)) := by
    rw [candidate_input_eq,hprepare]
    exact hwidth
  have HV : SquareSampleCompleteVertices.Valid (IntegralMixedAuxiliaryCandidate.input hn ht ha)
      (IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original advice)) w := by
    rw [candidate_input_eq,hprepare]
    exact hw
  refine ⟨labels,advice,w,IntegralMixedAuxiliaryCandidate.encode hn ht ha original advice w,hlabels,
    IntegralMixedAuxiliaryCandidate.encode_length hn ht ha original advice w,
    IntegralMixedAuxiliaryCandidate.valid_encode hn ht ha original advice w HA HW HV,
    (IntegralMixedAuxiliaryCandidate.source_encode hn ht ha original advice w HA).trans hprepare,
    IntegralMixedAuxiliaryCandidate.vertex_encode hn ht ha original advice w HA HW,p,hp,hw,hread⟩

end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
