/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPositiveVertex
public import LeanCanny.Encoding.IntegralMixedAuxiliaryBoundedSampling

/-! # Actual positive-prefix vertices meet every original clopen zero piece

Cut choices have fixed-width advice and a native prepared root. The complete
vertex represents an actual joint prefix root, preserving all original
coordinates through the same default-extended bank.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open LeanCanny.Geometry LeanCanny.Geometry.CoerciveComponentSampling
open AuxiliaryTiltedTerm (polynomial)
open scoped Classical

theorem exists_bounded_positive_vertex {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    ∃ rootBound adviceBound : Polynomial ℕ, ∀ original,
      ∀ C : Set (Zeros (polynomial (n original) (t original))), IsClopen C →
      ∀ x0 : Zeros (polynomial (n original) (t original)), x0∈C →
      ∃ labels : Fin (n original)→ℕ×ℕ, ∃ advice : List Bool,
        advice=IntegralMixedAuxiliaryChoiceAdvice.encode (scalarWidth n t original) labels ∧
        advice.length=2*n original*scalarWidth n t original ∧
        advice.length≤adviceBound.eval original.length ∧
        (root original labels advice).length≤rootBound.eval original.length ∧
        IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original advice)=root original labels advice ∧
        (∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original) ∧
        ∃ p : Zeros (polynomial (n original) (t original)), p∈C ∧
        ∃ w : List Bool, ∃ hw : SquareSampleCompleteVertices.Valid (positiveInput hn ht ha) (root original labels advice) w,
          w.length=SquareSampleCompleteVertices.width (positiveInput hn ht ha) (root original labels advice) ∧
          ∀ i : Fin (n original),∃ j : Fin (((planAt hn ht ha).rules (root original labels advice)).length+1),
            j.val=n original-i.val ∧
            p.val i=IntegralMixedCanonicalBankPoint.point (positiveState hn ht ha (root original labels advice))
              (IntegralMixedCanonicalCompleteVertex.tuple (positiveInput hn ht ha) (root original labels advice) w hw
                (positive_count hn ht ha original labels advice)) j := by
  obtain ⟨r,a,H⟩:=exists_bounded_prepared_run_sample hn ht ha
  refine ⟨r,a,fun original C hC x0 hx0 => ?_⟩
  obtain ⟨labels,advice,he,hlen,haBound,hrBound,hprepare,hlabels,p,hp,hreal⟩:=H original C hC x0 hx0
  obtain ⟨w,hw,hwidth,hread⟩:=positive_vertex_of_realization hn ht ha original labels advice p.val hreal
  exact ⟨labels,advice,he,hlen,haBound,hrBound,hprepare,hlabels,p,hp,w,hw,hwidth,hread⟩

end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
