/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels

/-! # Every validated Boolean label decodes to its exact semantic cover tag -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels
open LeanCanny.Encoding LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  CanonicalAuxiliaryCandidateCover.width CanonicalAuxiliaryCandidateCover.labelBudget
  sign source candidate padding pair ClosedFormulaGateMetadata.count

theorem sign_length (q : List Bool) (hq : Guard q) : (sign q).length=signWidth (pairFst q) := by
  unfold sign
  rw [List.length_take,hq.1]
  change min (signWidth (pairFst q)) (signWidth (pairFst q)+CanonicalAuxiliaryCandidateCover.labelBudget (pairFst q))=_
  omega

noncomputable def acceptedSign (d : Description) (w : List Bool)
    (h : Valid (pair (CanonicalSignRefinement.original d) w)) : CanonicalSignRefinement.Label d :=
  ⟨sign (pair (CanonicalSignRefinement.original d) w),
    by simpa only [pairFst_pair,signWidth,CanonicalSignRefinement.width] using sign_length _ h.1,
    by simpa only [source,pairFst_pair] using h.2.1⟩

theorem source_accepted (d : Description) (w : List Bool)
    (h : Valid (pair (CanonicalSignRefinement.original d) w)) :
    CanonicalSignRefinement.source d (acceptedSign d w h)=source (pair (CanonicalSignRefinement.original d) w) := by
  unfold CanonicalSignRefinement.source acceptedSign source
  change pair (CanonicalSignRefinement.original d) (sign (pair (CanonicalSignRefinement.original d) w))=
    pair (pairFst (pair (CanonicalSignRefinement.original d) w)) (sign (pair (CanonicalSignRefinement.original d) w))
  exact congrArg (fun r=>pair r (sign (pair (CanonicalSignRefinement.original d) w))) (pairFst_pair _ _).symm

theorem candidate_length (q : List Bool) (hq : Valid q) :
    (candidate q).length=CanonicalAuxiliaryCandidateCover.width (source q) := by
  obtain ⟨hv,_⟩:=hq.2.2
  simpa only [pairSnd_pair,pairFst_pair,CanonicalAuxiliaryCandidateCover.width] using hv.1.1

noncomputable def decode (d : Description) (w : List Bool)
    (h : Valid (pair (CanonicalSignRefinement.original d) w)) : CanonicalAuxiliaryCandidateCover.Index d :=
  ⟨acceptedSign d w h,⟨candidate (pair (CanonicalSignRefinement.original d) w),by
    rw [source_accepted]
    exact candidate_length _ h⟩⟩

theorem split (q : List Bool) : pairSnd q=sign q++(candidate q++padding q) := by
  unfold sign candidate padding
  rw [List.take_append_drop,List.take_append_drop]

theorem padding_replicate (q : List Bool) (hq : Guard q) :
    padding q=List.replicate (padding q).length false := by
  apply List.eq_replicate_length.mpr
  intro b hb
  cases b
  · rfl
  · exact False.elim ((List.count_eq_zero.mp hq.2) hb)

theorem padding_length (q : List Bool) (hq : Valid q) :
    (padding q).length=CanonicalAuxiliaryCandidateCover.labelBudget (pairFst q)-(candidate q).length := by
  rw [candidate_length q hq]
  unfold padding
  rw [List.length_drop,List.length_drop,hq.1.1]
  change signWidth (pairFst q)+CanonicalAuxiliaryCandidateCover.labelBudget (pairFst q)-signWidth (pairFst q)-
    CanonicalAuxiliaryCandidateCover.width (source q)=_
  omega

theorem encode_decode (d : Description) (w : List Bool)
    (h : Valid (pair (CanonicalSignRefinement.original d) w)) :
    CanonicalAuxiliaryCandidateCover.encode d (decode d w h)=w := by
  have HP : padding (pair (CanonicalSignRefinement.original d) w)=
      List.replicate (CanonicalAuxiliaryCandidateCover.labelBudget (CanonicalSignRefinement.original d)-
        (candidate (pair (CanonicalSignRefinement.original d) w)).length) false := by
    rw [padding_replicate _ h.1,padding_length _ h,pairFst_pair]
  change sign (pair (CanonicalSignRefinement.original d) w)++
    (candidate (pair (CanonicalSignRefinement.original d) w)++
      List.replicate (CanonicalAuxiliaryCandidateCover.labelBudget (CanonicalSignRefinement.original d)-
        (candidate (pair (CanonicalSignRefinement.original d) w)).length) false)=w
  rw [←HP,←split,pairSnd_pair]

theorem decoded_nonempty (d : Description) (hd : d.WellFormed) (w : List Bool)
    (h : Valid (pair (CanonicalSignRefinement.original d) w)) :
    (CanonicalAuxiliaryCandidateCover.piece d (decode d w h)).Nonempty := by
  apply (CanonicalAuxiliaryCandidateCover.piece_nonempty_iff_good d hd _).mpr
  change AuxiliaryCandidateComponentCover.Good _ _ _
    (CanonicalSignRefinement.source d (acceptedSign d w h)) (candidate (pair (CanonicalSignRefinement.original d) w))
  rw [source_accepted]
  exact h.2.2
end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabels
