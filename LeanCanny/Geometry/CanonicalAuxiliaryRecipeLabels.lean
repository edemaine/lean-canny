/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryRecipeRun
/-! # Finite bounded original labels replay the actual seeded sampling trace -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.ETR IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction Index run)
open AuxiliaryTiltedTerm SampleFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private def reverseIndex {r : ℕ} (i : Fin r) : Fin r := ⟨r-1-i.val,by have H:=i.isLt; omega⟩

variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

noncomputable def replay {r : ℕ}
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 : ℕ) (labels : Fin r → ℕ × ℕ) : List (Instruction (n+2) B) :=
  (List.ofFn (fun j => recipeInstruction (S:=S) (t:=t) (ht:=ht) hcap G0 j.val (labels j).1 (labels j).2)).reverse

theorem replay_length {r : ℕ}
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 : ℕ) (labels : Fin r → ℕ × ℕ) : (replay (S:=S) (t:=t) (ht:=ht) hcap G0 labels).length=r := by
  simp only [replay,List.length_reverse,List.length_ofFn]



attribute [local irreducible] IsRecipeAt recipeInstruction recipeSource replay

private theorem extract_exact
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 : ℕ) (cs : List (Instruction (n+2) B))
    (hr : ∀ i : Fin cs.length, IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 (cs.length-1-i.val) (cs.get i)) :
    ∃ labels : Fin cs.length → ℕ × ℕ, cs=replay (S:=S) (t:=t) (ht:=ht) hcap G0 labels ∧
      ∀ i, (labels i).1≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) ∧
        (labels i).2≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) := by
  have HX (i : Fin cs.length) : ∃ label : ℕ × ℕ,
      cs.get (reverseIndex i)=recipeInstruction (S:=S) (t:=t) (ht:=ht) hcap G0 i.val label.1 label.2 ∧
        label.1≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) ∧
        label.2≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) := by
    have HR0 := hr (reverseIndex i)
    unfold IsRecipeAt at HR0
    obtain ⟨c,d,hc,hC,hD⟩:=HR0
    have HI : cs.length-1-(reverseIndex i).val=i.val := by
      have H:=i.isLt
      unfold reverseIndex
      simp only
      omega
    rw [HI] at hc
    exact ⟨(c,d),hc,hC,hD⟩
  choose labels heq hC hD using HX
  refine ⟨labels,?_,fun i => ⟨hC i,hD i⟩⟩
  have HR : cs.reverse=List.ofFn (fun j => recipeInstruction (S:=S) (t:=t) (ht:=ht) hcap G0 j.val (labels j).1 (labels j).2) := by
    apply List.ext_getElem
    · simp only [List.length_reverse,List.length_ofFn]
    · intro i hi hi'
      simp only [List.getElem_reverse,List.getElem_ofFn]
      exact heq ⟨i,by simpa only [List.length_reverse] using hi⟩
  have H:=congrArg List.reverse HR
  simpa only [List.reverse_reverse,replay] using H

theorem extract_labels {r : ℕ}
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 : ℕ) (cs : List (Instruction (n+2) B)) (hlen : cs.length=r)
    (hr : ∀ i : Fin cs.length, IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 (cs.length-1-i.val) (cs.get i)) :
    ∃ labels : Fin r → ℕ × ℕ, cs=replay (S:=S) (t:=t) (ht:=ht) hcap G0 labels ∧
      ∀ i, (labels i).1≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) ∧
        (labels i).2≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) := by
  cases hlen
  exact extract_exact hcap G0 cs hr

theorem SampleTrace.exists_label_run (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 : ℕ) (hG : 1≤G0) (hword : wordBudget n D t≤G0)
    {r : ℕ} {L : SampleFrame n S B D t ht}
    (H : SampleTrace hcap (seededInitialFrame t ht hn hcap G0 hG hword) r L) :
    ∃ labels : Fin r → ℕ × ℕ, ∃ hcs : (replay (S:=S) (t:=t) (ht:=ht) hcap G0 labels).length≤S+1,
      (∀ i, (labels i).1≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) ∧
        (labels i).2≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)) ∧
      Index (Fin 0) (replay (S:=S) (t:=t) (ht:=ht) hcap G0 labels)=L.carrier ∧
      HEq (reframe (run (seededInitialState (S:=S) t ht hcap G0)
        (replay (S:=S) (t:=t) (ht:=ht) hcap G0 labels) hcs)
        (source L.frozen D t ht L.birth B L.height) L.state.critical_cap) L.state := by
  obtain ⟨cs,hlen,hcs,hr,hIndex,hState⟩:=H.toSnoc.exists_recipe_run hn hcap G0 hG hword
  obtain ⟨labels,heq,hBounds⟩:=extract_labels hcap G0 cs hlen hr
  subst cs
  exact ⟨labels,hcs,hBounds,hIndex,hState⟩
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
