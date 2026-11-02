/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryRecipeInstruction
public import LeanCanny.Geometry.CanonicalAuxiliaryFramedRun
public import LeanCanny.Geometry.CanonicalAuxiliaryTraceHeight
/-! # Actual seeded cut traces replay literal original record instructions -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.ETR IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction Index run)
open AuxiliaryTiltedTerm SampleFrame
open scoped Classical
attribute [local irreducible] source
set_option backward.isDefEq.respectTransparency false
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

def IsRecipeAt
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 birth : ℕ) (c : Instruction (n+2) B) : Prop :=
  ∃ choice degree, c=recipeInstruction (S:=S) (t:=t) (ht:=ht) hcap G0 birth choice degree ∧
    choice≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) ∧
    degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)

attribute [local irreducible] IsRecipeAt recipeInstruction recipeSource

theorem SnocTrace.exists_recipe_run (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 : ℕ) (hG : 1≤G0) (hword : wordBudget n D t≤G0)
    {r : ℕ} {L : SampleFrame n S B D t ht}
    (H : SnocTrace hcap (seededInitialFrame t ht hn hcap G0 hG hword) r L) :
    ∃ cs : List (Instruction (n+2) B), ∃ _ : cs.length=r, ∃ hcs : cs.length≤S+1,
      (∀ i : Fin cs.length, IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 (cs.length-1-i.val) (cs.get i)) ∧
      Index (Fin 0) cs=L.carrier ∧
      HEq (reframe (run (seededInitialState (S:=S) t ht hcap G0) cs hcs)
        (source L.frozen D t ht L.birth B L.height) L.state.critical_cap) L.state := by
  induction H with
  | nil =>
    refine ⟨[],rfl,by simp,?_,rfl,?_⟩
    · intro i
      exact Fin.elim0 i
    · change HEq (reframe (seededInitialState (S:=S) t ht hcap G0) _
        (seededInitialState (S:=S) t ht hcap G0).critical_cap) (seededInitialState (S:=S) t ht hcap G0)
      rw [reframe_same]
  | @snoc F r prior hk b W ih =>
    obtain ⟨cs,hlen,hcs,hRecipe,hIndex,hState⟩ := ih
    let _ := F.finite
    let c0 : Instruction (n+2) B := IntegralMixedLimitCoordinate.instruction F.state F.criticalRule
      F.coordinate W.choice W.degree W.degree_le
    let L := W.frame hcap
    have HB : F.birth=r := by
      have HC:=prior.toForward.birth_count
      change F.birth=0+r at HC
      omega
    have HF : F.frozen=r := by
      have HC:=prior.toForward.frozen_count
      change F.frozen=0+r at HC
      omega
    have HHeight : F.height=nextHeight n S B D 1^r*G0 := prior.toForward.height_eq
    have HFront : F.Front := prior.toForward.front (by intro i; exact Fin.elim0 i)
    have HR0 : c0=recipeInstruction (S:=S) (t:=t) (ht:=ht) hcap G0 r W.choice.val W.degree :=
      F.instruction_eq_recipe HFront hcap G0 r HF HB HHeight W.choice W.degree W.degree_le
    have Hdeg := IntegralMixedLimitCoordinate.degree_auxiliaryCap
      (source F.frozen D t ht F.birth B F.height) F.criticalRule
    have HSourceDegree : (source F.frozen D t ht F.birth B F.height).degree=FixedLeadingTiltedSource.degree D := by
      unfold source
      rfl
    rw [HSourceDegree] at Hdeg
    have HChoice : W.choice.val≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) := by
      exact (Nat.le_of_lt_succ W.choice.isLt).trans Hdeg
    have HDegree : W.degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D) :=
      W.degree_le.trans Hdeg
    have Hbirth : cs.length=F.birth := hlen.trans HB.symm
    have HM : cs.length≤S := Hbirth.trans_le (birth_le F)
    have HH : (c0::cs).length≤S+1 := by simp only [List.length_cons]; omega
    have HI : Index (Fin 0) (c0::cs)=L.carrier := by
      change (Index (Fin 0) cs ⊕ Unit)=(F.carrier ⊕ Unit)
      exact congrArg (fun α : Type => α ⊕ Unit) hIndex
    have HRecipes : ∀ i : Fin (c0::cs).length,
        IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 ((c0::cs).length-1-i.val) ((c0::cs).get i) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 ((cs.length+1)-1-0) c0
        simpa only [Nat.add_sub_cancel,Nat.sub_zero,hlen] using
          (show IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 r c0 from by
            unfold IsRecipeAt
            exact ⟨W.choice.val,W.degree,HR0,HChoice,HDegree⟩)
      · have HJ:=hRecipe j
        change IsRecipeAt (S:=S) (t:=t) (ht:=ht) hcap G0 ((cs.length+1)-1-(j.val+1)) (cs.get j)
        convert HJ using 1; omega
    let R := source L.frozen D t ht L.birth B L.height
    have HS := IntegralMixedFramedStateTransport.step_reframe_heq
      (reframe (run (seededInitialState (S:=S) t ht hcap G0) cs hcs)
        (source F.frozen D t ht F.birth B F.height) F.state.critical_cap)
      F.state Hbirth hIndex hState HM (birth_le F) c0.command R L.state.critical_cap
    have HR : reframe (IntegralMixedFullHistoryScript.step F.state (birth_le F) c0.command)
        R L.state.critical_cap=L.state := by
      dsimp only [R,L,CutWitness.frame,SampleFrame.child,SampleFrame.cutState,nextState,c0,
        IntegralMixedLimitCoordinate.instruction,IntegralMixedDilationAdvance.advance,reframeDegree]
      unfold source SampleFrame.criticalRule
      rfl
    refine ⟨c0::cs,by simp only [List.length_cons,hlen],HH,HRecipes,HI,?_⟩
    have HL : reframe (run (seededInitialState (S:=S) t ht hcap G0) (c0::cs) HH) R L.state.critical_cap=
        reframe (IntegralMixedFullHistoryScript.step
          (reframe (run (seededInitialState (S:=S) t ht hcap G0) cs hcs)
            (source F.frozen D t ht F.birth B F.height) F.state.critical_cap) HM c0.command)
          R L.state.critical_cap := rfl
    exact (heq_of_eq HL).trans (HS.trans (heq_of_eq HR))
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
