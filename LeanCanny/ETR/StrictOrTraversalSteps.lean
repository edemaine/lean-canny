/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.StrictOrTraversal
public import LeanCanny.ETR.StrictOrSyntax
/-! # Exact native traversal steps protect every strict atom's original arithmetic term -/
@[expose] public section
namespace LeanCanny.ETR.StrictOrTraversal
open LeanCanny.Encoding LeanCanny.Encoding.Brackets

private theorem hasTwo_or (p q : Formula) : NNF.HasTwo 5 (Formula.or p q).encode := by
  rw [Formula.encode,NNF.hasTwo_toBits]
  exact ⟨p.toData,q.toData,rfl⟩
private theorem noTwo_lt (t : Term) : ¬NNF.HasTwo 5 (Formula.ltZero t).encode := by
  rw [Formula.encode,NNF.hasTwo_toBits]
  simp [Formula.toData,NNF.two,Codec.unary]
private theorem hasOne_lt (t : Term) : NNF.HasOne 2 (Formula.ltZero t).encode := by
  rw [Formula.encode,NNF.hasOne_toBits]
  exact ⟨t.toData,rfl⟩
private theorem noTwo_false : ¬NNF.HasTwo 5 Formula.falsum.encode := by
  rw [Formula.encode,NNF.hasTwo_toBits]
  simp [Formula.toData,NNF.two,Codec.unary]
private theorem noOne_false : ¬NNF.HasOne 2 Formula.falsum.encode := by
  rw [Formula.encode,NNF.hasOne_toBits]
  simp [Formula.toData,NNF.one,Codec.unary]
private theorem todo_nonempty (p : Formula) (tail : List Bool) : p.encode++tail≠[] := by
  intro H
  have HL:=congrArg List.length H
  have HP : 0<p.encode.length := by simp [Formula.encode]
  simp only [List.length_append,List.length_nil] at HL
  omega

theorem negative_term (t : Term) : negative t.toData.toBits=(Term.mul (.const (-1)) t).toData.toBits := by
  exact (Term.mul_toBits _ _).symm

theorem step_empty (out : List Bool) : step (pair [] out)=pair [] out := by
  simp only [step,pairFst_pair,pairSnd_pair,ite_true]

theorem step_or (p q : Formula) (tail out : List Bool) :
    step (pair ((Formula.or p q).encode++tail) out)=pair (p.encode++q.encode++tail) out := by
  have HN : firstNode ((Formula.or p q).encode++tail)=(Formula.or p q).encode := firstNode_toBits_append _ _
  have HT : afterNode ((Formula.or p q).encode++tail)=tail := afterNode_toBits_append _ _
  have HO:=hasTwo_or p q
  simp only [step,pairFst_pair,pairSnd_pair,HN,HT,ite_eq_right (todo_nonempty (Formula.or p q) tail),ite_eq_left HO]
  simp only [NNF.second,NNF.third,Formula.encode,Formula.toData,remainingChildren_toBits,firstChild_toBits]

theorem step_lt (t : Term) (tail out : List Bool) :
    step (pair ((Formula.ltZero t).encode++tail) out)=pair tail (out++(Term.mul (.const (-1)) t).toData.toBits) := by
  have HN : firstNode ((Formula.ltZero t).encode++tail)=(Formula.ltZero t).encode := firstNode_toBits_append _ _
  have HT : afterNode ((Formula.ltZero t).encode++tail)=tail := afterNode_toBits_append _ _
  have HO:=noTwo_lt t
  have HA:=hasOne_lt t
  simp only [step,pairFst_pair,pairSnd_pair,HN,HT,
    ite_eq_right (todo_nonempty (Formula.ltZero t) tail),ite_eq_right HO,ite_eq_left HA]
  simp only [NNF.second,Formula.encode,Formula.toData,remainingChildren_toBits,firstChild_toBits,negative_term]

theorem step_false (tail out : List Bool) :
    step (pair (Formula.falsum.encode++tail) out)=pair tail out := by
  have HN : firstNode (Formula.falsum.encode++tail)=Formula.falsum.encode := firstNode_toBits_append _ _
  have HT : afterNode (Formula.falsum.encode++tail)=tail := afterNode_toBits_append _ _
  simp only [step,pairFst_pair,pairSnd_pair,HN,HT,
    ite_eq_right (todo_nonempty Formula.falsum tail),ite_eq_right noTwo_false,ite_eq_right noOne_false]

end LeanCanny.ETR.StrictOrTraversal
