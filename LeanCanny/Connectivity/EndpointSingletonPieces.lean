/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.EndpointValidation
public import LeanCanny.Connectivity.FrontierCover

/-! # Accessible singleton endpoint pieces and native nonemptiness

A description denotes either one original point or none. Its membership in
the permitted realization is an ETR query after native singleton validation.
No component-membership algorithm is used.
-/
@[expose] public section
namespace LeanCanny.Connectivity.EndpointSingletonPieces
open LeanCanny.Encoding LeanCanny.ETR LeanCanny.Computation Set
open Turing.MultiTapeTM
open scoped Classical

def piece (d : Description) (p : Formula) : Set d.realization := {x | Denotes d.dimension p x.val}

theorem eq_of_mem (d : Description) (p : Formula) {x y : d.realization}
    (hx : x∈piece d p) (hy : y∈piece d p) : x=y := by
  apply Subtype.ext
  exact ((hx.2 y.val).mp ((hy.2 y.val).mpr rfl)).symm

theorem accessible (d : Description) (p : Formula) : FrontierCover.Accessible (piece d p) := by
  intro x hx y hy
  have HS : piece d p⊆{y} := by
    intro z hz
    exact eq_of_mem d p hz hy
  have HX : x=y := closure_minimal HS isClosed_singleton hx
  subst x
  exact JoinedIn.refl (mem_insert _ _)

theorem nonempty_iff (d : Description) (hd : d.WellFormed) (p : Formula) :
    (piece d p).Nonempty↔(∃ x : Fin d.dimension→ℝ,Denotes d.dimension p x) ∧ (nonemptyQuery d p).Satisfiable := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨⟨x.val,hx⟩,(nonemptyQuery_correct hd hx.1).mpr ?_⟩
    exact ⟨x,(hx.2 x.val).mpr rfl⟩
  · rintro ⟨⟨a,ha⟩,hb⟩
    obtain ⟨b,hb⟩:=(nonemptyQuery_correct hd ha.1).mp hb
    have HE : b.val=a := (ha.2 b.val).mp hb
    refine ⟨b,?_⟩
    change Denotes d.dimension p b.val
    rw [HE]
    exact ha

theorem and_computable {α : Type} {enc : α↪List Bool} {p q : α→Formula}
    (hp : ComputableTidilyInPolyTime (fun a=>(p a).encode) enc encBits)
    (hq : ComputableTidilyInPolyTime (fun a=>(q a).encode) enc encBits) :
    ComputableTidilyInPolyTime (fun a=>(Formula.and (p a) (q a)).encode) enc encBits := by
  have H:= ComputableTidilyInPolyTime.comp (Codec.taggedTwo_mem_FP 4 pairFst_mem_FP pairSnd_mem_FP) (pair_computable hp hq)
  apply H.of_enc_eq
  intro a
  simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,Formula.encode,Formula.toData,Codec.taggedTwo_toBits]

theorem nonempty_computable {α : Type} [Inhabited α] {enc : α↪List Bool}
    {n : α→ℕ} {s p : α→Formula}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hs : ComputableTidilyInPolyTime (fun a=>(s a).encode) enc encBits)
    (hp : ComputableTidilyInPolyTime (fun a=>(p a).encode) enc encBits) :
    ComputableInPolySpace
      (fun a=>decide ((Description.mk (n a) (s a)).WellFormed ∧
        (piece (Description.mk (n a) (s a)) (p a)).Nonempty)) enc encBool := by
  have HU:=EndpointValidation.exists_denotes_computable hp hn
  have HE:=satisfiable_computable (and_computable hs hp)
  have HA : ComputableTidilyInPolyTime (fun a=>(s a).arity) enc encUnary := by
    apply (ComputableTidilyInPolyTime.comp FormulaArity.value_unary hs).of_enc_eq
    intro a
    exact congrArg encUnary (FormulaArity.value_encode (s a)).symm
  have HW:=ComputableInPolySpace.of_tidyPolyTime (ComputableTidilyInPolyTime.unary_le' HA hn)
  have HF : ComputableInPolySpace (fun _ : α=>false) enc encBool:=.of_tidyPolyTime (.const false)
  apply (HW.ite (HU.ite HE HF) HF).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  by_cases hb : (s a).arity≤n a
  · have hd : (Description.mk (n a) (s a)).WellFormed:=hb
    have H:=nonempty_iff (Description.mk (n a) (s a)) hd (p a)
    simp only [hb,ite_true,hd,true_and]
    by_cases hu : ∃ x : Fin (n a)→ℝ,Denotes (n a) (p a) x
    · simp only [hu,ite_true,decide_eq_true_eq]
      exact (H.trans (and_iff_right hu)).symm
    · simp only [hu,ite_false,Bool.false_eq_true]
      exact (iff_of_false (fun h=>hu (H.mp h).1) id).symm
  · have hd : ¬(Description.mk (n a) (s a)).WellFormed:=hb
    simp only [hb,ite_false,hd,false_and,Bool.false_eq_true]
end LeanCanny.Connectivity.EndpointSingletonPieces
