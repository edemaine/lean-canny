/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
public import LeanCanny.Algebra.IntegralMixedCausalPlan
/-! # Literal physical enumeration depends only on critical command tags -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalLayoutCongruence
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex IntegralMixedCausalRecordBits
open scoped Classical

structure Layout where
  index:Type
  count:ℕ
  enumeration:index≃Fin count

noncomputable def layout {n B:ℕ} (cs:List (Instruction n B)):Layout:=
  ⟨Index (Fin 0) cs,arity cs,enumerate cs⟩

private noncomputable def unitStep (L:Layout):Layout:=
  ⟨L.index⊕Unit,L.count+1,(Equiv.sumCongr L.enumeration unitEquiv).trans finSumFinEquiv⟩

private noncomputable def criticalStep (n:ℕ) (L:Layout):Layout:=
  ⟨(L.index⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit,L.count+block n+1,
    (((Equiv.sumCongr L.enumeration criticalEquiv).trans finSumFinEquiv).sumCongr unitEquiv).trans finSumFinEquiv⟩

private noncomputable def step (n:ℕ) (critical:Bool) (L:Layout):Layout:=
  if critical then criticalStep n L else unitStep L

private theorem layout_cons {n B:ℕ} (c:Instruction n B) (cs:List (Instruction n B)):
    layout (c::cs)=step n c.command.isCritical (layout cs):=by
  cases c with
  | mk P h c=>cases c <;> rfl

def tags {n B:ℕ} (cs:List (Instruction n B)):List Bool:=cs.map (fun c=>c.command.isCritical)

theorem layout_eq {n B C:ℕ} (cs:List (Instruction n B)) (ds:List (Instruction n C))
    (h:tags cs=tags ds):layout cs=layout ds:=by
  induction cs generalizing ds with
  | nil=>
    cases ds with
    | nil=>rfl
    | cons d ds=>simp only [tags,List.map_nil,List.map_cons] at h;contradiction
  | cons c cs ih=>
    cases ds with
    | nil=>simp only [tags,List.map_nil,List.map_cons] at h;contradiction
    | cons d ds=>
      have hh:=List.cons.inj h
      dsimp only at hh
      rw [layout_cons,layout_cons,hh.1,ih ds hh.2]

theorem index_eq {n B C:ℕ} (cs:List (Instruction n B)) (ds:List (Instruction n C))
    (h:tags cs=tags ds):Index (Fin 0) cs=Index (Fin 0) ds:=
  congrArg Layout.index (layout_eq cs ds h)

theorem arity_eq {n B C:ℕ} (cs:List (Instruction n B)) (ds:List (Instruction n C))
    (h:tags cs=tags ds):arity cs=arity ds:=
  congrArg Layout.count (layout_eq cs ds h)

private theorem enumeration_of_eq (L M:Layout) (h:L=M):HEq L.enumeration M.enumeration:=by
  cases h
  rfl

theorem enumerate_heq {n B C:ℕ} (cs:List (Instruction n B)) (ds:List (Instruction n C))
    (h:tags cs=tags ds):HEq (enumerate cs) (enumerate ds):=
  enumeration_of_eq _ _ (layout_eq cs ds h)

def recordCritical {n B:ℕ} (r:Record n B):Bool:=
  match r.template with
  | .critical _=>true
  | _=>false

private theorem instantiate_critical {n S B m:ℕ} {P:SpatialSource n} {I:Type}
    (x:State P S B m I) (r:Record n B):(instantiate x r).command.isCritical=recordCritical r:=by
  cases r with
  | mk Q h r=>cases r <;> rfl

theorem commands_tags {n S B:ℕ} {P:SpatialSource n} {I:Type} [Fintype I]
    (x:State P S B 0 I) (rs:List (Record n B)) (hr:rs.length≤S+1):
    tags (IntegralMixedCausalPlanBits.commands x rs hr)=rs.map recordCritical:=by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    simp only [IntegralMixedCausalPlanBits.commands_cons,tags,List.map_cons,instantiate_critical]
    exact congrArg (List.cons (recordCritical r)) (ih _)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalLayoutCongruence
