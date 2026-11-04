/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
public import LeanCanny.Algebra.IntegralMixedFramedHistorySuccessor
/-! # Actual arbitrary creating commands agree on a shared chronological prefix -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixCommands
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem prefix_heq {n m S T B C :ℕ} {Q :SpatialSource n} {Q' :SpatialSource m}
    (x :State Q S B 0 (Fin 0)) (y :State Q' T C 0 (Fin 0))
    (rs :List (IntegralMixedCausalRecordBits.Record n B))
    (ds :List (IntegralMixedCausalRecordBits.Record m C))
    (hr :rs.length≤S+1) (hd :ds.length≤T+1) (fr :Instruction n B) (fd :Instruction m C)
    (a b :ℕ) (ha :a≤rs.length) (hb :b≤ds.length)
    (en :n=m) (eS :S=T) (eB :B=C) (ea :a=b) (eQ :HEq Q Q') (ex :HEq x y)
    (ep :HEq (rs.reverse.take a) (ds.reverse.take b)) :
    HEq (paddedPast fr (IntegralMixedCausalPlanBits.commands x rs hr) a)
      (paddedPast fd (IntegralMixedCausalPlanBits.commands y ds hd) b):=by
  subst m;subst T;subst C;subst b
  cases eq_of_heq eQ
  cases eq_of_heq ex
  exact heq_of_eq (IntegralMixedCausalPrefixCongruence.prefix_eq x rs ds hr hd fr fd a ha hb (eq_of_heq ep))

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)

theorem commands_heq (cL cR :List Bool) (hc :candidate cL=candidate cR)
    (hcount :IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j :ℕ) (hj :j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode :∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    HEq (paddedPast (defaultInstruction P D cL) ((D).rules cL) (number n cL+8+j))
      (paddedPast (defaultInstruction P D cR) ((D).rules cR) (number n cR+8+j)):=by
  rw [IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 cL,
    IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 cR]
  apply prefix_heq
  · rw [IntegralMixedMarkedPrefixRecords.length];omega
  · rw [IntegralMixedMarkedPrefixRecords.length];omega
  · exact IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc
  · exact congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 cL cR hc hcount)
  · exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc
  · exact congrArg (fun b=>b+8+j) (IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc)
  · exact IntegralMixedMarkedPrefixRecords.source_heq (n:=n) (t:=t) (R0:=R0) cL cR hc
  · exact IntegralMixedMarkedPrefixRecords.initial_heq hn ht ha hR0 cL cR hc hcount
  · exact IntegralMixedMarkedPrefixRecords.prefix_heq hn ht ha hR0 cL cR hc hcount j hj hcode

private theorem head_heq {a b B C :ℕ} (cs :List (Instruction a B)) (ds :List (Instruction b C))
    (x :Instruction a B) (y :Instruction b C) (xs :List (Instruction a B)) (ys :List (Instruction b C))
    (en :a=b) (eB :B=C) (he :HEq cs ds) (hx :cs=x::xs) (hy :ds=y::ys) :HEq x y:=by
  subst b;subst C
  have HE:cs=ds:=eq_of_heq he
  rw [hx,hy] at HE
  exact heq_of_eq (List.cons.inj HE).1

/-- This is literal instruction equality, so interpreted current Q is preserved
for cuts as well as the original headers of critical/integer instructions. -/
theorem creating_heq (cL cR :List Bool) (hc :candidate cL=candidate cR)
    (hcount :IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j :ℕ) (hj :j+1≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode :∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    HEq (IntegralMixedFramedRootPullback.instructionAt P D cL (number n cL+8+j))
      (IntegralMixedFramedRootPullback.instructionAt P D cR (number n cR+8+j)):=by
  have HH:=commands_heq hn ht ha hR0 cL cR hc hcount (j+1) hj hcode
  apply head_heq _ _ _ _ _ _
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc)
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc) HH
  · have H:(number n cL+8+(j+1))=(number n cL+8+j)+1:=by omega
    rw [H,paddedPast_succ]
    rfl
  · have H:(number n cR+8+(j+1))=(number n cR+8+j)+1:=by omega
    rw [H,paddedPast_succ]
    rfl

end LeanCanny.Encoding.IntegralMixedMarkedPrefixCommands
