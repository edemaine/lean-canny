/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixCommands
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalValues
/-! # Literal provider prefixes preserve creating instructions and metadata -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem commands_prefix_heq {n m S T B C :ℕ} {Q :SpatialSource n} {Q' :SpatialSource m}
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

private theorem head_heq {a b B C :ℕ} (cs :List (Instruction a B)) (ds :List (Instruction b C))
    (x :Instruction a B) (y :Instruction b C) (xs :List (Instruction a B)) (ys :List (Instruction b C))
    (en :a=b) (eB :B=C) (he :HEq cs ds) (hx :cs=x::xs) (hy :ds=y::ys) :HEq x y:=by
  subst b;subst C
  have HE:cs=ds:=eq_of_heq he
  rw [hx,hy] at HE
  exact heq_of_eq (List.cons.inj HE).1

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "provider" => FormulaSignSlotRadialProviderRecordPlan.providerContext
local notation "records" => FormulaSignSlotRadialProviderRecordReceipt.records
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem commands_heq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a)
    (hw : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    HEq (paddedPast (defaultInstruction P D a) ((D).rules a) (N a+j))
      (paddedPast (defaultInstruction P D b) ((D).rules b) (N b+j)) := by
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules a,FormulaSignSlotRadialProviderRecordReceipt.rules b]
  apply commands_prefix_heq
  · rw [FormulaSignSlotRadialProviderRecordReceipt.records_length];omega
  · rw [FormulaSignSlotRadialProviderRecordReceipt.records_length];omega
  · exact ambient a b hp
  · exact congrArg (·+1) (cap a b hp hc)
  · exact width a b hp
  · exact congrArg (·+j) (count_eq a b hp)
  · simpa only [initial_source] using source_heq a b hp
  · exact initial_heq a b hp hc
  · exact FormulaSignSlotRadialProviderRecordPrefix.prefix_heq a b hp hc j hj hw

theorem creating_heq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j+1≤IntegralMixedCausalRecordPlanBits.count a)
    (hw : ∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    HEq (IntegralMixedFramedRootPullback.instructionAt P D a (N a+j))
      (IntegralMixedFramedRootPullback.instructionAt P D b (N b+j)) := by
  have HH := commands_heq a b hp hc (j+1) hj hw
  apply head_heq _ _ _ _ _ _ (ambient a b hp) (width a b hp) HH
  · have H : N a+(j+1)=(N a+j)+1 := by omega
    rw [H,paddedPast_succ]
    rfl
  · have H : N b+(j+1)=(N b+j)+1 := by omega
    rw [H,paddedPast_succ]
    rfl

noncomputable def header (r : List Bool) (b : ℕ) := IntegralMixedFramedCriticalGuardBits.header T
  (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (context r) (List.replicate b true))

theorem header_actual (r : List Bool) (b : ℕ) : header r b=
    IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D r b).command := by
  have HH := IntegralFramedPhysicalCriticalReadback.header_packet P D (B).data T
    FormulaSignSlotRadialProviderAtomic.bank_represents (B).key IntegralFramedPhysicalCriticalGuardScan.stage
    (context r) (List.replicate b true) b
    (by simp only [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate])
  have HR := key_root r
  have HI := IntegralMixedFramedRootPullback.instructionAt_congr P D _ r b b HR rfl
  have HE := IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralMixedCommandHeaderBits.command I.command) _ _
    (congrArg (P).ambient HR) (congrArg (P).width HR) HI
  exact HH.trans HE

theorem header_eq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j+1≤IntegralMixedCausalRecordPlanBits.count a)
    (hw : ∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    header a (N a+j)=header b (N b+j) := by
  rw [header_actual,header_actual]
  exact IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralMixedCommandHeaderBits.command I.command) _ _ (ambient a b hp) (width a b hp)
    (creating_heq a b hp hc j hj hw)

theorem prefix_arity_observation (r : List Bool) (j : ℕ)
    (hj : j≤IntegralMixedCausalRecordPlanBits.count r) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (context r)) (List.replicate (N r+j) true))=
      (observation r j hj).arity := by
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet P D (B).data T
    FormulaSignSlotRadialProviderAtomic.bank_represents,key_root]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
