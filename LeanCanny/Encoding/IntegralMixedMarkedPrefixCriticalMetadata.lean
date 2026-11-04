/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixCommands
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalScanSemantics
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalValues
/-! # Shared original prefixes preserve the actual historical critical metadata -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixCriticalMetadata
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedPhysicalIndex.prefixArity

noncomputable def header (root :List Bool) (b :ℕ):=IntegralMixedFramedCriticalGuardBits.header T
  (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (CTX root) (List.replicate b true))

theorem header_actual (root :List Bool) (b :ℕ):header hn ht ha hR0 root b=
    IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D root b).command:=by
  have HH:=IntegralFramedPhysicalCriticalReadback.header_packet P D H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false) (B).key
    IntegralFramedPhysicalCriticalGuardScan.stage (CTX root) (List.replicate b true) b
    (by simp only [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate])
  have HR :pairFst ((B).key (CTX root))=root:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  have HI:=IntegralMixedFramedRootPullback.instructionAt_congr P D _ root b b HR rfl
  have HE:=IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralMixedCommandHeaderBits.command I.command) _ _
    (congrArg (P).ambient HR) (congrArg (P).width HR) HI
  exact HH.trans HE

attribute [local semireducible] IntegralMixedPhysicalMarkedPlan.bank

theorem header_eq (cL cR :List Bool) (hc :candidate cL=candidate cR)
    (hcount :IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j :ℕ) (hj :j+1≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode :∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    header hn ht ha hR0 cL (number n cL+8+j)=header hn ht ha hR0 cR (number n cR+8+j):=by
  rw [header_actual,header_actual]
  exact IntegralMixedFramedRootPullback.instruction_read (fun _ _ I=>IntegralMixedCommandHeaderBits.command I.command)
    _ _ (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc)
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc)
    (IntegralMixedMarkedPrefixCommands.creating_heq hn ht ha hR0 cL cR hc hcount j hj hcode)

private theorem arity_heq {a b u v :ℕ}
    (cs :List (IntegralMixedFramedHistoryScript.Instruction a u))
    (ds :List (IntegralMixedFramedHistoryScript.Instruction b v))
    (ha :a=b) (hB :u=v) (he :HEq cs ds) :
    IntegralMixedFramedPhysicalIndex.arity cs=IntegralMixedFramedPhysicalIndex.arity ds:=by
  subst b;subst v;cases eq_of_heq he;rfl

theorem arity_eq (cL cR :List Bool) (hc :candidate cL=candidate cR)
    (hcount :IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j :ℕ) (hj :j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode :∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX cL)) (List.replicate (number n cL+8+j) true))=
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX cR)) (List.replicate (number n cR+8+j) true)):=by
  have HR (r :List Bool):pairFst ((B).key (CTX r))=r:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),
    IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),HR,HR]
  exact arity_heq _ _ (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc)
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc)
    (IntegralMixedMarkedPrefixCommands.commands_heq hn ht ha hR0 cL cR hc hcount j hj hcode)

end LeanCanny.Encoding.IntegralMixedMarkedPrefixCriticalMetadata
