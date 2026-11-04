/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendNoCut
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendParent
public import LeanCanny.Algebra.IntegralMixedFramedCriticalPrefixArity
/-! # Physical prefix arity at the start of the actual retained extension -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "ROOT"=>preparedRoot hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot context parentCommands

theorem native_root (old : List Bool) (e : ℕ) :
    pairFst ((B).key (CTX old e))=ROOT old e:=by
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),context,pairFst_pair]

theorem native_dimension (old : List Bool) (e : ℕ) :
    (P).ambient (pairFst ((B).key (CTX old e)))=D old:=by
  rw [native_root]
  have H:=dimension_root hn ht ha hR0 old e
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  exact H

theorem prefix_arity_begin (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) :
    prefixArity P T (pair ((B).key (CTX old e)) (List.replicate (beginBirth hn ht ha hR0 old) true))=
      arity (parentCommands hn ht ha hR0 old hv hd e he):=by
  rw [prefixArity_packet P (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),native_root]
  have HB : beginBirth hn ht ha hR0 old=number n (ROOT old e)+8+start hn ht ha hR0 old:=by
    rw [initial_root]
    rfl
  rw [HB]
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  exact congrArg arity (parent_commands hn ht ha hR0 old hv hd e he)

theorem new_header_context (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : beginBirth hn ht ha hR0 old≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) :
    (IntegralMixedCommandHeaderBits.lookup ((T).commands (pairFst ((B).key (CTX old e)))) b).context=1:=by
  have H:=(active_after_begin hn ht ha hR0 old hv hd e he b hb0 hb1).2
  change (IntegralMixedFramedCriticalGuardBits.header T
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (CTX old e) (List.replicate b true))).context=1 at H
  simpa only [IntegralMixedFramedCriticalGuardBits.header,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
    IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate] using H

theorem prefix_arity_after_begin (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : beginBirth hn ht ha hR0 old≤b) (hb1 : b≤fullBirth hn ht ha hR0 old e) :
    prefixArity P T (pair ((B).key (CTX old e)) (List.replicate b true))=
      arity (parentCommands hn ht ha hR0 old hv hd e he)+
        (2*D old+4)*(b-beginBirth hn ht ha hR0 old):=by
  rw [prefixArity_critical_interval P T ((B).key (CTX old e)) _ b hb0
    (fun j hj0 hj1=>new_header_context hn ht ha hR0 old hv hd e he j hj0 (hj1.trans_le hb1)),
    prefix_arity_begin hn ht ha hR0 old hv hd e he,native_dimension]

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
