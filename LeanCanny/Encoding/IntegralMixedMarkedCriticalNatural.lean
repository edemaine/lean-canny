/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalScanSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # Historical critical guards compare literal natural columns and bank fields -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedCriticalNatural
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedPhysicalPointCompanionScan.retained
  IntegralMixedPhysicalFieldEquality.point IntegralMixedPhysicalPointCompanionScan.scalarValue

theorem selected_block (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w) (b :ℕ)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX root) b) :
    IntegralMixedPhysicalPointEquality.block hn ht ha (radius_binary hR0) false (CTX root) w hw b
      (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b)=
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw
      (IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate b true))+
        IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b)^
      UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root) b:=by
  let j:=IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b
  let col:=IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate b true))+j
  have HL:=IntegralMixedFramedCriticalGuardBits.physical_lt P (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (CTX root) (List.replicate b true)) hb
  have HE :IntegralMixedFramedCriticalGuardBits.physical P T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
      (pair (CTX root) (List.replicate b true))=col:=by
    simp only [col,j,IntegralMixedPhysicalPointCompanionScan.selected,IntegralMixedFramedCriticalGuardBits.physical,
      IntegralMixedFramedCriticalGuardBits.packet,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
      IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate,Nat.add_assoc]
  have HC :col<(S).count (CTX root):=by
    rw [←HE]
    exact HL.trans_eq (IntegralMixedPhysicalGuardScan.count_eq hn ht ha (radius_binary hR0) false
      (CTX root) (List.replicate b true))
  have HN :IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw col=
      (SquareSampleCompleteVertices.candidate S (CTX root) w hw).val ⟨col,HC⟩:=by
    unfold IntegralMixedMarkedPrefixFieldReadback.natural IntegralFramedPhysicalSquare.naturalPoint
    have HC' :col<IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key (CTX root)):=HC
    rw [dite_eq_left HC']
    rfl
  unfold IntegralMixedPhysicalPointEquality.block
  rw [dite_eq_left HC,←HN]
  have HR :pairFst ((B).key (CTX root))=root:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  simp only [IntegralMixedFramedCriticalGuardBits.physicalPower,HR]
  rfl

theorem scalarValue_zero_iff (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w) (b :ℕ)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX root) b) :
    IntegralMixedPhysicalPointCompanionScan.scalarValue hn ht ha (radius_binary hR0) false (CTX root) w b=
        InfinitesimalSign.encode 0↔
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX root) w hw b=
        IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw
          (IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate b true))+
            IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b)^
          UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root) b:=by
  rw [IntegralMixedPhysicalPointCompanionScan.scalarValue_zero_iff hn ht ha (radius_binary hR0) false (CTX root) w hw b hb,
    IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0) (CTX root) w hw b hb,
    selected_block hn ht ha hR0 root w hw b hb]

end LeanCanny.Encoding.IntegralMixedMarkedCriticalNatural
