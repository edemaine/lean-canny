/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbePrefix
public import LeanCanny.Geometry.IntegralMixedBankValueInterpretation
/-! # Actual provider coordinate probes share their full parent and sweep equations -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem raw_shape {n m : ℕ} (w : List Bool) (g j k : ℕ)
    (hj : IntegralMixedChronologicalCutCode.Good n m w g j)
    (hk : IntegralMixedChronologicalCutCode.Good n m w g k) (Q : ℤ) (hQ : Q≠0) :
    IntegralMixedSweepRetarget.rule ((IntegralMixedChronologicalCutCode.rawData n m w g j hj).rule Q hQ) 0=
      IntegralMixedSweepRetarget.rule ((IntegralMixedChronologicalCutCode.rawData n m w g k hk).rule Q hQ) 0 :=by
  rfl

private theorem raw_shape_heq {n a m b : ℕ} (hn : n=a) (hm : m=b)
    (w v : List Bool) (hw : w=v) (g h j k : ℕ) (hg : g=h)
    (hj : IntegralMixedChronologicalCutCode.Good n m w g j)
    (hk : IntegralMixedChronologicalCutCode.Good a b v h k)
    (Q R : ℤ) (hQ : Q≠0) (hR : R≠0) (he : Q=R) :
    HEq (IntegralMixedSweepRetarget.rule ((IntegralMixedChronologicalCutCode.rawData n m w g j hj).rule Q hQ) 0)
      (IntegralMixedSweepRetarget.rule ((IntegralMixedChronologicalCutCode.rawData a b v h k hk).rule R hR) 0) :=by
  cases hn
  cases hm
  cases hw
  cases hg
  subst R
  exact heq_of_eq (raw_shape w g j k hj hk Q hQ)

local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  parentKey parent terminal creating parentBirth root context

theorem parent_coordinate_snapshot_eq (q a b :List Bool)
    (hv :FormulaSignSlotRadialProviderAtomic.Valid q) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey false (pair q a)))=
      IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey false (pair q b))):=by
  have HVa:FormulaSignSlotRadialProviderAtomic.Valid (atomic (pair q a)):=by
    simpa only [atomic,pairFst_pair] using hv
  have HVb:FormulaSignSlotRadialProviderAtomic.Valid (atomic (pair q b)):=by
    simpa only [atomic,pairFst_pair] using hv
  have HA:=probe_snapshot_original false (pair q a) HVa
  have HB:=probe_snapshot_original false (pair q b) HVb
  have HS:FormulaSignSlotRadialProviderRecordPrefix.snapshot
      (FormulaSignSlotRadialProviderAtomic.root (atomic (pair q a)))
      (probeStart (pair q a)) (probe_start_fit (pair q a))=
    FormulaSignSlotRadialProviderRecordPrefix.snapshot
      (FormulaSignSlotRadialProviderAtomic.root (atomic (pair q b)))
      (probeStart (pair q b)) (probe_start_fit (pair q b)):=by
    simp only [probeStart,oldPacket,atomic,pairFst_pair]
  exact HA.trans (HS.trans HB.symm)

theorem ordinary_coordinate_shape (q a b : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hA : FormulaSignSlotRadialProviderProperRowWitness.RowGood (pair q a))
    (hB : FormulaSignSlotRadialProviderProperRowWitness.RowGood (pair q b)) :
    HEq (IntegralMixedSweepRetarget.rule ((G).rule (parentKey false (pair q a))) 0)
      (IntegralMixedSweepRetarget.rule ((G).rule (parentKey false (pair q b))) 0) :=by
  have HVa : FormulaSignSlotRadialProviderAtomic.Valid (atomic (pair q a)):=by
    simpa only [atomic,pairFst_pair] using hv
  have HVb : FormulaSignSlotRadialProviderAtomic.Valid (atomic (pair q b)):=by
    simpa only [atomic,pairFst_pair] using hv
  have HC:=row_count_positive _ HVa
  have HD:=row_count_positive _ HVb
  have HA:=parent_good false _ HC hA
  have HB:=parent_good false _ HD hB
  have HE:=parent_coordinate_snapshot_eq q a b hv
  have HN : parentDimension false (pair q a)=parentDimension false (pair q b):=by
    rw [parentDimension_eq,parentDimension_eq]
    simp only [dimension,atomic,pairFst_pair]
  have HM : parentBirth false (pair q a)=parentBirth false (pair q b):=by
    rw [parentBirth_eq false _ HC,parentBirth_eq false _ HD]
    unfold creating
    simp only [initial,oldPacket,atomic,pairFst_pair]
  have HQ : commonDenominator ((G).state (parentKey false (pair q a)))=
      commonDenominator ((G).state (parentKey false (pair q b))):=by
    simpa only [IntegralMixedPrefixSnapshot.ofState] using
      congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>commonDenominator d.state) HE
  have HW : labels (pair q a)=labels (pair q b):=by simp only [labels,atomic,pairFst_pair]
  have HO : offset (pair q a)=offset (pair q b):=by simp only [offset,atomic,pairFst_pair]
  have HRaw:=raw_shape_heq HN HM (labels (pair q a)) (labels (pair q b)) HW
    (offset (pair q a)) (offset (pair q b)) (coordinate (pair q a)) (coordinate (pair q b)) HO HA.1 HB.1
    (commonDenominator ((G).state (parentKey false (pair q a))))
    (commonDenominator ((G).state (parentKey false (pair q b))))
    (commonDenominator_ne_zero ((G).state (parentKey false (pair q a))))
    (commonDenominator_ne_zero ((G).state (parentKey false (pair q b)))) HQ
  rw [rule_at_parent false _ HC hA,rule_at_parent false _ HD hB]
  simpa only [parentData,Bool.false_eq_true,ite_false] using HRaw


end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
