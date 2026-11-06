/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbePrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadComplete
public import LeanCanny.Algebra.IntegralMixedSelectedBadMembership
/-! # Original-prefix bad roots are exactly the actual ordinary row bad roots -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFramedHistoryFamilyBits (family Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem raw_bad_iff {n S W m :ℕ} {Q :SpatialSource n} {ι :Type}
    (x :State Q S W m ι) (hm :m≤S) (hc :Canonical x) (labels :List Bool) (g j :ℕ)
    (hg :g=WordListRecords.count labels+1)
    (H :IntegralMixedChronologicalCutCode.Good n m labels g j)
    (r :Rule n) (hr :r=(IntegralMixedChronologicalCutCode.rawData n m labels g j H).rule
      (commonDenominator x) (commonDenominator_ne_zero x))
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (v :ℕ→ℝ)
    (hφ :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=v i.val)
    (c :IntegralMixedRelativeCuts.Choices x hm r φ) (a :ℝ) :
    a∈(IntegralMixedPrefixSnapshot.ofState x).bad labels v ↔
      a∈IntegralMixedSelectedCriticalCuts.bad x hm r φ c:=by
  subst g;subst r
  exact (IntegralMixedPrefixSnapshot.ofState_mem_bad_iff x hm hc labels j H φ v hφ a).trans
    (IntegralMixedSelectedBadMembership.mem_bad_iff x hm _ φ c a).symm

private theorem family_raw_rule (p :Parameters) (d :Plan p)
    (h :IntegralMixedFramedHistoryFamilyBits.Data p d) (k labels :List Bool) (g j b :ℕ)
    (hg :IntegralMixedChronologicalCutCode.Good (p.ambient (pairFst k)) b labels g j)
    (hb :b=(family p d h).birth k)
    (hr :(family p d h).rule k=(IntegralMixedChronologicalCutCode.rawData
      (p.ambient (pairFst k)) b labels g j hg).rule
        (commonDenominator ((family p d h).state k)) (commonDenominator_ne_zero ((family p d h).state k))) :
    ∃HG :IntegralMixedChronologicalCutCode.Good ((family p d h).ambient k) ((family p d h).birth k) labels g j,
      (family p d h).rule k=(IntegralMixedChronologicalCutCode.rawData
        ((family p d h).ambient k) ((family p d h).birth k) labels g j HG).rule
          (commonDenominator ((family p d h).state k)) (commonDenominator_ne_zero ((family p d h).state k)):=by
  cases hb
  exact ⟨hg,hr⟩

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderBadProbeParent.snapshot
  FormulaSignSlotRadialProviderBadProbeParent.values FormulaSignSlotRadialProviderBadProbeParent.bad
  FormulaSignSlotRadialProviderAtomic.field FormulaSignSlotRadialProviderRecordPrefix.observation

theorem parent_original_bad_snapshot (z :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey false z))=
      FormulaSignSlotRadialProviderBadProbeParent.snapshot (FormulaSignSlotRadialProviderAtomic.root (atomic z)):=by
  have HS:=probe_snapshot_original false z hv
  simpa only [FormulaSignSlotRadialProviderBadProbeParent.snapshot,probeStart,probe_old_count z] using HS

private theorem parent_original_values (z :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (i :ℕ) (hi :i<(G).birth (parentKey false z)) :
    originalValue (atomic z) hv ((G).birth (parentKey false z)-1-i)=
      FormulaSignSlotRadialProviderBadProbeParent.values (FormulaSignSlotRadialProviderAtomic.root (atomic z))
        (FormulaSignSlotRadialProviderAtomic.word (atomic z)) (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv) i:=by
  let q:=atomic z
  have HB:=parent_birth_actual false z hv
  have HS:=parent_original_bad_snapshot z hv
  have HC:=congrArg IntegralMixedPrefixSnapshot.Data.birth HS
  have HClock:((G).birth (parentKey false z))=
      FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)+
        (IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q)-1):=
    HC.trans (FormulaSignSlotRadialProviderBadProbeParent.birth (FormulaSignSlotRadialProviderAtomic.root q))
  have HCount:=probe_original_field_count z hv
  have HField:=FormulaSignSlotRadialProviderFieldEquality.count_eq (FormulaSignSlotRadialProviderAtomic.context q)
  have HFull:FormulaSignSlotRadialProviderRecordPlan.fullCount (FormulaSignSlotRadialProviderAtomic.root q)=creating z+1:=by
    simpa only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair] using HField.symm.trans HCount
  have HL:=originalValue_field q hv ((G).birth (parentKey false z)-1-i) (by omega)
  have HV:=FormulaSignSlotRadialProviderBadProbeParent.value_field
    (FormulaSignSlotRadialProviderAtomic.root q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) i (hi.trans_eq HC)
  have HVF:FormulaSignSlotRadialProviderBadProbeParent.values (FormulaSignSlotRadialProviderAtomic.root q)
      (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) i=
      FormulaSignSlotRadialProviderAtomic.field q hv
        (FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)+
          (IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q)-1)-1-i):=by
    simpa only [FormulaSignSlotRadialProviderAtomic.field,FormulaSignSlotRadialProviderAtomic.context,
      FormulaSignSlotRadialProviderRecordPrefix.context] using HV
  exact HL.trans ((congrArg (FormulaSignSlotRadialProviderAtomic.field q hv)
    (congrArg (fun m=>m-1-i) HClock)).trans HVF.symm)

theorem ordinary_bad_iff_original (z :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hr :FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (φ :((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :QuotientsAt G (parentKey false z) φ (originalValue (atomic z) hv))
    (c :IntegralMixedRelativeCuts.Choices ((G).state (parentKey false z)) ((G).birth_bound _)
      ((G).rule (parentKey false z)) φ) (a :ℝ) :
    a∈FormulaSignSlotRadialProviderBadProbeParent.bad (FormulaSignSlotRadialProviderAtomic.root (atomic z))
      (FormulaSignSlotRadialProviderAtomic.word (atomic z)) (labels z)
      (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv) ↔
    a∈IntegralMixedSelectedCriticalCuts.bad ((G).state (parentKey false z)) ((G).birth_bound _)
      ((G).rule (parentKey false z)) φ c:=by
  have HC:=row_count_positive z hv
  have HG:=(parent_good false z HC hr).1
  have HR:=rule_at_parent false z HC hr
  simp only [parentData,Bool.false_eq_true,ite_false] at HR
  obtain ⟨HF,HRule⟩:=family_raw_rule P D H (parentKey false z) (labels z) (offset z) (coordinate z)
    (parentBirth false z) HG ((parentBirth_eq false z HC).trans (parent_birth_actual false z hv).symm) HR
  have HBad:=raw_bad_iff ((G).state (parentKey false z)) ((G).birth_bound _)
    (parent_canonical false z HC) (labels z) (offset z) (coordinate z) (offset_count z) HF
    ((G).rule (parentKey false z)) HRule φ
    (fun i=>originalValue (atomic z) hv ((G).birth (parentKey false z)-1-i)) hφ c a
  have HE:=IntegralMixedPrefixSnapshot.Data.bad_transport _ _ (parent_original_bad_snapshot z hv)
    (labels z) (fun i=>originalValue (atomic z) hv ((G).birth (parentKey false z)-1-i))
    (FormulaSignSlotRadialProviderBadProbeParent.values (FormulaSignSlotRadialProviderAtomic.root (atomic z))
      (FormulaSignSlotRadialProviderAtomic.word (atomic z)) (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv))
    (parent_original_values z hv)
  unfold FormulaSignSlotRadialProviderBadProbeParent.bad
  rw [←HE]
  exact HBad

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
