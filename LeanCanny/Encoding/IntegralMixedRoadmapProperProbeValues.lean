/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProbeMetadata
/-! # Fresh coordinate-probe words recover the original retained values -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank parent terminal creating context
  IntegralFramedPhysicalSquare.point IntegralMixedPhysicalFieldEquality.point
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedMarkedPrefixFieldReadback.parentPoint

private theorem point_fin_congr (Q : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan Q)
    (A : IntegralMixedFramedHistoryFamilyBits.Data Q E) (L F C : List Bool→ℕ)
    (h : IntegralMixedFramedStepHeight.FamilyInputs Q E L F C) (key : List Bool→List Bool)
    (hp hq : ∀z,0<(IntegralMixedFramedHistoryFamilyBits.family Q E A).birth (key z)) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E A L F C h key hp) z w)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E A L F C h key hq) z w)
    (i j : Fin ((IntegralMixedFramedHistoryFamilyBits.family Q E A).birth (key z))) (he : i.val=j.val) :
    IntegralFramedPhysicalSquare.point Q E A L F C h key hp z w hv i=
      IntegralFramedPhysicalSquare.point Q E A L F C h key hq z w hw j :=by
  have H : hp=hq:=Subsingleton.elim _ _
  subst hq
  have HI : i=j:=Fin.ext he
  subst j
  rfl

private theorem own_count (mode : Bool) (z : List Bool) :
    (G).birth (terminal hn ht ha hR0 mode z)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((BK).key (context hn ht ha hR0 mode z)) :=by
  unfold terminal
  exact IntegralMixedFramedHistoryFamilyBits.family_birth P BP BH _

theorem probe_own_scalar_value (mode : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 mode) (positive hn ht ha hR0 mode)) z w)
    (p : ℕ) (hp : p<(G).birth (terminal hn ht ha hR0 mode z)) :
    IntegralFramedPhysicalSquare.point P BP BH BL BF BC BS (terminal hn ht ha hR0 mode)
      (positive hn ht ha hR0 mode) z w hv ⟨(G).birth (terminal hn ht ha hR0 mode z)-1-p,by omega⟩=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (context hn ht ha hR0 mode z) w
        ((valid_at_context hn ht ha hR0 mode z w).mp hv) p :=by
  have HV:=(valid_at_context hn ht ha hR0 mode z w).mp hv
  have HF:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0)
    (context hn ht ha hR0 mode z) w HV p (hp.trans_eq (own_count hn ht ha hR0 mode z))
  rw [point_at_context hn ht ha hR0 mode z w hv HV]
  apply Eq.trans ?_ HF.symm
  have HT : terminal hn ht ha hR0 mode z=(BK).key (context hn ht ha hR0 mode z):=by unfold terminal;rfl
  have HC:=own_count hn ht ha hR0 mode z
  convert point_fin_congr P BP BH BL BF BC BS (BK).key (BK).positive
    (IntegralMixedPhysicalPointCompanionScan.full_positive hn ht ha (radius_binary hR0) false)
    (context hn ht ha hR0 mode z) w HV HV
    ⟨(G).birth (terminal hn ht ha hR0 mode z)-1-p,by rw [←HT];omega⟩
    ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength P ((BK).key (context hn ht ha hR0 mode z))-1-p,by
      rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
      have HPP:=hp.trans_eq HC
      omega⟩
    (congrArg (fun a : ℕ=>a-1-p) HC) using 1
  unfold terminal
  rfl

theorem probe_scalar_value (mode : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HF : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 mode u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0))
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 mode) (positive hn ht ha hR0 mode))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord mode u))
    (p : ℕ) (hp : p<creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)) :
    IntegralFramedPhysicalSquare.point P BP BH BL BF BC BS (terminal hn ht ha hR0 mode)
      (positive hn ht ha hR0 mode) (IntegralMixedRoadmapProperRowWitness.key u)
      (IntegralMixedRoadmapProperRowWitness.ownWord mode u) hw
      ⟨(G).birth (terminal hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))-1-p,by
        have HC:=probe_terminal_count hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u) hv
        change (G).birth (terminal hn ht ha hR0 mode _)=_ at HC
        omega⟩=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv p :=by
  obtain ⟨hL,hR,HE⟩:=IntegralMixedRoadmapProperRowWitness.fieldMatch_sound hn ht ha hR0 mode u HF
  have HT:=probe_terminal_count hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u) hv
  change (G).birth (terminal hn ht ha hR0 mode _)=_ at HT
  exact (probe_own_scalar_value hn ht ha hR0 mode _ _ hw p (by omega)).trans (HE p hp).symm

theorem probe_parent_values (mode : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HF : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 mode u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0))
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 mode) (positive hn ht ha hR0 mode))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord mode u))
    (hfit : (G).birth (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))≤
      (G).birth (terminal hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)))
    (φ : ((G).state (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((G).state (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 mode)
        (positive hn ht ha hR0 mode) (IntegralMixedRoadmapProperRowWitness.key u)
        (IntegralMixedRoadmapProperRowWitness.ownWord mode u) hw (UniformIntegralPowerSchedule.embed hfit i)^
          UniformIntegralPowerSchedule.weights ((G).cap (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)))
            (2^(G).width (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)))
            ((G).birth (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))) i) :
    ∀i,φ (((G).state (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))).bank.numerator i)/
      (((G).state (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))).bank.denominator i:ℝ)=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv
        ((G).birth (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))-1-i.val) :=by
  obtain ⟨hL,hR,HE⟩:=IntegralMixedRoadmapProperRowWitness.fieldMatch_sound hn ht ha hR0 mode u HF
  have HC:=row_count_positive hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u) hv
  have HB:=probe_parent_birth hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u) hv
  have HP : IntegralMixedMarkedPrefixFieldReadback.parent n (root hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))=
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    unfold IntegralMixedMarkedPrefixFieldReadback.parent
    rw [root_number hn ht ha hR0,root_count hn ht ha hR0 mode _ HC]
    rw [creating,IntegralMixedRoadmapBadProbePacket.creating]
  have HQ:=statistic_parent_quotients hn ht ha hR0 mode _ _ hv hw hfit φ hφ
  have HBR : (G).birth (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))=
      (IntegralMixedFramedHistoryFamilyBits.commands P BP (parentKey hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))).length:=by
    unfold IntegralMixedFramedHistoryFamilyBits.family;rfl
  intro i
  have HI : i.val<creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=i.isLt.trans_eq HB
  have hR' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedMarkedPrefixFieldReadback.context (root hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralMixedRoadmapProperRowWitness.ownWord mode u):=by
    simpa only [context,IntegralMixedMarkedPrefixFieldReadback.context] using hR
  have HJ : IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
      (root hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)) (IntegralMixedRoadmapProperRowWitness.ownWord mode u) hR' i.val=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (context hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)) (IntegralMixedRoadmapProperRowWitness.ownWord mode u)
        hR (creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)-1-i.val):=by
    simpa only [HP,context,IntegralMixedMarkedPrefixFieldReadback.context] using
      IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
        (root hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u)) _ hR'
        (HC.trans_eq (root_count hn ht ha hR0 mode _ HC).symm) i.val (HI.trans_eq HP.symm)
  have HX:=(HQ ⟨i.val,i.isLt.trans_eq HBR⟩).trans (HJ.trans
    (HE (creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)-1-i.val) (by omega)).symm)
  simp only [originalValue,HB]
  unfold IntegralMixedFramedHistoryFamilyBits.family at i HX ⊢
  cases i
  exact HX

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
