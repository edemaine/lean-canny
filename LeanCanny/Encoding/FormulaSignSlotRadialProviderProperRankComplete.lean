/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeMetadata
/-! # A field-matched mean probe accepts the ordinary midpoint root rank -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
local notation "hf"=>FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive
local notation "hd"=>FormulaSignSlotRadialProviderAtomic.Cuts.fallback
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  parent terminal creating originalValue IntegralFramedZeroTarskiStatistic.value
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedCanonicalBankPoint.point IntegralFramedPhysicalSquare.scalarTuple IntegralMixedCriticalSweep.selected

variable (u : List Bool)
local notation "z"=>FormulaSignSlotRadialProviderProperRowWitness.key u
local notation "old"=>parentKey false z
local notation "meanOld"=>parentKey true z
local notation "x"=>IntegralMixedCutSource.Family.state G old
local notation "r"=>IntegralMixedCutSource.Family.rule G old
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent false z))

private theorem reverse_indices (a b i k : ℕ) (hab : a=b) (hik : i=k) : a-1-i=b-1-k:=by omega
private theorem reverse_reference (a b p i : ℕ) (hab : a=b) (hp : p<b) (hi : i=b-1-p) : a-1-i=p:=by omega

private theorem probe_mean_roots
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HR : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : ((G).state meanOld).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv ((G).birth old-1-i.val))
    (Hψ : ∀i,ψ (((G).state meanOld).bank.numerator i)/(((G).state meanOld).bank.denominator i:ℝ)=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv ((G).birth meanOld-1-i.val)) :
    ((selected ((G).state meanOld) ((G).birth_bound _) ((G).rule meanOld)
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G meanOld (get P Field.slot13 (parent true z))) ψ).map (evalRingHom 0)).roots=
    ((selected x ((G).birth_bound old) r j φ).map (evalRingHom
      ((originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z)+
        originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z))/2))).roots :=by
  have HC:=row_count_positive z hv
  have HBO:=parent_birth_actual false z hv
  have HBM:=parent_birth_actual true z hv
  have HA : ∀(i : Fin ((G).birth old)) (k : Fin ((G).birth meanOld)),i.val=k.val→
      φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
        ψ (((G).state meanOld).bank.numerator k)/(((G).state meanOld).bank.denominator k:ℝ):=by
    intro i k hik
    have HI:=reverse_indices _ _ i.val k.val (HBO.trans HBM.symm) hik
    exact (Hφ i).trans ((congrArg (originalValue
      (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv) HI).trans (Hψ k).symm)
  have HRef (side : Bool) :
      φ ((x).bank.numerator (actualMeanReference side z hv HR))/
        ((x).bank.denominator (actualMeanReference side z hv HR):ℝ)=
        originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer side z):=by
    have HP : oldProducer side z<creating z:=by
      cases side
      · exact HR.2.2.1
      · exact HR.2.2.2.1
    have HRef : (actualMeanReference side z hv HR).val=
        creating z-1-oldProducer side z:=by
      simp only [actualMeanReference,meanReference,IntegralMixedChronologicalMidpoint.reference,Fin.val_mk,
        parentBirth_eq false z HC]
    have HI:=reverse_reference _ _ _ _ HBO HP HRef
    exact (Hφ (actualMeanReference side z hv HR)).trans
      (congrArg (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv) HI)
  let jm:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G meanOld (get P Field.slot13 (parent true z))
  have HJ : (j).val=jm.val:=(selected_coordinate false z hv HR).trans
    (selected_coordinate true z hv HR).symm
  have HRoots:=(actual_mean_roots z hv HR) φ ψ HA j jm HJ
  rw [HRef false,HRef true] at HRoots
  exact HRoots

theorem probe_rank_of_semantics
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HR : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (HF : FormulaSignSlotRadialProviderProperRowWitness.fieldMatch true u∈
      FormulaSignSlotRadialProviderFieldEqualityList.language)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal true) (positive true)) z
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u))
    (hmid : pointProducer true z<creating z)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv ((G).birth old-1-i.val))
    (HM : originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (pointProducer true z)∈
      IntegralMixedFrozenFrameSectionCode.roots x ((G).birth_bound old) r φ
        ((originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z)+
          originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z))/2) j)
    (HCode : Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u)=
      IntegralMixedSelectedRootRank.rank x ((G).birth_bound old) r φ
        ((originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z)+
          originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z))/2) j
        (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (pointProducer true z))) :
    FormulaSignSlotRadialProviderProperRowWitness.query true u∈rankLanguage :=by
  have HMeta : IntegralFramedPhysicalNear.Metadata P BP BH (parent true) (terminal true)
      (pointIndex true true) (pointIndex true true) z:=by
    have H:=probe_metadata true z hv HR _ _ hmid hmid
    exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2⟩
  have HFIT : (G).birth meanOld≤(G).birth (terminal true z):=HMeta.2.1
  have HBackend:=IntegralFramedZeroTarskiStatistic.exists_rankPacket_iff P BP BH BL BF BC BS
    (parent true) (terminal true) (pointIndex true true)
    (positive true) hf hd z (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u)
    (FormulaSignSlotRadialProviderProperRowWitness.rank u) hw HMeta.1 HMeta.2.1 HMeta.2.2.1 HMeta.2.2.2.2
  obtain ⟨ψ,hψ,HK⟩:=HBackend
  have Hψ:=probe_parent_values true u hv HF hw HFIT ψ hψ
  have HRoots:=probe_mean_roots u hv HR φ ψ Hφ Hψ
  simp only [parentKey] at HRoots
  have HS : IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal true z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal true)
        (positive true) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u) hw)
      ⟨pointIndex true true z,HMeta.2.2.2.2⟩=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (pointProducer true z):=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    exact probe_scalar_value true u hv HF hw _ hmid (by
      change creating z≤count true z
      rw [probe_terminal_count true z hv]
      omega)
  have HAccept:=HK.mpr (by
    dsimp only
    rw [HS,HRoots]
    constructor
    · exact HM
    · simpa only [IntegralMixedSelectedRootRank.rank,IntegralMixedFrozenFrameSectionCode.roots,
        IntegralMixedFrozenFrameSectionCode.polynomial,OrderedRealRootWindow.rank,parentKey] using HCode.symm)
  have HPacket : rankPacket (FormulaSignSlotRadialProviderProperRowWitness.query true u)=
      IntegralFramedZeroTarskiStatistic.rankPacket P BP BH BL BF BC BS (parent true) (terminal true)
        (pointIndex true true) (positive true) hf hd z
          (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u) (FormulaSignSlotRadialProviderProperRowWitness.rank u):=by
    simp only [FormulaSignSlotRadialProviderProperRowWitness.query,rankPacket,zeroStatistic,IntegralFramedPhysicalNear.reset,
      pairFst_pair,pairSnd_pair,IntegralFramedZeroTarskiStatistic.rankPacket]
  have HK' : RankAccept (FormulaSignSlotRadialProviderProperRowWitness.query true u):=by
    unfold RankAccept
    rw [HPacket]
    exact HAccept
  simpa only [FormulaSignSlotRadialProviderProperRowWitness.query,rankLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using
    (show IntegralFramedPhysicalNear.Metadata P BP BH (parent true) (terminal true)
        (pointIndex true true) (pointIndex true true) z ∧
      SquareSampleCompleteVertices.Valid (Input (terminal true) (positive true)) z
        (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u) ∧RankAccept (FormulaSignSlotRadialProviderProperRowWitness.query true u)
      from ⟨HMeta,hw,HK'⟩)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
