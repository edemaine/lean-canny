/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProbeValues
/-! # A field-matched mean probe accepts the ordinary midpoint root rank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
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
local notation "hf"=>IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (radius_binary hR0) false
local notation "hd"=>IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  parent terminal creating originalValue IntegralFramedZeroTarskiStatistic.value
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedCanonicalBankPoint.point IntegralFramedPhysicalSquare.scalarTuple IntegralMixedCriticalSweep.selected

variable (u : List Bool)
local notation "z"=>IntegralMixedRoadmapProperRowWitness.key u
local notation "old"=>parentKey hn ht ha hR0 false z
local notation "meanOld"=>parentKey hn ht ha hR0 true z
local notation "x"=>IntegralMixedCutSource.Family.state G old
local notation "r"=>IntegralMixedCutSource.Family.rule G old
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent hn ht ha hR0 false z))

private theorem reverse_indices (a b i k : ℕ) (hab : a=b) (hik : i=k) : a-1-i=b-1-k:=by omega
private theorem reverse_reference (a b p i : ℕ) (hab : a=b) (hp : p<b) (hi : i=b-1-p) : a-1-i=p:=by omega

private theorem probe_mean_roots
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : ((G).state meanOld).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv ((G).birth old-1-i.val))
    (Hψ : ∀i,ψ (((G).state meanOld).bank.numerator i)/(((G).state meanOld).bank.denominator i:ℝ)=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv ((G).birth meanOld-1-i.val)) :
    ((selected ((G).state meanOld) ((G).birth_bound _) ((G).rule meanOld)
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G meanOld (get P Field.slot13 (parent hn ht ha hR0 true z))) ψ).map (evalRingHom 0)).roots=
    ((selected x ((G).birth_bound old) r j φ).map (evalRingHom
      ((originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z)+
        originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z))/2))).roots :=by
  have HC:=row_count_positive hn ht ha hR0 z hv
  have HBO:=probe_parent_birth hn ht ha hR0 false z hv
  have HBM:=probe_parent_birth hn ht ha hR0 true z hv
  have HA : ∀(i : Fin ((G).birth old)) (k : Fin ((G).birth meanOld)),i.val=k.val→
      φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
        ψ (((G).state meanOld).bank.numerator k)/(((G).state meanOld).bank.denominator k:ℝ):=by
    intro i k hik
    have HI:=reverse_indices _ _ i.val k.val (HBO.trans HBM.symm) hik
    exact (Hφ i).trans ((congrArg (originalValue hn ht ha hR0
      (IntegralMixedRoadmapProperRowWitness.atomic u) hv) HI).trans (Hψ k).symm)
  have HRef (side : Bool) :
      φ ((x).bank.numerator (actualMeanReference hn ht ha hR0 side z hv HR))/
        ((x).bank.denominator (actualMeanReference hn ht ha hR0 side z hv HR):ℝ)=
        originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer side z):=by
    have HP : oldProducer side z<creating hn ht ha hR0 z:=by
      cases side
      · exact HR.2.2.1
      · exact HR.2.2.2.1
    have HRef : (actualMeanReference hn ht ha hR0 side z hv HR).val=
        creating hn ht ha hR0 z-1-oldProducer side z:=by
      simp only [actualMeanReference,meanReference,IntegralMixedChronologicalMidpoint.reference,Fin.val_mk,
        parentBirth_eq hn ht ha hR0 false z HC]
    have HI:=reverse_reference _ _ _ _ HBO HP HRef
    exact (Hφ (actualMeanReference hn ht ha hR0 side z hv HR)).trans
      (congrArg (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv) HI)
  let jm:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G meanOld (get P Field.slot13 (parent hn ht ha hR0 true z))
  have HJ : (j).val=jm.val:=(selected_coordinate hn ht ha hR0 false z hv HR).trans
    (selected_coordinate hn ht ha hR0 true z hv HR).symm
  have HRoots:=(actual_mean_roots hn ht ha hR0 z hv HR) φ ψ HA j jm HJ
  rw [HRef false,HRef true] at HRoots
  exact HRoots

theorem probe_rank_of_semantics
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)
    (HF : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 true u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0))
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true)) z
      (IntegralMixedRoadmapProperRowWitness.ownWord true u))
    (hmid : pointProducer hn ht ha hR0 true z<creating hn ht ha hR0 z)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv ((G).birth old-1-i.val))
    (HM : originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (pointProducer hn ht ha hR0 true z)∈
      IntegralMixedFrozenFrameSectionCode.roots x ((G).birth_bound old) r φ
        ((originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z)+
          originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z))/2) j)
    (HCode : Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u)=
      IntegralMixedSelectedRootRank.rank x ((G).birth_bound old) r φ
        ((originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z)+
          originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z))/2) j
        (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (pointProducer hn ht ha hR0 true z))) :
    IntegralMixedRoadmapProperRowWitness.query true u∈rankLanguage hn ht ha hR0 :=by
  have HMeta : IntegralFramedPhysicalNear.Metadata P BP BH (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true)
      (pointIndex hn ht ha hR0 true true) (pointIndex hn ht ha hR0 true true) z:=by
    have H:=probe_metadata hn ht ha hR0 true z hv HR _ _ hmid hmid
    exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2⟩
  have HFIT : (G).birth meanOld≤(G).birth (terminal hn ht ha hR0 true z):=HMeta.2.1
  have HBackend:=IntegralFramedZeroTarskiStatistic.exists_rankPacket_iff P BP BH BL BF BC BS
    (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
    (positive hn ht ha hR0 true) hf hd z (IntegralMixedRoadmapProperRowWitness.ownWord true u)
    (IntegralMixedRoadmapProperRowWitness.rank u) hw HMeta.1 HMeta.2.1 HMeta.2.2.1 HMeta.2.2.2.2
  obtain ⟨ψ,hψ,HK⟩:=HBackend
  have Hψ:=probe_parent_values hn ht ha hR0 true u hv HF hw HFIT ψ hψ
  have HRoots:=probe_mean_roots hn ht ha hR0 u hv HR φ ψ Hφ Hψ
  simp only [parentKey] at HRoots
  have HS : IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 true z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 true)
        (positive hn ht ha hR0 true) z (IntegralMixedRoadmapProperRowWitness.ownWord true u) hw)
      ⟨pointIndex hn ht ha hR0 true true z,HMeta.2.2.2.2⟩=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (pointProducer hn ht ha hR0 true z):=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    exact probe_scalar_value hn ht ha hR0 true u hv HF hw _ hmid
  have HAccept:=HK.mpr (by
    dsimp only
    rw [HS,HRoots]
    constructor
    · exact HM
    · simpa only [IntegralMixedSelectedRootRank.rank,IntegralMixedFrozenFrameSectionCode.roots,
        IntegralMixedFrozenFrameSectionCode.polynomial,OrderedRealRootWindow.rank,parentKey] using HCode.symm)
  have HPacket : rankPacket hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.query true u)=
      IntegralFramedZeroTarskiStatistic.rankPacket P BP BH BL BF BC BS (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true)
        (pointIndex hn ht ha hR0 true true) (positive hn ht ha hR0 true) hf hd z
          (IntegralMixedRoadmapProperRowWitness.ownWord true u) (IntegralMixedRoadmapProperRowWitness.rank u):=by
    simp only [IntegralMixedRoadmapProperRowWitness.query,rankPacket,zeroStatistic,IntegralFramedPhysicalNear.reset,
      pairFst_pair,pairSnd_pair,IntegralFramedZeroTarskiStatistic.rankPacket]
  have HK' : RankAccept hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.query true u):=by
    unfold RankAccept
    rw [HPacket]
    exact HAccept
  simpa only [IntegralMixedRoadmapProperRowWitness.query,rankLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using
    (show IntegralFramedPhysicalNear.Metadata P BP BH (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true)
        (pointIndex hn ht ha hR0 true true) (pointIndex hn ht ha hR0 true true) z ∧
      SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true)) z
        (IntegralMixedRoadmapProperRowWitness.ownWord true u) ∧RankAccept hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.query true u)
      from ⟨HMeta,hw,HK'⟩)

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
