/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProbeValues
/-! # Geometric Near is accepted on a fresh, field-matched probe word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep
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
  parent terminal creating originalValue IntegralMixedRoadmapProperRowWitness.language
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedCanonicalBankPoint.point IntegralFramedPhysicalSquare.scalarTuple
  IntegralMixedSelectedCoordinateEndpoint.Near IntegralMixedCriticalSweep.selected

variable (u : List Bool)
local notation "z"=>IntegralMixedRoadmapProperRowWitness.key u
local notation "old"=>parentKey hn ht ha hR0 false z
local notation "x"=>IntegralMixedCutSource.Family.state G old
local notation "r"=>IntegralMixedCutSource.Family.rule G old
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent hn ht ha hR0 false z))

private theorem probe_anchor (right : Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)
    (HF : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 false u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0))
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false)) z
      (IntegralMixedRoadmapProperRowWitness.ownWord false u))
    (hchild : pointProducer hn ht ha hR0 false z<creating hn ht ha hR0 z)
    (HM : IntegralFramedPhysicalNear.Metadata P BP BH (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
      (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) z) :
    (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 false z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 false)
        (positive hn ht ha hR0 false) z (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw)
      ⟨centerIndex hn ht ha hR0 right z,HM.2.2.2.1⟩=
      if right then originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z)
      else originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z)) ∧
    IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 false z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 false)
        (positive hn ht ha hR0 false) z (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw)
      ⟨pointIndex hn ht ha hR0 false false z,HM.2.2.2.2⟩=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (pointProducer hn ht ha hR0 false z) :=by
  have hc : oldProducer right z<creating hn ht ha hR0 z:=by
    cases right
    · exact HR.2.2.1
    · exact HR.2.2.2.1
  have HV (p : ℕ) (hp : p<creating hn ht ha hR0 z) :
      IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 false z))
        (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 false)
          (positive hn ht ha hR0 false) z (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw)
        ⟨count hn ht ha hR0 false z-1-p,by
          change count hn ht ha hR0 false z-1-p<count hn ht ha hR0 false z
          rw [probe_terminal_count hn ht ha hR0 false z hv];omega⟩=
        originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv p:=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    exact probe_scalar_value hn ht ha hR0 false u hv HF hw p hp
  have HA : IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 false z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 false)
        (positive hn ht ha hR0 false) z (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw)
      ⟨centerIndex hn ht ha hR0 right z,HM.2.2.2.1⟩=
      if right then originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z)
      else originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z):=by
    cases right <;> exact HV _ hc
  exact ⟨HA,HV _ hchild⟩

theorem probe_near_of_semantics (right : Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)
    (HF : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 false u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0))
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false)) z
      (IntegralMixedRoadmapProperRowWitness.ownWord false u))
    (hchild : pointProducer hn ht ha hR0 false z<creating hn ht ha hR0 z)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv ((G).birth old-1-i.val))
    (hab : originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z)<
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z))
    (HN : IntegralMixedSelectedCoordinateEndpoint.Near x ((G).birth_bound old) r φ
      (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z))
      (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z))
      (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer right z)) j
      (Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u))
      (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (pointProducer hn ht ha hR0 false z))) :
    IntegralMixedRoadmapProperRowWitness.query false u∈nearLanguage hn ht ha hR0 right :=by
  have hc : oldProducer right z<creating hn ht ha hR0 z:=by
    cases right
    · exact HR.2.2.1
    · exact HR.2.2.2.1
  have HM : IntegralFramedPhysicalNear.Metadata P BP BH (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
      (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) z:=by
    have H:=probe_metadata hn ht ha hR0 false z hv HR _ _ hc hchild
    exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2⟩
  have HAnchor:=probe_anchor hn ht ha hR0 u right hv HR HF hw hchild HM
  have HA:=HAnchor.1
  have HS:=HAnchor.2
  have HFIT : (G).birth old≤(G).birth (terminal hn ht ha hR0 false z):=HM.2.1
  have HC:=row_count_positive hn ht ha hR0 z hv
  have HBackend:=IntegralFramedPhysicalNear.exists_near_iff P BP BH BL BF BC BS
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false)
    hf hd right z (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw HM.1 HM.2.1 HM.2.2.1 HM.2.2.2.1 HM.2.2.2.2
    (a:=originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z))
    (b:=originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z)) hab HA
    (Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u))
  obtain ⟨ψ,hψ,HK⟩:=HBackend
  have Hψ:=probe_parent_values hn ht ha hR0 false u hv HF hw HFIT ψ hψ
  have HE : ψ=φ:=IntegralMixedBankValueInterpretation.hom_ext x (parent_canonical hn ht ha hR0 false z HC) ψ φ
    (fun i=>(Hψ i).trans (Hφ i).symm)
  subst ψ
  have HNear:=HN
  have HEp : (if right then originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer true z)
      else originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer false z))=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv (oldProducer right z):=by cases right <;> rfl
  have HAccept : pair (pair z (IntegralMixedRoadmapProperRowWitness.ownWord false u))
      (BinaryNatCode.encode (Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u)))∈
      IntegralFramedPhysicalNear.Accept P BP BH BL BF BC BS (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
        (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false) hf hd right:=by
    apply HK.mpr
    simpa only [HEp,HS,parentKey] using HNear
  have HW:=(IntegralFramedPhysicalNear.accept_rank_word P BP BH BL BF BC BS
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false) hf hd right
    z (IntegralMixedRoadmapProperRowWitness.ownWord false u) (IntegralMixedRoadmapProperRowWitness.rank u)).mpr HAccept
  exact (IntegralFramedPhysicalNear.guarded_packet P BP BH BL BF BC BS
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false) hf hd right
    z (IntegralMixedRoadmapProperRowWitness.ownWord false u) (IntegralMixedRoadmapProperRowWitness.rank u) HM hw).mpr HW

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
