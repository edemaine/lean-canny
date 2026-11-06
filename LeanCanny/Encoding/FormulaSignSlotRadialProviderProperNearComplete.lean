/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeMetadata
/-! # Geometric Near is accepted on a fresh, field-matched probe word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep
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
  parent terminal creating originalValue FormulaSignSlotRadialProviderProperRowWitness.language
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedCanonicalBankPoint.point IntegralFramedPhysicalSquare.scalarTuple
  IntegralMixedSelectedCoordinateEndpoint.Near IntegralMixedCriticalSweep.selected

variable (u : List Bool)
local notation "z"=>FormulaSignSlotRadialProviderProperRowWitness.key u
local notation "old"=>parentKey false z
local notation "x"=>IntegralMixedCutSource.Family.state G old
local notation "r"=>IntegralMixedCutSource.Family.rule G old
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent false z))

private theorem probe_anchor (right : Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HR : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (HF : FormulaSignSlotRadialProviderProperRowWitness.fieldMatch false u∈
      FormulaSignSlotRadialProviderFieldEqualityList.language)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal false) (positive false)) z
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u))
    (hchild : pointProducer false z<creating z)
    (HM : IntegralFramedPhysicalNear.Metadata P BP BH (parent false) (terminal false)
      (centerIndex right) (pointIndex false false) z) :
    (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal false z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal false)
        (positive false) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw)
      ⟨centerIndex right z,HM.2.2.2.1⟩=
      if right then originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z)
      else originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z)) ∧
    IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal false z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal false)
        (positive false) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw)
      ⟨pointIndex false false z,HM.2.2.2.2⟩=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (pointProducer false z) :=by
  have hc : oldProducer right z<creating z:=by
    cases right
    · exact HR.2.2.1
    · exact HR.2.2.2.1
  have HV (p : ℕ) (hp : p<creating z) :
      IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal false z))
        (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal false)
          (positive false) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw)
        ⟨count false z-1-p,by
          change count false z-1-p<count false z
          rw [probe_terminal_count false z hv];omega⟩=
        originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv p:=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    exact probe_scalar_value false u hv HF hw p hp (by
      change creating z≤count false z
      rw [probe_terminal_count false z hv]
      omega)
  have HA : IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P BP BH (terminal false z))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal false)
        (positive false) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw)
      ⟨centerIndex right z,HM.2.2.2.1⟩=
      if right then originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z)
      else originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z):=by
    cases right <;> exact HV _ hc
  exact ⟨HA,HV _ hchild⟩

theorem probe_near_of_semantics (right : Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HR : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (HF : FormulaSignSlotRadialProviderProperRowWitness.fieldMatch false u∈
      FormulaSignSlotRadialProviderFieldEqualityList.language)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal false) (positive false)) z
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u))
    (hchild : pointProducer false z<creating z)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv ((G).birth old-1-i.val))
    (hab : originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z)<
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z))
    (HN : IntegralMixedSelectedCoordinateEndpoint.Near x ((G).birth_bound old) r φ
      (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z))
      (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z))
      (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer right z)) j
      (Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u))
      (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (pointProducer false z))) :
    FormulaSignSlotRadialProviderProperRowWitness.query false u∈nearLanguage right :=by
  have hc : oldProducer right z<creating z:=by
    cases right
    · exact HR.2.2.1
    · exact HR.2.2.2.1
  have HM : IntegralFramedPhysicalNear.Metadata P BP BH (parent false) (terminal false)
      (centerIndex right) (pointIndex false false) z:=by
    have H:=probe_metadata false z hv HR _ _ hc hchild
    exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2⟩
  have HAnchor:=probe_anchor u right hv HR HF hw hchild HM
  have HA:=HAnchor.1
  have HS:=HAnchor.2
  have HFIT : (G).birth old≤(G).birth (terminal false z):=HM.2.1
  have HC:=row_count_positive z hv
  have HBackend:=IntegralFramedPhysicalNear.exists_near_iff P BP BH BL BF BC BS
    (parent false) (terminal false)
    (centerIndex right) (pointIndex false false) (positive false)
    hf hd right z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw HM.1 HM.2.1 HM.2.2.1 HM.2.2.2.1 HM.2.2.2.2
    (a:=originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z))
    (b:=originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z)) hab HA
    (Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u))
  obtain ⟨ψ,hψ,HK⟩:=HBackend
  have Hψ:=probe_parent_values false u hv HF hw HFIT ψ hψ
  have HE : ψ=φ:=IntegralMixedBankValueInterpretation.hom_ext x (parent_canonical false z HC) ψ φ
    (fun i=>(Hψ i).trans (Hφ i).symm)
  subst ψ
  have HNear:=HN
  have HEp : (if right then originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer true z)
      else originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer false z))=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv (oldProducer right z):=by cases right <;> rfl
  have HAccept : pair (pair z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u))
      (BinaryNatCode.encode (Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u)))∈
      IntegralFramedPhysicalNear.Accept P BP BH BL BF BC BS (parent false) (terminal false)
        (centerIndex right) (pointIndex false false) (positive false) hf hd right:=by
    apply HK.mpr
    simpa only [HEp,HS,parentKey] using HNear
  have HW:=(IntegralFramedPhysicalNear.accept_rank_word P BP BH BL BF BC BS
    (parent false) (terminal false)
    (centerIndex right) (pointIndex false false) (positive false) hf hd right
    z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) (FormulaSignSlotRadialProviderProperRowWitness.rank u)).mpr HAccept
  exact (IntegralFramedPhysicalNear.guarded_packet P BP BH BL BF BC BS
    (parent false) (terminal false)
    (centerIndex right) (pointIndex false false) (positive false) hf hd right
    z (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) (FormulaSignSlotRadialProviderProperRowWitness.rank u) HM hw).mpr HW

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
