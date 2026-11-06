/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNearNative
public import LeanCanny.Encoding.IntegralFramedPhysicalNearWord
/-! # Actual ordinary provider tests recognize selected-polynomial Near

Both anchors and the selected value come from the SAME own prepared full word.
The real interpreting hom is constructed internally from that word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem exists_iff_of_unique {α : Type*} {X : Prop} {PP QQ : α→Prop}
    (h : ∃a,PP a∧(X↔QQ a)) (hu : ∀a b,PP a→PP b→a=b) :
    X↔∃a,PP a∧QQ a :=by
  obtain ⟨a,ha,H⟩:=h
  constructor
  · exact fun hx=>⟨a,ha,H.mp hx⟩
  · rintro ⟨b,hb,Hb⟩
    have HE:=hu b a hb ha
    subst b
    exact H.mpr Hb

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "hf"=>FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive
local notation "hd"=>FormulaSignSlotRadialProviderAtomic.Cuts.fallback
local notation "S"=>IntegralFramedPhysicalSquare.input P D H L F C hs (terminal false) (positive false)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family parent terminal

noncomputable def OrdinaryMetadata (z : List Bool) := ∀right : Bool,
  IntegralFramedPhysicalNear.Metadata P D H (parent false) (terminal false)
    (centerIndex right) (pointIndex false false) z

noncomputable def ordinaryAnchor (z w : List Bool) (hm : OrdinaryMetadata z)
    (hv : SquareSampleCompleteVertices.Valid S z w) (right : Bool) : ℝ :=
  IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal false z))
    (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs (terminal false) (positive false) z w hv)
    ⟨centerIndex right z,(hm right).2.2.2.1⟩

variable (z w code : List Bool)
local notation "oldKey"=>IntegralMixedVirtualTaskBits.saved P (parent false z)
local notation "x"=>IntegralMixedCutSource.Family.state G oldKey
local notation "r"=>IntegralMixedCutSource.Family.rule G oldKey
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G oldKey
  (get P Field.slot13 (parent false z))

noncomputable def NearAt (right : Bool) (hm : OrdinaryMetadata z)
    (hv : SquareSampleCompleteVertices.Valid S z w) : Prop :=
  ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs (terminal false) (positive false) z w hv
        (UniformIntegralPowerSchedule.embed (hm right).2.1 i)^
        UniformIntegralPowerSchedule.weights ((G).cap oldKey) (2^(G).width oldKey) ((G).birth oldKey) i) ∧
    LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint.Near x ((G).birth_bound oldKey) r φ
      (ordinaryAnchor z w hm hv false) (ordinaryAnchor z w hm hv true)
      (if right then ordinaryAnchor z w hm hv true else ordinaryAnchor z w hm hv false) j
      (Nat.fromBitsLE code)
      (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (terminal false z))
        (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs (terminal false) (positive false) z w hv)
        ⟨pointIndex false false z,(hm right).2.2.2.2⟩)

attribute [local irreducible] NearAt

theorem nearLanguage_iff (right : Bool) (hm : OrdinaryMetadata z)
    (hv : SquareSampleCompleteVertices.Valid S z w)
    (hab : ordinaryAnchor z w hm hv false<ordinaryAnchor z w hm hv true) :
    pair (pair z w) code∈nearLanguage right ↔ NearAt z w code right hm hv :=by
  have HA : IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P D H (terminal false z))
      (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs (terminal false) (positive false) z w hv)
      ⟨centerIndex right z,(hm right).2.2.2.1⟩=
        if right then ordinaryAnchor z w hm hv true else ordinaryAnchor z w hm hv false:=by
    cases right <;> rfl
  have HNear:=IntegralFramedPhysicalNear.exists_near_iff P D H L F C hs
    (parent false) (terminal false) (centerIndex right) (pointIndex false false) (positive false)
    hf hd right z w hv (hm right).1 (hm right).2.1 (hm right).2.2.1
    (hm right).2.2.2.1 (hm right).2.2.2.2
    (a:=ordinaryAnchor z w hm hv false) (b:=ordinaryAnchor z w hm hv true) hab HA (Nat.fromBitsLE code)
  have HG:=IntegralFramedPhysicalNear.guarded_packet P D H L F C hs
    (parent false) (terminal false) (centerIndex right) (pointIndex false false) (positive false)
    hf hd right z w code (hm right) hv
  have HW:=IntegralFramedPhysicalNear.accept_rank_word P D H L F C hs
    (parent false) (terminal false) (centerIndex right) (pointIndex false false) (positive false)
    hf hd right z w code
  have HX:=exists_iff_of_unique HNear (by
    intro φ ψ hφ hψ
    apply (x).sampler.scalarPrefix.basis.algHom_ext
    intro i
    exact (hφ i).trans (hψ i).symm)
  simpa only [NearAt,nearLanguage] using HG.trans (HW.trans HX)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
