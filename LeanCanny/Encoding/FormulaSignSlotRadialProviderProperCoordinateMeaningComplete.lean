/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateComplete
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateMeaning
/-! # Actual chronological-field coordinate meaning has a bounded native witness -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
private theorem field_value_eq (a b : List Bool) (he : a=b)
    (ha : FormulaSignSlotRadialProviderAtomic.Valid a) (hb : FormulaSignSlotRadialProviderAtomic.Valid b) :
    FormulaSignSlotRadialProviderAtomic.field a ha=FormulaSignSlotRadialProviderAtomic.field b hb:=by cases he;rfl
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family CoordinateAt
  IntegralMixedSelectedCoordinateEndpoint.Near IntegralMixedSelectedRootRank.rank

theorem coordinate_at_of_field (right : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (hh : CoordinateAt right z (FormulaSignSlotRadialProviderAtomic.field (atomic z) hv)) :
    CoordinateAt right z (originalValue (atomic z) hv) :=by
  unfold CoordinateAt QuotientsAt at hh ⊢
  obtain ⟨φ,Hφ,HNear⟩:=hh
  have HB:=parent_birth_actual false z hv
  have HBounds:=row_producer_bounds z hv hd hr
  have HL:=before_probe_field z hv (oldProducer false z) hr.2.2.1
  have HR:=before_probe_field z hv (oldProducer true z) hr.2.2.2.1
  have HS:=before_probe_field z hv (oldProducer right z) (by
    cases right
    · exact hr.2.2.1
    · exact hr.2.2.2.1)
  have HC:=before_probe_field z hv (pointProducer false z) HBounds.1
  have HM:=before_probe_field z hv (pointProducer true z) HBounds.2
  refine ⟨φ,?_,?_⟩
  · intro i
    have HI:=i.isLt
    exact (Hφ i).trans (before_probe_field z hv _ (by omega)).symm
  · simpa only [←HL,←HR,←HS,←HC,←HM] using HNear

theorem holds_of_coordinate_meaning (right : Bool) (q : List Bool) (j : ℕ)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hab : FormulaSignSlotRadialProviderAtomic.field q hv (IntegralMixedRoadmapProper.producer false q)<
      FormulaSignSlotRadialProviderAtomic.field q hv (IntegralMixedRoadmapProper.producer true q))
    (hm : CoordinateMeaning right q j hv) :
    FormulaSignSlotRadialProviderProperCoordinateSearch.Holds right (pair q (BinaryNatCode.encode j)) :=by
  let z:=pair q (BinaryNatCode.encode j)
  have HAtomic : atomic z=q:=pairFst_pair _ _
  have HV : FormulaSignSlotRadialProviderAtomic.Valid (atomic z):=by rw [HAtomic];exact hv
  have HD : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z):=by rw [HAtomic];exact hd
  have HF:=field_value_eq _ _ HAtomic HV hv
  unfold CoordinateMeaning at hm
  obtain ⟨HR,HS,HNear⟩:=hm
  have HField : CoordinateAt right z (FormulaSignSlotRadialProviderAtomic.field (atomic z) HV):=by
    simpa only [HF] using HNear
  have HOriginal:=coordinate_at_of_field right z HV HD HR HField
  have HProducer (side : Bool) : oldProducer side z=IntegralMixedRoadmapProper.producer side q:=
    congrArg (IntegralMixedRoadmapProper.producer side) HAtomic
  have HValue (side : Bool) (hside : oldProducer side z<creating z) :
      originalValue (atomic z) HV (oldProducer side z)=
      FormulaSignSlotRadialProviderAtomic.field q hv (IntegralMixedRoadmapProper.producer side q):=
    (before_probe_field z HV _ hside).trans ((congrFun HF _).trans
      (congrArg (FormulaSignSlotRadialProviderAtomic.field q hv) (HProducer side)))
  have HOrder : originalValue (atomic z) HV (oldProducer false z)<originalValue (atomic z) HV (oldProducer true z):=
    (HValue false HR.2.2.1).trans_lt (hab.trans_eq (HValue true HR.2.2.2.1).symm)
  exact holds_of_coordinate_at right z HV HD HR HS HOrder HOriginal

theorem coordinate_search_iff_meaning (right : Bool) (q : List Bool) (j : ℕ)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hb : FormulaSignSlotRadialProviderProper.Base q)
    (hj : FormulaSignSlotRadialProviderAtomic.depth q≤j) (hjn : j≤FormulaSignSlotRadialProviderAtomic.dimension q) :
    FormulaSignSlotRadialProviderProperCoordinateSearch.Holds right (pair q (BinaryNatCode.encode j)) ↔
      CoordinateMeaning right q j hv :=by
  constructor
  · exact coordinate_meaning right q j hv hb hj hjn
  · exact holds_of_coordinate_meaning right q j hv hb.1
      (FormulaSignSlotRadialProviderProper.order_of_base q hv hb)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
