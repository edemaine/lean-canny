/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalCoordinates
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalFreeIndex
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowCoordinateTransport
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixParameters
public import LeanCanny.Connectivity.IntegralMixedSelectedRootRank
/-! # The actual MID point is physical in every coordinate's ordinary query -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def PhysicalReadback (A : IntegralMixedPrefixSnapshot.Data) (hm : A.birth≤ A.horizon)
    (r : Rule A.ambient) (p : Fin (A.ambient+1)→ℝ) (values : ℕ→ℝ) (t : ℝ) : Prop:=
  ∀φ : A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=values (A.birth-1-i.val))→
    p∈IntegralMixedSelectedPhysicalFiber.physical A.state hm r φ t

private theorem physical_readback_transport (A B : IntegralMixedPrefixSnapshot.Data) (he : A=B)
    (hm : A.birth≤ A.horizon) (hl : B.birth≤ B.horizon) (r : Rule A.ambient) (s : Rule B.ambient)
    (hs : HEq (IntegralMixedSweepRetarget.rule r 0) (IntegralMixedSweepRetarget.rule s 0))
    (p : Fin (A.ambient+1)→ℝ) (q : Fin (B.ambient+1)→ℝ) (hp : HEq p q)
    (values : ℕ→ℝ) (t : ℝ) (H : PhysicalReadback A hm r p values t) :
    PhysicalReadback B hl s q values t :=by
  cases he
  have HP : p=q:=eq_of_heq hp
  subst q
  have HS : IntegralMixedSweepRetarget.rule r 0=IntegralMixedSweepRetarget.rule s 0:=eq_of_heq hs
  change PhysicalReadback A hm (IntegralMixedSweepRetarget.rule r 0) p values t at H
  change PhysicalReadback A hl (IntegralMixedSweepRetarget.rule s 0) p values t
  rw [←HS]
  exact H

private theorem cast_point_heq {a b : ℕ} (H : a=b) (p : Fin a→ℝ) :
    HEq p (fun i : Fin b=>p (Fin.cast H.symm i)) :=by cases H;rfl

private theorem family_width (K : IntegralFramedBankQuery.Bank) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family K.parameters K.plan K.data).width key=
      K.parameters.width (pairFst key) :=rfl

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤ n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width
 IntegralMixedRoadmapProperRow.parentKey IntegralMixedRoadmapProperRow.dimension
 IntegralMixedRoadmapProperRow.initial IntegralMixedRoadmapProperRow.creating
 field midpoint IntegralMixedRoadmapProper.midpointPoint

theorem row_ambient_eq (q : List Bool) (j : ℕ) :
    (G).ambient (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))=D q :=by
  simpa only [IntegralMixedRoadmapProperRow.parentDimension,IntegralMixedRoadmapProperRow.dimension,
    IntegralMixedRoadmapProperRow.atomic,pairFst_pair,IntegralMixedFramedHistoryFamilyBits.family] using
    IntegralMixedRoadmapProperRow.parentDimension_eq hn ht ha hR0 false (pair q (BinaryNatCode.encode j))

noncomputable def rowMidpoint (q : List Bool) (j : ℕ) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    Fin ((G).ambient (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))+1)→ℝ:=
  fun i=>IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv
    (Fin.cast (congrArg (·+1) (row_ambient_eq hn ht ha hR0 q j)) i)

private theorem reference_good_of_row (q : List Bool) (j : ℕ)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (pair q (BinaryNatCode.encode j))) :
    IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q) :=by
  have HD:=HB.1
  have HN:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  simp only [IntegralMixedRoadmapProperRowWitness.RowGood,IntegralMixedRoadmapProperRow.dimension,
    IntegralMixedRoadmapProperRow.creating,IntegralMixedRoadmapProperRow.initial,IntegralMixedRoadmapProperRow.oldPacket,
    IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.coordinate,
    IntegralMixedRoadmapProperRow.atomic,IntegralMixedRoadmapProperRow.oldProducer,rowKey,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits] at HR ⊢
  have HF : WordListRecords.count (IntegralMixedRoadmapProper.labels q)+1≤ IntegralMixedRoadmapAtomic.depth q:=by
    rw [IntegralMixedRoadmapProper.labels_count]
    unfold IntegralMixedRoadmapProper.levelIndex
    omega
  exact ⟨⟨HR.1.1,HR.1.2.1,HR.1.2.2.1,HF,by omega⟩,
    ⟨HR.2.1,HR.2.2.1,HR.2.2.2.1,HR.2.2.2.2.1,HR.2.2.2.2.2.1,HF,by omega⟩⟩

theorem row_parent_width (mode : Bool) (z : List Bool) :
    (G).width (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 mode z)=
      IntegralMixedRoadmapAtomic.width hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z) :=by
  have HC : IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapProperRow.root hn ht ha hR0 mode z)=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapAtomic.root (IntegralMixedRoadmapProperRow.atomic z)):=by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapProperRow.root,
      IntegralMixedRoadmapAtomic.root,pairFst_pair]
  have HP : (BK).parameters=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0):=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    rfl
  rw [family_width,IntegralMixedRoadmapProperRow.parentKey_root]
  unfold IntegralMixedRoadmapAtomic.width
  rw [HP]
  exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 _ _ HC

theorem row_midpoint_physical (q : List Bool) (j : ℕ)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (pair q (BinaryNatCode.encode j)))
    (φ : ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))).bank.numerator i)/
      (((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))).bank.denominator i:ℝ)=
      field hn ht ha hR0 q hv ((G).birth (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))-1-i.val)) :
    rowMidpoint hn ht ha hR0 q j hv∈IntegralMixedSelectedPhysicalFiber.physical
      ((G).state (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j))))
      ((G).birth_bound _) ((G).rule (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))) φ
      ((field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
        field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2) :=by
  have HR0:=reference_good_of_row hn ht ha hR0 q j hv HB HR
  have HE:=IntegralMixedRoadmapProperRow.parent_coordinate_snapshot_eq hn ht ha hR0 q
    (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q)) (BinaryNatCode.encode j) hv
  have HS:=IntegralMixedRoadmapProperRow.ordinary_coordinate_shape hn ht ha hR0 q
    (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q)) (BinaryNatCode.encode j) hv HR0 HR
  have HP : HEq (midpoint hn ht ha hR0 q hv) (rowMidpoint hn ht ha hR0 q j hv):=by
    have HA : HEq (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv) (midpoint hn ht ha hR0 q hv):=by
      unfold midpoint
      exact cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 q).symm) _
    have HB' : HEq (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv) (rowMidpoint hn ht ha hR0 q j hv):=by
      unfold rowMidpoint
      exact cast_point_heq (congrArg (·+1) (row_ambient_eq hn ht ha hR0 q j).symm) _
    exact HA.symm.trans HB'
  have HRef : PhysicalReadback (IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey hn ht ha hR0 q)))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) (midpoint hn ht ha hR0 q hv)
      (field hn ht ha hR0 q hv)
      ((field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
        field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2):=by
    intro ψ Hψ
    exact midpoint_physical hn ht ha hR0 q hv HB HR0 ψ Hψ
  have HOut:=physical_readback_transport _ _ HE ((G).birth_bound _) ((G).birth_bound _)
    ((G).rule (oldKey hn ht ha hR0 q)) _ HS _ _ HP (field hn ht ha hR0 q hv) _ HRef
  exact HOut φ Hφ

theorem row_midpoint_free (q : List Bool) (j : ℕ)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (i : Fin ((G).ambient (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))+1))
    (hi : IntegralMixedRoadmapAtomic.depth q≤ i.val) :
    rowMidpoint hn ht ha hR0 q j hv i=
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.midProducer (D q) (N q) q i.val) :=by
  have H:=IntegralMixedRoadmapProper.midpointPoint_free hn ht ha hR0 q hv HB.1 HB.2.2.1
    (Fin.cast (congrArg (·+1) (row_ambient_eq hn ht ha hR0 q j)) i)
    (by have HD:=HB.1;simp only [Fin.val_cast];unfold IntegralMixedRoadmapProper.levelIndex;omega)
  simpa only [rowMidpoint,field,Fin.val_cast] using H

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
