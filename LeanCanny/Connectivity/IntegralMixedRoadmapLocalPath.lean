/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSelected
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowCoordinateTransport
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalCoordinates
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBadSound
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
public import LeanCanny.Geometry.IntegralMixedSelectedNearTransport
/-! # Native coordinate guards give a path from the child to its physical MID -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem original_quotient_agreement (A B : IntegralMixedPrefixSnapshot.Data) (he : A=B)
    (values : ℕ→ℝ) (φ : A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : B.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=values (A.birth-1-i.val))
    (Hψ : ∀i,ψ (B.state.bank.numerator i)/(B.state.bank.denominator i:ℝ)=values (B.birth-1-i.val)) :
    ∀(i : Fin A.birth) (j : Fin B.birth),i.val=j.val→
      φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=
      ψ (B.state.bank.numerator j)/(B.state.bank.denominator j:ℝ) :=by
  have HB:=congrArg IntegralMixedPrefixSnapshot.Data.birth he
  intro i j hij
  rw [Hφ i,Hψ j]
  exact congrArg values (by omega)

private theorem side_good_pair (right : Bool) (q w : List Bool)
    (H : IntegralMixedRoadmapProperRowWitness.SideGood right (pair q w)) :
    IntegralMixedRoadmapChain.sideWord (IntegralMixedRoadmapAtomic.payload q)
      (IntegralMixedRoadmapProper.levelIndex q)=if right then [true] else [] :=by
  simpa only [IntegralMixedRoadmapProperRowWitness.SideGood,
    IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using H

private theorem side_value (right : Bool) (w : List Bool) (values : Bool→ℝ)
    (H : w=if right then [true] else []) :
    (if w=[true] then values true else values false)=values right :=by
  rw [H]
  cases right <;> simp

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
 (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
 IntegralMixedRoadmapProper.labels field midpoint child
 IntegralMixedRoadmapProperRow.parentKey IntegralMixedRoadmapProperRow.parent
 IntegralMixedRoadmapProperRow.root IntegralMixedRoadmapProperRow.creating

private theorem coordinates_near (right : Bool) (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HAll : IntegralMixedRoadmapLocalEdge.allCoordinates hn ht ha hR0 right q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val)) :
    ∀i : Free ((G).rule (oldKey hn ht ha hR0 q)),
      IntegralMixedSelectedCoordinateEndpoint.Near ((G).state (oldKey hn ht ha hR0 q))
        ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ
        (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
        (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))
        (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer right q)) i
        (IntegralMixedSelectedRootRank.rank ((G).state (oldKey hn ht ha hR0 q)) ((G).birth_bound _)
          ((G).rule (oldKey hn ht ha hR0 q)) φ
          ((field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
            field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2) i
          (midpoint hn ht ha hR0 q hv (ClearedCoordinateCritical.freeIndex
            ((G).rule (oldKey hn ht ha hR0 q)).critical.offset.val
            (fit ((G).rule (oldKey hn ht ha hR0 q))).le i)))
        (child hn ht ha hR0 q hv (ClearedCoordinateCritical.freeIndex
          ((G).rule (oldKey hn ht ha hR0 q)).critical.offset.val
          (fit ((G).rule (oldKey hn ht ha hR0 q))).le i)) :=by
  intro i
  let j:=IntegralMixedRoadmapAtomic.depth q+i.val
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HO0:=IntegralMixedRoadmapProperRow.rule_offset hn ht ha hR0 false (rowKey q) HV HR
  have HL : IntegralMixedRoadmapProperRow.offset (rowKey q)=IntegralMixedRoadmapAtomic.depth q:=by
    unfold IntegralMixedRoadmapProperRow.offset IntegralMixedRoadmapProper.levelIndex
    have HP:=HB.1
    simp only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair]
    omega
  have HO : ((G).rule (oldKey hn ht ha hR0 q)).critical.offset.val=IntegralMixedRoadmapAtomic.depth q:=HO0.trans HL
  have HD:=ambient_eq hn ht ha hR0 q
  have HI : i.val<ambient hn ht ha hR0 q-IntegralMixedRoadmapAtomic.depth q+1:=by
    simpa only [Free,HO,ambient] using i.isLt
  have HF:= (fit ((G).rule (oldKey hn ht ha hR0 q))).le
  have HJ : j≤D q:=by dsimp only [j];unfold ambient at HD HI;omega
  have HC : i.val<IntegralMixedRoadmapLocalEdge.count hn ht ha hR0 q:=by
    unfold IntegralMixedRoadmapLocalEdge.count IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex
    have HP:=HB.1
    dsimp only [j] at HJ
    omega
  have HSearch:=HAll i.val HC
  simp only [IntegralMixedRoadmapLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,List.length_replicate] at HSearch
  have HJlo : IntegralMixedRoadmapAtomic.depth q≤j:=by dsimp only [j];omega
  obtain ⟨HRj,_,ψ,Hψ,HNear⟩:=IntegralMixedRoadmapProperRow.coordinate_meaning hn ht ha hR0 right q j hv HB HJlo HJ HSearch
  have HE:=IntegralMixedRoadmapProperRow.parent_coordinate_snapshot_eq hn ht ha hR0 q
    (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q)) hv
  have HS:=IntegralMixedRoadmapProperRow.ordinary_coordinate_shape hn ht ha hR0 q
    (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q)) hv HRj HR
  let oldj:=IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j))
  let selectedj:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G oldj
    (IntegralCriticalHistoryTask.get P IntegralCriticalHistoryTask.Field.slot13
      (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 false (pair q (BinaryNatCode.encode j))))
  have HVa : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (pair q (BinaryNatCode.encode j))):=by
    simpa only [IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HSelected : selectedj.val=i.val:=by
    have HX:=IntegralMixedRoadmapProperRow.selected_coordinate hn ht ha hR0 false
      (pair q (BinaryNatCode.encode j)) HVa HRj
    have HEindex : IntegralMixedRoadmapProperRow.relativeCoordinate (pair q (BinaryNatCode.encode j))=i.val:=by
      unfold IntegralMixedRoadmapProperRow.relativeCoordinate
      have HLj : IntegralMixedRoadmapProperRow.offset (pair q (BinaryNatCode.encode j))=IntegralMixedRoadmapAtomic.depth q:=by
        simpa only [IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair] using HL
      rw [HLj]
      simp only [IntegralMixedRoadmapProperRow.coordinate,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,j,Nat.add_sub_cancel_left]
    exact HX.trans HEindex
  have HAgreement:=original_quotient_agreement
    (IntegralMixedPrefixSnapshot.ofState ((G).state oldj))
    (IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey hn ht ha hR0 q))) HE
    (field hn ht ha hR0 q hv) ψ φ Hψ Hφ
  have HCj:=IntegralMixedRoadmapProperRow.parent_canonical hn ht ha hR0 false
    (pair q (BinaryNatCode.encode j)) (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 _ HVa)
  have HTransfer:=IntegralMixedSelectedNearTransport.anchored_near_iff_of_snapshot
    (IntegralMixedPrefixSnapshot.ofState ((G).state oldj))
    (IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey hn ht ha hR0 q))) HE HCj
    ((G).birth_bound _) ((G).birth_bound _) ((G).rule oldj) ((G).rule (oldKey hn ht ha hR0 q))
    HS ψ φ HAgreement selectedj i HSelected
    (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
    (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))
    (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer right q))
    ((field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2)
    (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.midProducer (D q) (N q) q j))
    (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.childProducer (D q) (N q) q j))
  have HT:=HTransfer.mp HNear
  let ix : Fin (ambient hn ht ha hR0 q+1):=ClearedCoordinateCritical.freeIndex ((G).rule (oldKey hn ht ha hR0 q)).critical.offset.val HF i
  have Hix : ix.val=j:=congrArg (fun k : ℕ=>k+i.val) HO
  have HM:=midpoint_free hn ht ha hR0 q hv HB ix (by rw [Hix];exact HJlo)
  have HH:=child_free hn ht ha hR0 q hv ix (by rw [Hix];exact HJlo)
  rw [Hix] at HM HH
  rw [HM,HH]
  exact HT

private theorem joined_of_side (right : Bool) (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HAll : IntegralMixedRoadmapLocalEdge.allCoordinates hn ht ha hR0 right q) :
    JoinedIn {p : Fin (ambient hn ht ha hR0 q+1)→ℝ |
      (FermatCriticalHomogenization.polynomial ((G).spatial (oldKey hn ht ha hR0 q)).low
        ((G).spatial (oldKey hn ht ha hR0 q)).leading ((G).spatial (oldKey hn ht ha hR0 q)).degree).eval₂
        (Int.castRingHom ℝ) p=0} (child hn ht ha hR0 q hv) (midpoint hn ht ha hR0 q hv) :=by
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  have HP:=HB.1
  have HC : 0<IntegralMixedRoadmapLocalEdge.count hn ht ha hR0 q:=by
    unfold IntegralMixedRoadmapLocalEdge.count IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex
    omega
  have HSearch:=HAll 0 HC
  simp only [IntegralMixedRoadmapLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,
    List.length_replicate,Nat.add_zero] at HSearch
  obtain ⟨HR,HS,φ,Hφ,_⟩:=IntegralMixedRoadmapProperRow.coordinate_meaning hn ht ha hR0 right q
    (IntegralMixedRoadmapAtomic.depth q) hv HB (Nat.le_refl _) HD HSearch
  have HPhysical:=midpoint_physical hn ht ha hR0 q hv HB HR φ Hφ
  have HFrozen:=child_frozen hn ht ha hR0 q hv HB HR φ Hφ
  have HSide:=side_good_pair right q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q)) HS
  have HEndpoint:=side_value right _
    (fun side=>field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer side q)) HSide
  have HFrozenRight:=Eq.mp (congrArg (fun e : ℝ=>
    IntegralMixedSelectedCoordinateEndpoint.Frozen ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ e (child hn ht ha hR0 q hv)) HEndpoint) HFrozen
  have HOrder:=order_of_base hn ht ha hR0 q hv HB
  let a:=field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)
  let b:=field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)
  let e:=field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer right q)
  have HAB : a<b:=HOrder
  let t₀ : Ioo a b:=⟨(a+b)/2,by constructor <;> linarith⟩
  have HE : e∈Icc a b:=by
    cases right
    · exact ⟨le_refl _,le_of_lt HAB⟩
    · exact ⟨le_of_lt HAB,le_refl _⟩
  have HChoices:=IntegralMixedRelativeCuts.exists_choices ((G).state (oldKey hn ht ha hR0 q))
    ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ
  obtain ⟨c⟩:=HChoices
  exact IntegralMixedSelectedCoordinateEndpoint.joined_source_of_near
    ((G).state (oldKey hn ht ha hR0 q)) ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ c t₀
    (no_bad_of_base hn ht ha hR0 q hv HB HR φ Hφ c)
    ⟨midpoint hn ht ha hR0 q hv,HPhysical⟩ e HE (child hn ht ha hR0 q hv) HFrozenRight
    (coordinates_near hn ht ha hR0 right q hv HB HAll HR φ Hφ)

/-- Every accepted native local incidence joins its actual child point to its
actual physical midpoint. The no-critical conjunct is unnecessary for soundness. -/
theorem local_joined (q : List Bool) (H : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 q) :
    JoinedIn {p : Fin (ambient hn ht ha hR0 q+1)→ℝ |
      (FermatCriticalHomogenization.polynomial ((G).spatial (oldKey hn ht ha hR0 q)).low
        ((G).spatial (oldKey hn ht ha hR0 q)).leading ((G).spatial (oldKey hn ht ha hR0 q)).degree).eval₂
        (Int.castRingHom ℝ) p=0} (child hn ht ha hR0 q H.1) (midpoint hn ht ha hR0 q H.1) :=by
  rcases H.2.2.2 with HL|HR
  · exact joined_of_side hn ht ha hR0 false q H.1 H.2.1 HL
  · exact joined_of_side hn ht ha hR0 true q H.1 H.2.1 HR

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
