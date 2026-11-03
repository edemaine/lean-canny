/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardOrigin
/-! # A companion guard reads its own actual quotient and powered point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open IntegralMixedPhysicalPointEquality (block)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native tables IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalCriticalGuardTest.value IntegralMixedPhysicalPointEquality.value
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "T" => tables hn ht ha hR outer
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer
local notation "HC" => IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer
local notation "stage" => IntegralFramedPhysicalCriticalGuardScan.stage

noncomputable def Active (c : List Bool) (b : ℕ) :=IntegralMixedFramedCriticalGuardBits.Active P T
  (keyDatum (B).key) stage (pair c (List.replicate b true))
noncomputable def selected (c : List Bool) (b : ℕ) :=
  (IntegralMixedFramedCriticalGuardBits.header T (keyDatum (B).key) stage (pair c (List.replicate b true))).offset+
  (IntegralMixedFramedCriticalGuardBits.header T (keyDatum (B).key) stage (pair c (List.replicate b true))).coordinate

theorem selected_lt (c : List Bool) (b : ℕ) (hb : Active hn ht ha hR outer c b) :
    selected hn ht ha hR outer c b<(P).ambient (pairFst ((B).key c))+1 :=by
  obtain ⟨r,hr⟩:=IntegralMixedFramedCriticalGuardBits.active_critical P (B).plan (B).data T
    (represents hn ht ha hR outer) (keyDatum (B).key) stage (pair c (List.replicate b true)) hb
  unfold selected
  rw [IntegralMixedFramedCriticalGuardBits.header_actual P (B).plan (B).data T
    (represents hn ht ha hR outer) (keyDatum (B).key) stage (pair c (List.replicate b true)),hr]
  simp only [IntegralMixedCommandHeaderBits.command,keyDatum,pairFst_pair]
  change r.offset.val+r.coordinate%((P).ambient (pairFst ((B).key c))-r.offset.val+1)<(P).ambient (pairFst ((B).key c))+1
  have HH:=r.offset.isLt
  simp only [keyDatum,pairFst_pair] at HH
  have HM:=Nat.mod_lt r.coordinate (by omega : 0<(P).ambient (pairFst ((B).key c))-r.offset.val+1)
  omega

noncomputable def fullTuple (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b : ℕ) :=
  IntegralFramedPhysicalCriticalGuardScan.point S P (B).plan (B).data T (B).nodes (B).factor (B).seed
    (B).bounds (B).key HC c w hv (List.replicate b true)
noncomputable def retained (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (b : ℕ) (hb : Active hn ht ha hR outer c b) : ℝ :=
  IntegralMixedFramedCriticalGuard.actualPoint P (B).plan (B).data T (represents hn ht ha hR outer)
    (keyDatum (B).key) stage (pair c (List.replicate b true)) hb (fullTuple hn ht ha hR outer c w hv b)
noncomputable def scalarValue (c w : List Bool) (b : ℕ) :=IntegralFramedPhysicalCriticalGuardTest.value S P (B).plan (B).data T
  (B).nodes (B).factor (B).seed (B).bounds (B).key stage HC (pair (pair c w) (List.replicate b true))

theorem correlation_packet (c w : List Bool) (a f k j : ℕ) :
    correlation hn ht ha hR outer (pair (pair (pair c w) (descriptor a f k)) (List.replicate j true))=
      scalarValue hn ht ha hR outer c w (f+j) :=by
  simp only [correlation,Function.comp_apply,correlationQuery,first,descriptor,scalarValue,
    pairFst_pair,pairSnd_pair,List.length_replicate]

theorem selected_block (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b : ℕ)
    (hb : Active hn ht ha hR outer c b) :
    fullTuple hn ht ha hR outer c w hv b
      ⟨IntegralMixedFramedCriticalGuardBits.physical P T (keyDatum (B).key) stage (pair c (List.replicate b true)),
        IntegralMixedFramedCriticalGuardBits.physical_lt P (B).plan (B).data T (represents hn ht ha hR outer)
          (keyDatum (B).key) stage (pair c (List.replicate b true)) hb⟩^
      IntegralMixedFramedCriticalGuardBits.physicalPower P (keyDatum (B).key) stage (pair c (List.replicate b true))=
        block hn ht ha hR outer c w hv b (selected hn ht ha hR outer c b) :=by
  have HL:=IntegralMixedFramedCriticalGuardBits.physical_lt P (B).plan (B).data T (represents hn ht ha hR outer)
    (keyDatum (B).key) stage (pair c (List.replicate b true)) hb
  have HN:=HC c (List.replicate b true)
  have Hcol : IntegralMixedFramedCriticalGuardBits.physical P T (keyDatum (B).key) stage (pair c (List.replicate b true))=
      IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+
        selected hn ht ha hR outer c b :=by
    simp only [IntegralMixedFramedCriticalGuardBits.physical,IntegralMixedFramedCriticalGuardBits.packet,
      keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate,selected,Nat.add_assoc]
  have HI : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+
      selected hn ht ha hR outer c b<(S).count c :=by
    rw [←Hcol]
    exact HL.trans_eq HN
  unfold block
  rw [dite_eq_left HI]
  apply congrArg₂ (fun (a : ℝ) (e : ℕ)=>a^e)
  · unfold fullTuple IntegralFramedPhysicalCriticalGuardScan.point
    apply congrArg (SquareSampleCompleteVertices.candidate S c w hv).val
    apply Fin.ext
    change 0+IntegralMixedFramedCriticalGuardBits.physical P T (keyDatum (B).key) stage
      (pair c (List.replicate b true))=_
    exact (Nat.zero_add _).trans Hcol
  · simp only [IntegralMixedFramedCriticalGuardBits.physicalPower,keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
      pairFst_pair,pairSnd_pair,List.length_replicate]

theorem scalarValue_zero_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (b : ℕ) (hb : Active hn ht ha hR outer c b) :
    scalarValue hn ht ha hR outer c w b=InfinitesimalSign.encode 0 ↔
      retained hn ht ha hR outer c w hv b hb=block hn ht ha hR outer c w hv b (selected hn ht ha hR outer c b) :=by
  have HP:=IntegralFramedPhysicalCriticalGuardTest.packet S P (B).plan (B).data T
    (B).nodes (B).factor (B).seed (B).bounds (B).key stage HC c w (List.replicate b true) hv
  change scalarValue hn ht ha hR outer c w b=InfinitesimalSign.encode (SignType.sign
    ((IntegralMixedFramedCriticalGuardBits.polynomial P (B).plan (B).data T (keyDatum (B).key) stage
      (pair c (List.replicate b true))).eval₂ (Int.castRingHom ℝ) (fullTuple hn ht ha hR outer c w hv b))) at HP
  rw [HP,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff,
    IntegralMixedFramedCriticalGuard.zero_iff_actualPoint P (B).plan (B).data T (represents hn ht ha hR outer)
      (keyDatum (B).key) stage (pair c (List.replicate b true)) hb,
    selected_block hn ht ha hR outer c w hv b hb]
  rfl

theorem admissible_packet_iff (c w : List Bool) (a b i : ℕ) :
    IntegralMixedPhysicalPointEquality.Admissible hn ht ha hR outer
      (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a b i)) ↔
    Active hn ht ha hR outer c a ∧ Active hn ht ha hR outer c b ∧ i<(P).ambient (pairFst ((B).key c))+1 :=by
  simp only [IntegralMixedPhysicalPointEquality.Admissible,IntegralMixedFramedPointEqualityBits.Admissible,
    IntegralMixedPhysicalPointEquality.context,IntegralMixedPhysicalPointEquality.left,IntegralMixedPhysicalPointEquality.right,
    IntegralMixedPhysicalPointEquality.coordinate,IntegralMixedPhysicalPointEquality.datum,Active,
    IntegralMixedFramedCriticalGuardBits.Active,IntegralMixedFramedCriticalGuardBits.header,
    IntegralFramedPhysicalCriticalGuardScan.stage,keyDatum,pairFst_pair,pairSnd_pair,List.length_replicate,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def geometricPoint (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b : ℕ) :
    Fin ((P).ambient (pairFst ((B).key c))+1)→ℝ :=fun i=>block hn ht ha hR outer c w hv b i.val

theorem holds_iff_points (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (a f k : ℕ) (hAnchor : Active hn ht ha hR outer c a) :
    holds hn ht ha hR outer (pair (pair c w) (descriptor a f k)) ↔
      ∀j<k,∃hb : Active hn ht ha hR outer c (f+j),
        geometricPoint hn ht ha hR outer c w hv (f+j)=geometricPoint hn ht ha hR outer c w hv a ∧
        retained hn ht ha hR outer c w hv (f+j) hb=
          geometricPoint hn ht ha hR outer c w hv a
            ⟨selected hn ht ha hR outer c (f+j),selected_lt hn ht ha hR outer c (f+j) hb⟩ :=by
  have HH : holds hn ht ha hR outer (pair (pair c w) (descriptor a f k)) ↔
      ∀j<k,(∀i<(P).ambient (pairFst ((B).key c))+1,
        IntegralMixedPhysicalPointEquality.Accepted hn ht ha hR outer
          (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a (f+j) i))) ∧
        scalarValue hn ht ha hR outer c w (f+j)=InfinitesimalSign.encode 0 :=by
    simp only [holds]
    simp_rw [correlation_packet]
    simp only [number,descriptor,dimension,coordinateQuery_packet,anchor,first,
      pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [HH]
  constructor
  · intro H j hj
    have HJ:=H j hj
    have H0:=HJ.1 0 (Nat.zero_lt_succ _)
    have HB:=((admissible_packet_iff hn ht ha hR outer c w a (f+j) 0).mp H0.2.1).2.1
    have HE : geometricPoint hn ht ha hR outer c w hv (f+j)=geometricPoint hn ht ha hR outer c w hv a :=by
      funext i
      have HI:=HJ.1 i.val i.isLt
      exact ((IntegralMixedPhysicalPointEquality.zero_iff_block hn ht ha hR outer c w hv a (f+j) i.val
        HI.2.1).mp HI.2.2).symm
    refine ⟨HB,HE,?_⟩
    exact ((scalarValue_zero_iff hn ht ha hR outer c w hv (f+j) HB).mp HJ.2).trans
      (congrFun HE ⟨selected hn ht ha hR outer c (f+j),selected_lt hn ht ha hR outer c (f+j) HB⟩)
  · intro H j hj
    obtain ⟨HB,HE,HR⟩:=H j hj
    refine ⟨fun i hi=>?_,?_⟩
    · have HA:=(admissible_packet_iff hn ht ha hR outer c w a (f+j) i).mpr ⟨hAnchor,HB,hi⟩
      refine ⟨IntegralMixedPhysicalPointEquality.wellformed_packet c w a (f+j) i,HA,?_⟩
      apply (IntegralMixedPhysicalPointEquality.zero_iff_block hn ht ha hR outer c w hv a (f+j) i HA).mpr
      exact (congrFun HE ⟨i,hi⟩).symm
    · apply (scalarValue_zero_iff hn ht ha hR outer c w hv (f+j) HB).mpr
      exact HR.trans (congrFun HE ⟨selected hn ht ha hR outer c (f+j),selected_lt hn ht ha hR outer c (f+j) HB⟩).symm

theorem language_packet_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (a f k : ℕ) (hAnchor : Active hn ht ha hR outer c a)
    (hfit : f+k≤IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)) :
    pair (pair c w) (descriptor a f k)∈language hn ht ha hR outer ↔
      ∀j<k,∃hb : Active hn ht ha hR outer c (f+j),
        geometricPoint hn ht ha hR outer c w hv (f+j)=geometricPoint hn ht ha hR outer c w hv a ∧
        retained hn ht ha hR outer c w hv (f+j) hb=
          geometricPoint hn ht ha hR outer c w hv a
            ⟨selected hn ht ha hR outer c (f+j),selected_lt hn ht ha hR outer c (f+j) hb⟩ :=by
  have HG : Grammar hn ht ha hR outer (pair (pair c w) (descriptor a f k)) :=by
    refine ⟨descriptor_packet c w a f k,?_,?_⟩
    · simpa only [Active,anchorQuery,anchor,descriptor,pairFst_pair,pairSnd_pair,List.length_replicate] using hAnchor
    · simpa only [first,number,descriptor,pairFst_pair,pairSnd_pair,List.length_replicate] using hfit
  have HM : pair (pair c w) (descriptor a f k)∈language hn ht ha hR outer ↔
      holds hn ht ha hR outer (pair (pair c w) (descriptor a f k)) :=by
    constructor
    · exact fun h=>h.2.2
    · intro h
      refine ⟨?_,HG,h⟩
      simpa only [pairFst_pair,pairSnd_pair] using hv
  exact HM.trans (holds_iff_points hn ht ha hR outer c w hv a f k hAnchor)

theorem reject_malformed (z : List Bool) (h : ¬Wellformed z) : z∉language hn ht ha hR outer :=
  fun H=>h H.2.1.1

theorem reject_outside_coordinate (c w : List Bool) (a b i : ℕ)
    (hi : (P).ambient (pairFst ((B).key c))+1 ≤ i) :
    ¬IntegralMixedPhysicalPointEquality.Accepted hn ht ha hR outer
      (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a b i)) :=by
  intro H
  exact (Nat.not_lt_of_ge hi) ((admissible_packet_iff hn ht ha hR outer c w a b i).mp H.2.1).2.2

theorem reject_noncritical_anchor (c w : List Bool) (a f k : ℕ)
    (hb : ¬Active hn ht ha hR outer c a) :
    pair (pair c w) (descriptor a f k)∉language hn ht ha hR outer :=by
  intro H
  apply hb
  have HA:=H.2.1.2.1
  simpa only [Active,anchorQuery,anchor,descriptor,pairFst_pair,pairSnd_pair,List.length_replicate] using HA

end LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
