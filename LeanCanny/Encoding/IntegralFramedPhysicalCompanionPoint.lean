/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalAnchor
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardScan
public import LeanCanny.Encoding.IntegralFramedPhysicalPointEqualityTest
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalValues
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
public import LeanCanny.Geometry.IntegralMixedChronologicalCriticalReadback
/-! # Powered companion points on an arbitrary actual full framed bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (commands prefixLength defaultInstruction)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open IntegralMixedFramedCriticalGuardBits (age count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
include hr
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "S" => IntegralFramedPhysicalBankTerm.input B
local notation "stage" => IntegralFramedPhysicalCriticalGuardScan.stage

theorem count_eq (c d : List Bool) : IntegralMixedFramedCriticalGuardBits.count P T (keyDatum B.key) (pair c d)=(S).count c := by
  change _=IntegralMixedFramedPhysicalIndex.arity (commands P B.plan (B.key c))
  have H := IntegralMixedFramedCriticalGuardBits.count_actual P B.plan B.data T hr (keyDatum B.key) (pair c d)
  exact H.trans (congrArg (fun k => IntegralMixedFramedPhysicalIndex.arity (commands P B.plan k))
    (congrArg B.key (pairFst_pair c d)))
local notation "HC" => count_eq B T hr
noncomputable def block (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b i : ℕ) : ℝ :=
  let col:=IntegralMixedFramedPhysicalIndex.prefixArity P T (pair (B.key c) (List.replicate b true))+i
  if hc : col<(S).count c then (SquareSampleCompleteVertices.candidate S c w hv).val ⟨col,hc⟩^
    IntegralMixedFramedCriticalGuardBits.physicalPower P B.key (fun _=>b) c else 0
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical

noncomputable def Active (c : List Bool) (b : ℕ) :=IntegralMixedFramedCriticalGuardBits.Active P T
  (keyDatum (B).key) stage (pair c (List.replicate b true))
noncomputable def selected (c : List Bool) (b : ℕ) :=
  (IntegralMixedFramedCriticalGuardBits.header T (keyDatum (B).key) stage (pair c (List.replicate b true))).offset+
  (IntegralMixedFramedCriticalGuardBits.header T (keyDatum (B).key) stage (pair c (List.replicate b true))).coordinate

theorem selected_lt (c : List Bool) (b : ℕ) (hb : Active B T c b) :
    selected B T c b<(P).ambient (pairFst ((B).key c))+1 :=by
  obtain ⟨r,hcmd⟩:=IntegralMixedFramedCriticalGuardBits.active_critical P (B).plan (B).data T
    hr (keyDatum (B).key) stage (pair c (List.replicate b true)) hb
  unfold selected
  rw [IntegralMixedFramedCriticalGuardBits.header_actual P (B).plan (B).data T
    hr (keyDatum (B).key) stage (pair c (List.replicate b true)),hcmd]
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
    (b : ℕ) (hb : Active B T c b) : ℝ :=
  IntegralMixedFramedCriticalGuard.actualPoint P (B).plan (B).data T hr
    (keyDatum (B).key) stage (pair c (List.replicate b true)) hb (fullTuple B T hr c w hv b)
noncomputable def scalarValue (c w : List Bool) (b : ℕ) :=IntegralFramedPhysicalCriticalGuardTest.value S P (B).plan (B).data T
  (B).nodes (B).factor (B).seed (B).bounds (B).key stage HC (pair (pair c w) (List.replicate b true))

theorem selected_block (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b : ℕ)
    (hb : Active B T c b) :
    fullTuple B T hr c w hv b
      ⟨IntegralMixedFramedCriticalGuardBits.physical P T (keyDatum (B).key) stage (pair c (List.replicate b true)),
        IntegralMixedFramedCriticalGuardBits.physical_lt P (B).plan (B).data T hr
          (keyDatum (B).key) stage (pair c (List.replicate b true)) hb⟩^
      IntegralMixedFramedCriticalGuardBits.physicalPower P (keyDatum (B).key) stage (pair c (List.replicate b true))=
        block B T c w hv b (selected B T c b) :=by
  have HL:=IntegralMixedFramedCriticalGuardBits.physical_lt P (B).plan (B).data T hr
    (keyDatum (B).key) stage (pair c (List.replicate b true)) hb
  have HN:=HC c (List.replicate b true)
  have Hcol : IntegralMixedFramedCriticalGuardBits.physical P T (keyDatum (B).key) stage (pair c (List.replicate b true))=
      IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+
        selected B T c b :=by
    simp only [IntegralMixedFramedCriticalGuardBits.physical,IntegralMixedFramedCriticalGuardBits.packet,
      keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate,selected,Nat.add_assoc]
  have HI : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+
      selected B T c b<(S).count c :=by
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
    (b : ℕ) (hb : Active B T c b) :
    scalarValue B T hr c w b=InfinitesimalSign.encode 0 ↔
      retained B T hr c w hv b hb=block B T c w hv b (selected B T c b) :=by
  have HP:=IntegralFramedPhysicalCriticalGuardTest.packet S P (B).plan (B).data T
    (B).nodes (B).factor (B).seed (B).bounds (B).key stage HC c w (List.replicate b true) hv
  change scalarValue B T hr c w b=InfinitesimalSign.encode (SignType.sign
    ((IntegralMixedFramedCriticalGuardBits.polynomial P (B).plan (B).data T (keyDatum (B).key) stage
      (pair c (List.replicate b true))).eval₂ (Int.castRingHom ℝ) (fullTuple B T hr c w hv b))) at HP
  rw [HP,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff,
    IntegralMixedFramedCriticalGuard.zero_iff_actualPoint P (B).plan (B).data T hr
      (keyDatum (B).key) stage (pair c (List.replicate b true)) hb,
    selected_block B T hr c w hv b hb]
  rfl


noncomputable def geometricPoint (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b : ℕ) :
    Fin ((P).ambient (pairFst ((B).key c))+1)→ℝ :=fun i=>block B T c w hv b i.val


omit hr in
theorem active_direct (c :List Bool) (b :ℕ) (hb :Active B T c b) :
    IntegralMixedFramedCriticalGuardBits.Active P T (B).key (fun _=>b) c :=by
  simpa only [Active,IntegralMixedFramedCriticalGuardBits.Active,
    IntegralMixedFramedCriticalGuardBits.header,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] using hb

theorem geometricPoint_readback (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active B T c b) :
    geometricPoint B T c w hv b=
      IntegralMixedFramedCriticalAnchor.geometricPoint P (B).plan (B).key (fun _=>b) c
        (IntegralFramedPhysicalCriticalReadback.tuple P (B).plan (B).data (B).nodes (B).factor (B).seed
          (B).bounds (B).key (B).positive c w hv) :=by
  funext i
  have HCount:=count_eq B T hr c []
  have HC' :count P T (B).key c=(S).count c:=by
    simpa only [IntegralMixedFramedCriticalGuardBits.count,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,Function.comp_apply,pairFst_pair] using HCount
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt P T (B).key (fun _=>i.val) (fun _=>b) c
    (active_direct B T c b hb) i.isLt
  have HI :IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i.val<(S).count c:=
    HL.trans_eq HC'
  unfold geometricPoint block
  rw [dite_eq_left HI]
  unfold IntegralMixedFramedCriticalAnchor.geometricPoint IntegralFramedPhysicalCriticalReadback.tuple
    IntegralMixedFramedBankObservation.extend
  rw [←IntegralMixedFramedPhysicalIndex.prefixArity_packet P (B).plan (B).data T
    hr]
  have HI' :IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i.val<
      IntegralFramedPhysicalSquare.count P (B).plan ((B).key c):=HI
  rw [dite_eq_left HI']
  rfl

theorem exists_critical (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active B T c b)
    (r :IntegralMixedHistory.CriticalRule ((P).ambient (pairFst ((B).key c))))
    (hc :(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).command=.critical r) :
    ∃hcs :IntegralMixedFramedHistoryFamilyBits.commands P (B).plan ((B).key c)=
      (IntegralMixedFramedHistoryFamilyBits.commands P (B).plan ((B).key c)).take
        (age P (B).key (fun _=>b) c)++
      ⟨(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).source,
        (IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).source_cap,.critical r⟩::
        IntegralMixedFramedHistoryScript.paddedPast
          (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (B).plan (pairFst ((B).key c)))
          ((B).plan.rules (pairFst ((B).key c))) b,
    let x:=IntegralFramedPhysicalCriticalReadback.oldState P (B).plan (B).data (B).key c _ _ r _ _ hcs
    ∃φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalCriticalReadback.tuple P (B).plan (B).data (B).nodes (B).factor (B).seed
          (B).bounds (B).key (B).positive c w hv
          (IntegralMixedFramedPhysicalIndex.enumerate _ (x.sampler.scalar i)).val^
          UniformIntegralPowerSchedule.weights ((P).cap (pairFst ((B).key c))+1)
            (2^(P).width (pairFst ((B).key c))) _ i) ∧
      IntegralMixedCriticalReadback.CriticalPoint x
        (IntegralFramedPhysicalCriticalReadback.older_room P (B).plan (B).data (B).key c _ _ r _ _ hcs) r φ
        (geometricPoint B T c w hv b) :=by
  obtain ⟨s,hs,hcs,φ,hφ,HP⟩:=IntegralFramedPhysicalCriticalReadback.exists_active_point P (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds T hr (B).key
    (B).positive (fun _=>b) c w hv (active_direct B T c b hb)
  have Hsr :s=r:=IntegralMixedFullHistoryScript.Command.critical.inj (hs.symm.trans hc)
  subst s
  exact ⟨hcs,φ,hφ,(geometricPoint_readback B T hr c w hv b hb).symm ▸ HP⟩


theorem frame_point (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active B T c b) (labels :List Bool) (g j :ℕ)
    (HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key c))) b labels g j)
    (hc :(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key c))) b labels g j HG).rule) :
    let Q:=(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).source
    let p:=geometricPoint B T c w hv b
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀i (hi :i<WordListRecords.count labels),p ⟨i,hi.trans_le HG.1.1⟩=
      IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive c w hv
        ⟨prefixLength P ((B).key c)-1-Nat.fromBitsLE (WordList.get labels i),by
          rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
          have HB:=(active_direct B T c b hb).1
          omega⟩) ∧
    ∀ (i :Fin ((P).ambient (pairFst ((B).key c))+1)), (WordListRecords.count labels ≤ i.val) → i.val≠g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0 :=by
  let r:=(IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key c))) b labels g j HG).rule
  let newer:=(commands P (B).plan ((B).key c)).take (IntegralMixedFramedCriticalGuardBits.age P (B).key (fun _=>b) c)
  let older:=paddedPast (defaultInstruction P (B).plan (pairFst ((B).key c))) ((B).plan.rules (pairFst ((B).key c))) b
  obtain ⟨hcs,φ,Hφ,HP⟩:=exists_critical B T hr c w hv b hb r hc
  let x:=IntegralFramedPhysicalCriticalReadback.oldState P (B).plan (B).data (B).key c _ _ r newer older hcs
  have HM :older.length=b:=paddedPast_length _ _ _
  have HT :(commands P (B).plan ((B).key c)).length=prefixLength P ((B).key c):=paddedPast_length _ _ _
  have HL :(commands P (B).plan ((B).key c)).length=newer.length+1+older.length:=by
    have HH:=congrArg List.length hcs
    simpa only [newer,older,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using HH
  let v :Fin older.length→ℝ:=fun i=>IntegralFramedPhysicalSquare.point P (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv
    ⟨newer.length+1+i.val,by rw [IntegralMixedFramedHistoryFamilyBits.family_birth,←HT];omega⟩
  have HV :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=v i:=by
    intro i
    exact IntegralFramedPhysicalCriticalReadback.quotient_full P (B).plan (B).data (B).nodes (B).factor (B).seed
      (B).bounds (B).key (B).positive c w hv _ _ r newer older hcs φ Hφ i
  have HR:=IntegralMixedChronologicalFrame.raw_readback x
    (IntegralFramedPhysicalCriticalReadback.older_room P (B).plan (B).data (B).key c _ _ r newer older hcs)
    b HM labels g j HG φ v HV (geometricPoint B T c w hv b) HP
  refine ⟨HR.1,?_,HR.2.2⟩
  intro i hi
  refine (HR.2.1 i hi).trans ?_
  unfold v
  congr 1
  apply Fin.ext
  change newer.length+1+(older.length-1-Nat.fromBitsLE (WordList.get labels i))=
    prefixLength P ((B).key c)-1-Nat.fromBitsLE (WordList.get labels i)
  have HH:=HG.1.2 i hi
  omega

theorem selected_of_frame (c :List Bool) (b :ℕ) (labels :List Bool) (g j :ℕ)
    (HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key c))) b labels g j)
    (hc :(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key c))) b labels g j HG).rule) :
    selected B T c b=j :=by
  unfold selected
  rw [IntegralFramedPhysicalCriticalReadback.header_packet P (B).plan (B).data T hr
    (B).key IntegralFramedPhysicalCriticalGuardScan.stage c (List.replicate b true) b
    (by simp only [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate])]
  rw [hc]
  exact IntegralMixedChronologicalFrame.raw_selected b labels g j HG


end LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
