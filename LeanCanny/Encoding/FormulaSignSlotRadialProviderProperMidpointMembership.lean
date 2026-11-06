/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointPhysical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeValues
/-! # The actual midpoint capture belongs to the ordinary selected section -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
structure CoordinateFrame {n : ℕ} (p : Fin (n+1)→ℝ) (labels : List Bool)
    (values : ℕ→ℝ) (a b : ℕ) : Prop where
  count : WordListRecords.count labels<n+1
  frozen : ∀i : Fin (WordListRecords.count labels),p ⟨i.val,i.isLt.trans count⟩=
    values (Nat.fromBitsLE (WordList.get labels i.val))
  height : p ⟨WordListRecords.count labels,count⟩=(values a+values b)/2
private theorem frame_transport {n m : ℕ} (he : n=m) (p : Fin (n+1)→ℝ) (q : Fin (m+1)→ℝ)
    (hp : HEq p q) (labels : List Bool) (values : ℕ→ℝ) (a b : ℕ)
    (hf : CoordinateFrame p labels values a b) : CoordinateFrame q labels values a b :=by
  cases he
  have HE : p=q:=eq_of_heq hp
  exact HE ▸ hf
private theorem frame_values {n : ℕ} (p : Fin (n+1)→ℝ) (labels : List Bool)
    (v w : ℕ→ℝ) (a b : ℕ) (hf : CoordinateFrame p labels v a b)
    (hl : ∀i<WordListRecords.count labels,v (Nat.fromBitsLE (WordList.get labels i))=
      w (Nat.fromBitsLE (WordList.get labels i))) (ha : v a=w a) (hb : v b=w b) :
    CoordinateFrame p labels w a b :=by
  refine ⟨hf.count,fun i=>(hf.frozen i).trans (hl i.val i.isLt),?_⟩
  exact hf.height.trans (congrArg₂ (fun a b : ℝ=>(a+b)/2) ha hb)
private theorem physical_of_capture_frame {n S W m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S W m ι) (hm : m≤S) (b : ℕ) (hb : m=b) (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good n b labels g j)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (v : ℕ→ℝ)
    (hv : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=v (m-1-i.val))
    (a d : ℕ) (p : Fin (n+1)→ℝ)
    (hz : SourceJet Q p (WordListRecords.count labels+1) g)
    (hf : CoordinateFrame p labels v a d) :
    p∈IntegralMixedSelectedPhysicalFiber.physical x hm
      ((IntegralMixedChronologicalCutCode.rawData n b labels g j hg).rule
        (commonDenominator x) (commonDenominator_ne_zero x)) φ ((v a+v d)/2) :=by
  apply IntegralMixedChronologicalSweepReadback.raw_physical x hm b hb labels g j hg φ
    (fun i=>v (m-1-i.val)) hv _ p hz.1 _ hf.height hz.2
  intro i hi
  have HH:=hg.1.2 i hi
  have HE : m-1-(m-1-Nat.fromBitsLE (WordList.get labels i))=
      Nat.fromBitsLE (WordList.get labels i):=by omega
  simpa only [HE] using hf.frozen ⟨i,hi⟩
private theorem native_midpoint_frame (K : IntegralFramedBankQuery.Bank)
    (ts : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents K.parameters K.plan K.data ts)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w)
    (b : ℕ) (hb : IntegralFramedPhysicalCompanionPoint.Active K ts c b)
    (labels : List Bool) (a d g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good (K.parameters.ambient (pairFst (K.key c))) b labels a d g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt K.parameters K.plan (pairFst (K.key c)) b).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (K.parameters.ambient (pairFst (K.key c))) b labels a d g j hg).rule) :
    CoordinateFrame (IntegralFramedPhysicalCompanionPoint.geometricPoint K ts c w hv b) labels
      (IntegralFramedPhysicalBankTerm.env K ts hr c w hv) a d :=by
  have HH:=IntegralFramedPhysicalCompanionPoint.midpoint_frame_env K ts hr c w hv b hb labels a d g j hg hc
  exact ⟨(by have H1:=hg.2.2.2.1;have H2:=hg.2.2.2.2.1;omega),fun i=>HH.2.1 i.val i.isLt,HH.2.2.1⟩
private theorem cast_frame_point_heq {a b : ℕ} (h : a=b) (p : Fin (a+1)→ℝ) :
    HEq p (fun i : Fin (b+1)=>p (Fin.cast (congrArg (·+1) h).symm i)) :=by cases h;rfl
private theorem raw_rule_heq {a b : ℕ} (hn : a=b) (birth : ℕ) (labels : List Bool) (g j : ℕ)
    (ha : IntegralMixedChronologicalCutCode.Good a birth labels g j)
    (hb : IntegralMixedChronologicalCutCode.Good b birth labels g j) (Q : ℤ) (hq : Q≠0) :
    HEq ((IntegralMixedChronologicalCutCode.rawData a birth labels g j ha).rule Q hq)
      ((IntegralMixedChronologicalCutCode.rawData b birth labels g j hb).rule Q hq) :=by cases hn;rfl
private theorem family_ambient_value (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (h : IntegralMixedFramedHistoryFamilyBits.Data p d)
    (key : List Bool) : (IntegralMixedFramedHistoryFamilyBits.family p d h).ambient key=p.ambient (pairFst key) :=rfl
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H"=>FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family SourceJet

theorem before_probe_field (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (i : ℕ) (hi : i<creating z) : originalValue (atomic z) hv i=
      FormulaSignSlotRadialProviderAtomic.field (atomic z) hv i :=by
  have HB:=probe_original_field_count z hv
  have HC:=FormulaSignSlotRadialProviderFieldEquality.count_eq (FormulaSignSlotRadialProviderAtomic.context (atomic z))
  have HE : FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context (atomic z))=
      FormulaSignSlotRadialProviderRecordPlan.fullCount (FormulaSignSlotRadialProviderAtomic.root (atomic z)):=by
    simpa only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair] using HC
  exact originalValue_field _ hv i (by omega)

theorem midpoint_capture_frame (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (i : ℕ) (hi : i<IntegralMixedRoadmapProper.captureCount (dimension z) (atomic z)) :
    CoordinateFrame (midpointRowCapture z hv i) (labels z) (originalValue (atomic z) hv)
      (oldProducer false z) (oldProducer true z) :=by
  let q:=atomic z
  let b:=IntegralMixedRoadmapProper.midFirst (dimension z) (initial z) q+i
  let p:=FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) b
  have HF:=native_midpoint_frame B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) b
    (FormulaSignSlotRadialProviderProper.midpoint_capture_active q hv hd i hi)
    (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
    (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q+1) (dimension z-i)
    (FormulaSignSlotRadialProviderProper.midpoint_companion_context_good q hv hd i hi)
    (FormulaSignSlotRadialProviderProper.midpoint_companion_context_command q hv hd i hi)
  have HP : HEq p (midpointRowCapture z hv i):=cast_frame_point_heq (midpoint_row_ambient z) p
  have HFrame : CoordinateFrame (midpointRowCapture z hv i) (labels z)
      (FormulaSignSlotRadialProviderAtomic.field q hv) (oldProducer false z) (oldProducer true z):=
    frame_transport (midpoint_row_ambient z) p _ HP _ _ _ _ HF
  exact frame_values _ _ _ _ _ _ HFrame
    (fun j hj=>(before_probe_field z hv _ (hr.1.1.2 j hj)).symm)
    (before_probe_field z hv _ hr.2.2.1).symm
    (before_probe_field z hv _ hr.2.2.2.1).symm

theorem midpoint_capture_physical (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (i : ℕ) (hi : i<IntegralMixedRoadmapProper.captureCount (dimension z) (atomic z))
    (φ : ((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀j,φ (((G).state (parentKey false z)).bank.numerator j)/
      (((G).state (parentKey false z)).bank.denominator j:ℝ)=
      originalValue (atomic z) hv ((G).birth (parentKey false z)-1-j.val)) :
    midpointRowCapture z hv i∈IntegralMixedSelectedPhysicalFiber.physical
      ((G).state (parentKey false z)) ((G).birth_bound _) ((G).rule (parentKey false z)) φ
      ((originalValue (atomic z) hv (oldProducer false z)+originalValue (atomic z) hv (oldProducer true z))/2) :=by
  have HC:=row_count_positive z hv
  have HG:=(parent_good false z HC hr).1
  have HB:=(parent_birth_actual false z hv).trans (parentBirth_eq false z HC).symm
  have HR:=rule_at_parent false z HC hr
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank] at HR HB
  rw [HR]
  simp only [parentData,Bool.false_eq_true,ite_false]
  with_unfolding_all
    exact physical_of_capture_frame ((G).state (parentKey false z)) ((G).birth_bound _)
      (parentBirth false z) HB (labels z) (offset z) (coordinate z) HG φ
      (originalValue (atomic z) hv) hφ (oldProducer false z) (oldProducer true z) (midpointRowCapture z hv i)
      (midpoint_capture_rows z hv hd i hi) (midpoint_capture_frame z hv hd hr i hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
