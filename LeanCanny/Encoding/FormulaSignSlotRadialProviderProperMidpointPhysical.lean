/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowMeaning
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback
/-! # Actual midpoint captures in the source of the reserved ordinary row -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
def SourceJet {n : ℕ} (Q : SpatialSource n) (p : Fin (n+1)→ℝ) (k g : ℕ) : Prop:=
  (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
  ∀j : Fin (n+1),k ≤ j.val → j.val≠g →
    (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
      (Int.castRingHom ℝ) p=0
private theorem native_midpoint_jet (K : IntegralFramedBankQuery.Bank)
    (ts : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents K.parameters K.plan K.data ts)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input K) c w)
    (b : ℕ) (hb : IntegralFramedPhysicalCompanionPoint.Active K ts c b)
    (labels : List Bool) (a d g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good (K.parameters.ambient (pairFst (K.key c))) b labels a d g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt K.parameters K.plan (pairFst (K.key c)) b).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (K.parameters.ambient (pairFst (K.key c))) b labels a d g j hg).rule) :
    SourceJet (IntegralMixedFramedRootPullback.instructionAt K.parameters K.plan (pairFst (K.key c)) b).source
      (IntegralFramedPhysicalCompanionPoint.geometricPoint K ts c w hv b) (WordListRecords.count labels+1) g :=by
  have HH:=IntegralFramedPhysicalCompanionPoint.midpoint_frame_env K ts hr c w hv b hb labels a d g j hg hc
  exact ⟨HH.1,HH.2.2.2⟩
private theorem source_root_heq (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (a b : List Bool) (he : a=b) (k : ℕ) :
    HEq (IntegralMixedFramedRootPullback.instructionAt p d a k).source
      (IntegralMixedFramedRootPullback.instructionAt p d b k).source :=by cases he;rfl
private theorem family_source_heq (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (h : IntegralMixedFramedHistoryFamilyBits.Data p d)
    (key : List Bool) (Q : SpatialSource (p.ambient (pairFst key)))
    (hs : (IntegralMixedFramedHistoryFamilyBits.instruction p d key).source=d.initialSource (pairFst key))
    (hq : d.initialSource (pairFst key)=Q) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family p d h).spatial key) Q :=by
  exact heq_of_eq (hs.trans hq)
private theorem family_ambient (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (h : IntegralMixedFramedHistoryFamilyBits.Data p d)
    (key : List Bool) : (IntegralMixedFramedHistoryFamilyBits.family p d h).ambient key=p.ambient (pairFst key) :=rfl
private theorem cast_point_heq {a b : ℕ} (h : a=b) (p : Fin (a+1) → ℝ) :
    HEq p (fun i : Fin (b+1)=>p (Fin.cast (congrArg (·+1) h).symm i)) :=by cases h;rfl
private theorem jet_transport {a b : ℕ} (P : SpatialSource a) (Q : SpatialSource b) (HD : a=b)
    (HS : HEq P Q) (p : Fin (a+1) → ℝ) (q : Fin (b+1) → ℝ) (HP : HEq p q) (k g : ℕ)
    (HJ : SourceJet P p k g) :
    SourceJet Q q k g :=by
  cases HD
  have H1 : P=Q:=eq_of_heq HS
  have H2 : p=q:=eq_of_heq HP
  simpa only [SourceJet,←H1,←H2] using HJ
attribute [local irreducible] SourceJet
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H"=>FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.source

theorem midpoint_capture_source (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z)) (i : ℕ) (hi : i<captureCount (dimension z) (atomic z)) :
    HEq (IntegralMixedFramedRootPullback.instructionAt P D
      (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context (atomic z))))
      (midFirst (dimension z) (initial z) (atomic z)+i)).source
      ((G).spatial (parentKey false z)) :=by
  let q:=atomic z
  let rawIndex:=FormulaSignSlotRadialProviderProper.midRawIndex (dimension z) q+1+i
  let b:=midFirst (dimension z) (initial z) q+i
  have HI : rawIndex<IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q):=by
    rw [IntegralMixedCausalRecordPlanBits.count,FormulaSignSlotRadialProviderAtomic.root_records]
    simpa only [rawIndex,FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload,dimension] using
      FormulaSignSlotRadialProviderProper.midpoint_companion_fit q hv hd i hi
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)+rawIndex:=by
    have HN : FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)=initial z:=rfl
    rw [HN]
    simp only [b,rawIndex,midFirst,midBirth,baseBirth,IntegralMixedRoadmapChain.birth,
      FormulaSignSlotRadialProviderProper.midRawIndex,FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
    omega
  have HS:=FormulaSignSlotRadialProviderRecordReceipt.source_at (FormulaSignSlotRadialProviderAtomic.root q) rawIndex b HI HB
  have HNative:=source_root_heq P D _ _ (FormulaSignSlotRadialProviderAtomic.context_root q) b
  have HSource : HEq (IntegralMixedFramedRootPullback.instructionAt P D
      (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q))) b).source (FormulaSignSlotRadialProviderRecordPlan.spatial (FormulaSignSlotRadialProviderAtomic.root q)):=by
    exact HNative.trans (heq_of_eq HS)
  have HP:=FormulaSignSlotRadialProviderRecordPrefix.instruction_initial (parentKey false z)
  have HP0:=FormulaSignSlotRadialProviderRecordPrefix.initial_source (pairFst (parentKey false z))
  have HParent : HEq ((G).spatial (parentKey false z))
      (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst (parentKey false z))):=by
    exact family_source_heq P D H (parentKey false z) _ HP HP0
  have HProvider : FormulaSignSlotRadialProviderRecordPlan.providerContext (pairFst (parentKey false z))=
      FormulaSignSlotRadialProviderRecordPlan.providerContext (FormulaSignSlotRadialProviderAtomic.root q):=by
    rw [parentKey_root,root_provider,FormulaSignSlotRadialProviderAtomic.root_provider]
  have HC:=FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ HProvider
  exact HSource.trans (HParent.trans HC).symm

attribute [local semireducible] FormulaSignSlotRadialProviderRecordPlan.bank

theorem midpoint_row_ambient (z : List Bool) :
    (P).ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context (atomic z))))=
      (G).ambient (parentKey false z) :=by
  have HA:=FormulaSignSlotRadialProviderAtomic.native_dimension (atomic z)
  have HB:=parentDimension_eq false z
  rw [family_ambient]
  exact HA.trans HB.symm

noncomputable def midpointRowCapture (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) (i : ℕ) :
    Fin ((G).ambient (parentKey false z)+1) → ℝ:=fun j=>
  FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context (atomic z))
    (FormulaSignSlotRadialProviderAtomic.word (atomic z)) (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv)
    (midFirst (dimension z) (initial z) (atomic z)+i)
    (Fin.cast (congrArg (·+1) (midpoint_row_ambient z)).symm j)

theorem midpoint_capture_rows (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (i : ℕ) (hi : i<captureCount (dimension z) (atomic z)) :
    SourceJet ((G).spatial (parentKey false z)) (midpointRowCapture z hv i)
      (WordListRecords.count (labels z)+1) (offset z) :=by
  let q:=atomic z
  let b:=midFirst (dimension z) (initial z) q+i
  let p:=FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) b
  have HP : HEq p (midpointRowCapture z hv i):=cast_point_heq (midpoint_row_ambient z) p
  have HF:=native_midpoint_jet B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) b
    (FormulaSignSlotRadialProviderProper.midpoint_capture_active q hv hd i hi)
    (IntegralMixedRoadmapProper.labels q) (producer false q) (producer true q) (levelIndex q+1) (dimension z-i)
    (FormulaSignSlotRadialProviderProper.midpoint_companion_context_good q hv hd i hi)
    (FormulaSignSlotRadialProviderProper.midpoint_companion_context_command q hv hd i hi)
  exact jet_transport _ _ (midpoint_row_ambient z) (midpoint_capture_source z hv hd i hi)
    p (midpointRowCapture z hv i) HP (WordListRecords.count (labels z)+1) (offset z) HF

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
