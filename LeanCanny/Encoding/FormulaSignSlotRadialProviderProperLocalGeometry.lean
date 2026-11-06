/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateLocalPath
/-! # Genuine child frozen equations and physical MID in the actual provider parent -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem family_raw_rule (p :Parameters) (d :IntegralMixedFramedHistoryFamilyBits.Plan p)
    (h :IntegralMixedFramedHistoryFamilyBits.Data p d) (k labels :List Bool) (g j b :ℕ)
    (hg :IntegralMixedChronologicalCutCode.Good (p.ambient (pairFst k)) b labels g j)
    (hb :b=(IntegralMixedFramedHistoryFamilyBits.family p d h).birth k)
    (hr :(IntegralMixedFramedHistoryFamilyBits.family p d h).rule k=(IntegralMixedChronologicalCutCode.rawData
      (p.ambient (pairFst k)) b labels g j hg).rule
        (commonDenominator ((IntegralMixedFramedHistoryFamilyBits.family p d h).state k))
        (commonDenominator_ne_zero ((IntegralMixedFramedHistoryFamilyBits.family p d h).state k))) :
    ∃HG :IntegralMixedChronologicalCutCode.Good ((IntegralMixedFramedHistoryFamilyBits.family p d h).ambient k)
      ((IntegralMixedFramedHistoryFamilyBits.family p d h).birth k) labels g j,
      (IntegralMixedFramedHistoryFamilyBits.family p d h).rule k=(IntegralMixedChronologicalCutCode.rawData
        ((IntegralMixedFramedHistoryFamilyBits.family p d h).ambient k)
        ((IntegralMixedFramedHistoryFamilyBits.family p d h).birth k) labels g j HG).rule
          (commonDenominator ((IntegralMixedFramedHistoryFamilyBits.family p d h).state k))
          (commonDenominator_ne_zero ((IntegralMixedFramedHistoryFamilyBits.family p d h).state k)):=by
  cases hb
  exact ⟨hg,hr⟩

private theorem cast_heq {a b :ℕ} (H :a=b) (p :Fin a→ℝ) :
    HEq p (fun i :Fin b=>p (Fin.cast H.symm i)):=by cases H;rfl

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D0"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H0"=>FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D0 H0
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
open FormulaSignSlotRadialProviderProperRow
attribute [local irreducible] IntegralFramedPhysicalCompanionPoint.geometricPoint

private theorem row_capture_heq (z :List Bool)
    (hv :FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) (i :ℕ) :
    HEq (FormulaSignSlotRadialProviderAtomic.geometricPoint
      (FormulaSignSlotRadialProviderAtomic.context (atomic z))
      (FormulaSignSlotRadialProviderAtomic.word (atomic z))
      (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv)
      (midFirst (dimension z) (initial z) (atomic z)+i))
      (midpointRowCapture z hv i):=by
  exact cast_heq (congrArg (·+1) (midpoint_row_ambient z)) _

private theorem atomic_point_heq (q r :List Bool)
    (hq :FormulaSignSlotRadialProviderAtomic.Valid q)
    (hr :FormulaSignSlotRadialProviderAtomic.Valid r) (H :q=r) (b d :ℕ) (Hb :b=d) :
    HEq (FormulaSignSlotRadialProviderAtomic.geometricPoint
      (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
      (FormulaSignSlotRadialProviderAtomic.full_valid q hq) b)
      (FormulaSignSlotRadialProviderAtomic.geometricPoint
      (FormulaSignSlotRadialProviderAtomic.context r) (FormulaSignSlotRadialProviderAtomic.word r)
      (FormulaSignSlotRadialProviderAtomic.full_valid r hr) d):=by
  cases H
  cases Hb
  rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.field
  midpoint child field

private theorem coarse_labels_count (q :List Bool) :WordListRecords.count (FormulaSignSlotRadialProviderProperRow.labels (rowKey q))=levelIndex q:=by
  simp only [FormulaSignSlotRadialProviderProperRow.labels,atomic,rowKey,pairFst_pair,IntegralMixedRoadmapProper.labels_count]

theorem child_frozen (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB :FormulaSignSlotRadialProviderProper.Base q)
    (HR :FormulaSignSlotRadialProviderProperRowWitness.RowGood (rowKey q))
    (φ :((G).state (oldKey q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ :∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=field q hv ((G).birth (oldKey q)-1-i.val)) :
    IntegralMixedSelectedCoordinateEndpoint.Frozen ((G).state (oldKey q)) ((G).birth_bound _)
      ((G).rule (oldKey q)) φ
      (if IntegralMixedRoadmapChain.sideWord (FormulaSignSlotRadialProviderAtomic.payload q) (levelIndex q)=[true]
       then field q hv (producer true q) else field q hv (producer false q)) (child q hv):=by
  have HV:FormulaSignSlotRadialProviderAtomic.Valid (atomic (rowKey q)):=by
    simpa only [atomic,rowKey,pairFst_pair] using hv
  have HC:=row_count_positive (rowKey q) HV
  have HG:=(parent_good false (rowKey q) HC HR).1
  have HBth:parentBirth false (rowKey q)=(G).birth (oldKey q):=by
    with_unfolding_all exact (parentBirth_eq false (rowKey q) HC).trans (parent_birth_actual false (rowKey q) HV).symm
  have HRu:=rule_at_parent false (rowKey q) HC HR
  simp only [parentData,Bool.false_eq_true,ite_false] at HRu
  have HShape:∃HG0 :IntegralMixedChronologicalCutCode.Good ((G).ambient (oldKey q))
      ((G).birth (oldKey q)) (FormulaSignSlotRadialProviderProperRow.labels (rowKey q)) (offset (rowKey q)) (coordinate (rowKey q)),
      (G).rule (oldKey q)=(IntegralMixedChronologicalCutCode.rawData
        ((G).ambient (oldKey q)) ((G).birth (oldKey q)) (FormulaSignSlotRadialProviderProperRow.labels (rowKey q))
        (offset (rowKey q)) (coordinate (rowKey q)) HG0).rule
          (commonDenominator ((G).state (oldKey q))) (commonDenominator_ne_zero ((G).state (oldKey q))):=by
    with_unfolding_all exact (family_raw_rule P D0 H0 (oldKey q) (FormulaSignSlotRadialProviderProperRow.labels (rowKey q))
      (offset (rowKey q)) (coordinate (rowKey q)) (parentBirth false (rowKey q)) HG HBth HRu)
  obtain ⟨HG0,HRule⟩:=HShape
  rw [HRule]
  apply IntegralMixedChronologicalSweepReadback.raw_frozen ((G).state (oldKey q)) ((G).birth_bound _)
    ((G).birth (oldKey q)) rfl (FormulaSignSlotRadialProviderProperRow.labels (rowKey q)) (offset (rowKey q)) (coordinate (rowKey q)) HG0 φ
    (fun i=>field q hv ((G).birth (oldKey q)-1-i.val)) Hφ
  · intro i hi
    have HI:i<levelIndex q:=by rw [←coarse_labels_count q];exact hi
    have HH:=child_frozen_labels q hv
      (Fin.cast (congrArg (·+1) (ambient_eq q)) ⟨i,hi.trans_le HG0.1.1⟩) HI
    have HE:(G).birth (oldKey q)-1-
        ((G).birth (oldKey q)-1-Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderProperRow.labels (rowKey q)) i))=
        Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderProperRow.labels (rowKey q)) i):=by
      have HL:=HG0.1.2 i hi
      omega
    change child q hv ⟨i,hi.trans_le HG0.1.1⟩=field q hv _
    rw [HE]
    simpa only [child,FormulaSignSlotRadialProviderProperRow.labels,atomic,rowKey,pairFst_pair,Fin.val_cast] using HH
  · have HD:=HB.1
    have HH:=child_height q hv HD
      (Fin.cast (congrArg (·+1) (ambient_eq q))
        ⟨WordListRecords.count (FormulaSignSlotRadialProviderProperRow.labels (rowKey q)),by
          have H1:=HG0.2.1
          have H2:=HG0.2.2.1
          have HA:ambient q=(G).ambient (oldKey q):=rfl
          omega⟩)
      (by simp only [Fin.val_cast,coarse_labels_count])
    simpa only [child] using HH

theorem quotients_original (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (φ :((G).state (oldKey q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ :∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=field q hv ((G).birth (oldKey q)-1-i.val)) :
    ∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=originalValue q hv ((G).birth (oldKey q)-1-i.val):=by
  have HV:FormulaSignSlotRadialProviderAtomic.Valid (atomic (rowKey q)):=by
    simpa only [atomic,rowKey,pairFst_pair] using hv
  have HBth:(G).birth (oldKey q)=creating (rowKey q):=by
    with_unfolding_all exact parent_birth_actual false (rowKey q) HV
  intro i
  have HF:=before_probe_field (rowKey q) HV ((G).birth (oldKey q)-1-i.val) (by have HI:=i.isLt;omega)
  have HE:originalValue q hv ((G).birth (oldKey q)-1-i.val)=field q hv ((G).birth (oldKey q)-1-i.val):=by
    simpa only [atomic,rowKey,pairFst_pair,field] using HF
  exact (Hφ i).trans HE.symm

attribute [local irreducible] IntegralMixedSelectedPhysicalFiber.physical

theorem midpoint_physical (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB :FormulaSignSlotRadialProviderProper.Base q)
    (HR :FormulaSignSlotRadialProviderProperRowWitness.RowGood (rowKey q))
    (φ :((G).state (oldKey q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ :∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=field q hv ((G).birth (oldKey q)-1-i.val)) :
    midpoint q hv∈IntegralMixedSelectedPhysicalFiber.physical ((G).state (oldKey q)) ((G).birth_bound _)
      ((G).rule (oldKey q)) φ ((field q hv (producer false q)+field q hv (producer true q))/2):=by
  have HV:FormulaSignSlotRadialProviderAtomic.Valid (atomic (rowKey q)):=by
    simpa only [atomic,rowKey,pairFst_pair] using hv
  have HD:=FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HPos:0<captureCount (D q) q:=by
    unfold captureCount levelIndex
    change 0<D q-(FormulaSignSlotRadialProviderAtomic.depth q-1)
    have HP:=HB.1
    omega
  have HOrig:=quotients_original q hv φ Hφ
  have HF:∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=
      originalValue (atomic (rowKey q)) HV ((G).birth (oldKey q)-1-i.val):=by
    simpa only [atomic,rowKey,pairFst_pair] using HOrig
  have HDepth:0<FormulaSignSlotRadialProviderAtomic.depth (atomic (rowKey q)):=by
    simpa only [atomic,rowKey,pairFst_pair] using HB.1
  have HPos0:0<captureCount (dimension (rowKey q)) (atomic (rowKey q)):=by
    simpa only [dimension,atomic,rowKey,pairFst_pair] using HPos
  let φ0:((G).state (parentKey false (rowKey q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ:=by
    simpa only [oldKey] using φ
  have HF0:∀i,φ0 (((G).state (parentKey false (rowKey q))).bank.numerator i)/
      (((G).state (parentKey false (rowKey q))).bank.denominator i:ℝ)=
      originalValue (atomic (rowKey q)) HV ((G).birth (parentKey false (rowKey q))-1-i.val):=by
    simpa only [φ0,oldKey] using HF
  have HP0:=FormulaSignSlotRadialProviderProperRow.midpoint_capture_physical
    (rowKey q) HV HDepth HR 0 HPos0 φ0 HF0
  have HP:midpointRowCapture (rowKey q) HV 0∈IntegralMixedSelectedPhysicalFiber.physical
      ((G).state (oldKey q)) ((G).birth_bound _) ((G).rule (oldKey q)) φ
      ((originalValue (atomic (rowKey q)) HV (oldProducer false (rowKey q))+
        originalValue (atomic (rowKey q)) HV (oldProducer true (rowKey q)))/2):=by
    simpa only [φ0,oldKey] using HP0
  have HCast:HEq
      (FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
        (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
        (midFirst (D q) (N q) q+0)) (midpointRowCapture (rowKey q) HV 0):=by
    have HE:=atomic_point_heq (atomic (rowKey q)) q HV hv
      (by simp only [atomic,rowKey,pairFst_pair])
      (midFirst (dimension (rowKey q)) (initial (rowKey q)) (atomic (rowKey q))+0)
      (midFirst (D q) (N q) q+0)
      (by simp only [dimension,initial,atomic,rowKey,pairFst_pair])
    exact HE.symm.trans (row_capture_heq (rowKey q) HV 0)
  have HMid:HEq
      (FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
        (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
        (midBirth (D q) (N q) q)) (midpoint q hv):=by
    unfold midpoint
    exact cast_heq (congrArg (·+1) (native_ambient_eq q)) _
  have HPoint:midpointRowCapture (rowKey q) HV 0=midpoint q hv:=
    eq_of_heq (HCast.symm.trans ((heq_of_eq (midpoint_capture_eq q hv HB 0 HPos)).trans HMid))
  have HL:=before_probe_field (rowKey q) HV _ HR.2.2.1
  have HRv:=before_probe_field (rowKey q) HV _ HR.2.2.2.1
  rw [HPoint,HL,HRv] at HP
  simpa only [oldProducer,atomic,rowKey,pairFst_pair,field] using HP

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
