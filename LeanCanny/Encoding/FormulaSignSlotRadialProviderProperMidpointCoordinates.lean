/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
/-! # The actual MID anchor retains frozen fields and the endpoint mean -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderAtomic.Valid FormulaSignSlotRadialProviderAtomic.point
  FormulaSignSlotRadialProviderAtomic.dimension IntegralMixedFramedHistoryFamilyBits.family

theorem midpoint_frozen (q : List Bool) (hv : A q) (HB : FormulaSignSlotRadialProviderProper.Base q)
    (i : Fin (ambient q+1)) (hi : i.val<levelIndex q) :
    midpoint q hv i=field q hv (Nat.fromBitsLE (WordList.get (labels q) i.val)) := by
  have HD := FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HP : 0<FormulaSignSlotRadialProviderAtomic.depth q := HB.1
  have HK : 0<captureCount (D q) q := by
    unfold captureCount levelIndex
    change 0<D q-(FormulaSignSlotRadialProviderAtomic.depth q-1)
    omega
  have HG := FormulaSignSlotRadialProviderProper.midpoint_capture_geometry q hv HP 0 HK
  dsimp only at HG
  rw [midpoint_capture_eq q hv HB 0 HK] at HG
  let j := Fin.cast (congrArg (·+1) (native_ambient_eq q)).symm i
  have HJ : j.val<WordListRecords.count (labels q) := by
    simpa only [j,Fin.val_cast,IntegralMixedRoadmapProper.labels_count] using hi
  have HF := HG.2.1 j.val HJ
  suffices HH : midpoint q hv i=field q hv (Nat.fromBitsLE (WordList.get (labels q) j.val)) by
    simpa only [j,Fin.val_cast] using HH
  apply Eq.trans _ HF
  unfold midpoint
  apply congrArg (FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midBirth (D q) (N q) q))
  apply Fin.ext
  simp only [j,Fin.val_cast]

theorem midpoint_height (q : List Bool) (hv : A q) (HB : FormulaSignSlotRadialProviderProper.Base q)
    (i : Fin (ambient q+1)) (hi : i.val=levelIndex q) :
    midpoint q hv i=(field q hv (producer false q)+field q hv (producer true q))/2 := by
  have HD := FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HP : 0<FormulaSignSlotRadialProviderAtomic.depth q := HB.1
  have HK : 0<captureCount (D q) q := by
    unfold captureCount levelIndex
    change 0<D q-(FormulaSignSlotRadialProviderAtomic.depth q-1)
    omega
  have HG := FormulaSignSlotRadialProviderProper.midpoint_capture_geometry q hv HP 0 HK
  dsimp only at HG
  rw [midpoint_capture_eq q hv HB 0 HK] at HG
  have HH := HG.2.2.1
  apply Eq.trans _ HH
  unfold midpoint
  apply congrArg (FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midBirth (D q) (N q) q))
  apply Fin.ext
  simpa only [Fin.val_cast,IntegralMixedRoadmapProper.labels_count] using hi

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
