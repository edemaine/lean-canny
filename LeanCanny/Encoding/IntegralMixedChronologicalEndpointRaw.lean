/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalEndpointActual
/-! # Checked endpoint inputs compile the literal recursive frozen child -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalEndpointCode
open LeanCanny.Algebra IntegralMixedHistory
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCriticalRecordConstructor.word

theorem entry_descriptor (n birth : ℕ) (w : List Bool)
    (H : IntegralMixedChronologicalFrameCode.Good n birth w) (a i : ℕ) :
    entry (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H)) a i=entry w a i :=by
  unfold entry
  rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length]
  split_ifs with hi
  · rw [IntegralMixedChronologicalFrameCode.descriptor_lookup n birth w H i hi]
  · rfl

theorem append_normalize (n birth : ℕ) (w : List Bool)
    (H : IntegralMixedChronologicalFrameCode.Good n birth w) (a : ℕ) :
    appendLabels (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H)) a=appendLabels w a :=by
  unfold appendLabels
  rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact congrArg (fun f : ℕ→List Bool=>WordList.encode ((List.range (WordListRecords.count w+1)).map f))
    (funext fun i=>entry_descriptor n birth w H a i)

theorem append_descriptor (n birth : ℕ) (w : List Bool)
    (H : IntegralMixedChronologicalFrameCode.Good n birth w) (a : Fin birth)
    (hk : (IntegralMixedChronologicalFrameCode.descriptor n birth w H).labels.length<n+1) :
    appendLabels w a.val=IntegralMixedChronologicalFrameCode.labels
      ((IntegralMixedChronologicalFrameCode.descriptor n birth w H).freeze a hk) :=by
  rw [←append_normalize n birth w H a.val]
  exact append_actual _ a hk

noncomputable def rawChild (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    IntegralMixedChronologicalFrame.Descriptor n birth :=
  (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1.1).freeze ⟨a,H.1.2.2⟩
    (by rw [IntegralMixedChronologicalFrameCode.descriptor_length];exact H.1.2.1)

theorem rawChild_labels (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    IntegralMixedChronologicalFrameCode.labels (rawChild n birth w a g j H)=appendLabels w a :=
  (append_descriptor n birth w H.1.1 ⟨a,H.1.2.2⟩ _).symm

theorem raw_free_g (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    (⟨g,H.2.2.1⟩ : Fin (n+1))∉(rawChild n birth w a g j H).frame.frozen :=by
  rw [(rawChild n birth w a g j H).frozen_mem]
  change ¬g<((IntegralMixedChronologicalFrameCode.descriptor n birth w H.1.1).freeze ⟨a,H.1.2.2⟩ _).labels.length
  rw [IntegralMixedChronologicalFrame.Descriptor.freeze_length,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact Nat.not_lt.mpr H.2.1

theorem raw_free_j (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    (⟨j,H.2.2.2.2⟩ : Fin (n+1))∉(rawChild n birth w a g j H).frame.frozen :=by
  rw [(rawChild n birth w a g j H).frozen_mem]
  change ¬j<((IntegralMixedChronologicalFrameCode.descriptor n birth w H.1.1).freeze ⟨a,H.1.2.2⟩ _).labels.length
  rw [IntegralMixedChronologicalFrame.Descriptor.freeze_length,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact Nat.not_lt.mpr H.2.2.2.1

noncomputable def rawData (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    IntegralMixedCriticalRecordConstructor.Data n birth :=
  IntegralMixedChronologicalFrameCode.data (rawChild n birth w a g j H)
    ⟨g,H.2.2.1⟩ ⟨j,H.2.2.2.2⟩ (raw_free_g n birth w a g j H) (raw_free_j n birth w a g j H)

theorem rawData_code (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    (rawData n birth w a g j H).code=code n w a g j :=by
  unfold rawData
  rw [IntegralMixedChronologicalFrameCode.data_code,rawChild_labels]
  rfl

theorem rawData_rule (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    (rawData n birth w a g j H).rule=pointRule (rawChild n birth w a g j H).frame
      ⟨g,H.2.2.1⟩ (raw_free_g n birth w a g j H) ⟨j,H.2.2.2.2⟩ (raw_free_j n birth w a g j H) :=
  IntegralMixedChronologicalFrameCode.data_rule _ _ _ _ _

theorem raw_command {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n w a g j) hcap).template.command Q hQ=
      .critical (rawData n birth w a g j H).rule :=by
  rw [←rawData_code n birth w a g j H]
  exact IntegralMixedCriticalRecordConstructor.command_decode P hn _ hcap Q hQ

theorem raw_code_size (n birth : ℕ) (w : List Bool) (a g j : ℕ) (H : PointGood n birth w a g j) :
    (code n w a g j).length≤IntegralMixedCriticalRecordConstructor.codeBudget n birth :=by
  rw [←rawData_code n birth w a g j H]
  exact IntegralMixedCriticalRecordConstructor.Data.code_length _

end LeanCanny.Encoding.IntegralMixedChronologicalEndpointCode
