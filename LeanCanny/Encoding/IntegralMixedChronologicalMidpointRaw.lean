/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointDecode
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
/-! # Native raw guards construct an actual midpoint point record -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
open LeanCanny.Algebra IntegralMixedHistory
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCriticalRecordConstructor.word

theorem code_descriptor (n birth : ℕ) (w : List Bool)
    (H : IntegralMixedChronologicalFrameCode.Good n birth w) (a b g j : ℕ) :
    code n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H)) a b g j=code n w a b g j :=by
  have HR : IntegralMixedChronologicalFrameCode.rows n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H))=IntegralMixedChronologicalFrameCode.rows n w :=
    congrArg (fun f : ℕ→List Bool=>WordList.encode ((List.range (n+1)).map f))
      (funext fun i=>IntegralMixedChronologicalFrameCode.row_descriptor n birth w H i)
  have HM : midRows n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H)) a b=midRows n w a b :=by
    unfold midRows midRow
    rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length]
  have HD : doubles n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H))=doubles n w :=by
    unfold doubles
    rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length]
  unfold code
  rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length,HR,HM,HD]

theorem raw_fit (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1).labels.length<n+1 :=by
  rw [IntegralMixedChronologicalFrameCode.descriptor_length]
  have HG:=H.2.2.2.1
  have HGN:=H.2.2.2.2.1
  omega

noncomputable def rawFrame (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :=
  IntegralMixedChronologicalMidpoint.frame (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1)
    (raw_fit n birth w a b g j H) ⟨a,H.2.1⟩ ⟨b,H.2.2.1⟩

theorem raw_free_g (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    (⟨g,H.2.2.2.2.1⟩ : Fin (n+1))∉(rawFrame n birth w a b g j H).frozen :=by
  rw [rawFrame,IntegralMixedChronologicalMidpoint.free_iff,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact H.2.2.2.1

theorem raw_free_j (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    (⟨j,H.2.2.2.2.2.2⟩ : Fin (n+1))∉(rawFrame n birth w a b g j H).frozen :=by
  rw [rawFrame,IntegralMixedChronologicalMidpoint.free_iff,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact H.2.2.2.2.2.1

noncomputable def rawData (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    IntegralMixedCriticalRecordConstructor.Data n birth :=
  data (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1) (raw_fit n birth w a b g j H)
    ⟨a,H.2.1⟩ ⟨b,H.2.2.1⟩ ⟨g,H.2.2.2.2.1⟩ ⟨j,H.2.2.2.2.2.2⟩
      (raw_free_g n birth w a b g j H) (raw_free_j n birth w a b g j H)

theorem rawData_code (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    (rawData n birth w a b g j H).code=code n w a b g j :=by
  unfold rawData
  rw [data_code,code_descriptor]

theorem rawData_rule (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    (rawData n birth w a b g j H).rule=
      pointRule (rawFrame n birth w a b g j H) ⟨g,H.2.2.2.2.1⟩ (raw_free_g n birth w a b g j H)
        ⟨j,H.2.2.2.2.2.2⟩ (raw_free_j n birth w a b g j H) :=
  data_rule _ _ _ _ _ _ _ _

theorem raw_command {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n w a b g j) hcap).template.command Q hQ=
      .critical (rawData n birth w a b g j H).rule :=by
  rw [←rawData_code n birth w a b g j H]
  exact IntegralMixedCriticalRecordConstructor.command_decode P hn _ hcap Q hQ

theorem raw_code_size (n birth : ℕ) (w : List Bool) (a b g j : ℕ) (H : Good n birth w a b g j) :
    (code n w a b g j).length≤IntegralMixedCriticalRecordConstructor.codeBudget n birth :=by
  rw [←rawData_code n birth w a b g j H]
  exact IntegralMixedCriticalRecordConstructor.Data.code_length _

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
