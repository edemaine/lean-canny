/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMeanCutActual
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointRaw
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
/-! # Guarded raw mean-cut bytes construct the same literal cut data -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCutRecordConstructor.word IntegralMixedCausalRecordDegree.withDegree

theorem code_descriptor (n birth : ℕ) (w : List Bool)
    (H : IntegralMixedChronologicalFrameCode.Good n birth w) (a b g j tag choice degree : ℕ) :
    code n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H)) a b g j tag choice degree=
      code n w a b g j tag choice degree:=by
  have HR : IntegralMixedChronologicalFrameCode.rows n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H))=IntegralMixedChronologicalFrameCode.rows n w:=
    congrArg (fun f : ℕ→List Bool=>WordList.encode ((List.range (n+1)).map f))
      (funext fun i=>IntegralMixedChronologicalFrameCode.row_descriptor n birth w H i)
  have HM : IntegralMixedChronologicalMidpointCode.midRows n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H)) a b=
      IntegralMixedChronologicalMidpointCode.midRows n w a b:=by
    unfold IntegralMixedChronologicalMidpointCode.midRows IntegralMixedChronologicalMidpointCode.midRow
    rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length]
  have HD : IntegralMixedChronologicalMidpointCode.doubles n (IntegralMixedChronologicalFrameCode.labels
      (IntegralMixedChronologicalFrameCode.descriptor n birth w H))=
      IntegralMixedChronologicalMidpointCode.doubles n w:=by
    unfold IntegralMixedChronologicalMidpointCode.doubles
    rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length]
  unfold code
  rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length,HR,HM,HD]

noncomputable def rawData (n birth : ℕ) (w : List Bool) (a b g j : ℕ)
    (H : IntegralMixedChronologicalMidpointCode.Good n birth w a b g j):=
  IntegralMixedChronologicalMeanCut.data
    (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1)
    (IntegralMixedChronologicalMidpointCode.raw_fit n birth w a b g j H)
    ⟨a,H.2.1⟩ ⟨b,H.2.2.1⟩ ⟨g,H.2.2.2.2.1⟩ ⟨j,H.2.2.2.2.2.2⟩
    (IntegralMixedChronologicalMidpointCode.raw_free_g n birth w a b g j H)
    (IntegralMixedChronologicalMidpointCode.raw_free_j n birth w a b g j H)

def Bounds (n birth B sourceCap : ℕ) (w : List Bool) (a b g j tag choice degree : ℕ):=
  IntegralMixedChronologicalMidpointCode.Good n birth w a b g j ∧
    tag≤2 ∧ choice≤2^B ∧ degree≤sourceCap

theorem bounds_FP {n birth B sourceCap a b g j tag choice degree : List Bool→ℕ} {w : List Bool→List Bool}
    (hn : UnaryFn n) (hm : BinaryFn birth) (hB : UnaryFn B) (hcap : BinaryFn sourceCap)
    (ha : BinaryFn a) (hb : BinaryFn b) (hg : BinaryFn g) (hj : BinaryFn j)
    (ht : BinaryFn tag) (hc : BinaryFn choice) (hd : BinaryFn degree) (hw : w∈FP) :
    FPPred (fun q=>Bounds (n q) (birth q) (B q) (sourceCap q) (w q)
      (a q) (b q) (g q) (j q) (tag q) (choice q) (degree q)):=
  (IntegralMixedChronologicalMidpointCode.good_FP hn hm ha hb hg hj hw).and
    ((ht.le (BinaryFn.const 2)).and ((hc.le ((BinaryFn.const 2).powUnary hB)).and (hd.le hcap)))

theorem rawData_code (n birth : ℕ) (w : List Bool) (a b g j : ℕ)
    (H : IntegralMixedChronologicalMidpointCode.Good n birth w a b g j)
    (tag : Tag) (choice degree : ℕ) :
    (rawData n birth w a b g j H).code tag choice degree=
      code n w a b g j (IntegralMixedCutRecordConstructor.tagIndex tag) choice degree:=by
  unfold rawData
  rw [data_code,code_descriptor]

theorem raw_command {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (w : List Bool) (a b g j tag choice degree : ℕ)
    (H : IntegralMixedChronologicalMidpointCode.Good n birth w a b g j) (ht : tag≤2)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n w a b g j tag choice degree) hcap).template.command Q hQ=
      .cut ((rawData n birth w a b g j H).rule Q hQ)
        (((rawData n birth w a b g j H).cut P (IntegralMixedChronologicalCutCode.ordinaryTag tag)
          choice degree hd hcap).kind Q hQ) degree hd (hd.trans hcap):=by
  have HC:=rawData_code n birth w a b g j H (IntegralMixedChronologicalCutCode.ordinaryTag tag) choice degree
  rw [IntegralMixedChronologicalCutCode.ordinaryTag_index tag ht] at HC
  rw [←HC]
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,
    IntegralMixedCutRecordConstructor.field_0,show ([] : List Bool)[0]?.getD false=false from rfl,
    Bool.false_eq_true,ite_false,Template.command]
  rw [IntegralMixedCutRecordConstructor.cut_decode]
  rfl

end LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode
