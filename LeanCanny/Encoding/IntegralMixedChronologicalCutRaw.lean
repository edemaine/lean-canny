/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutActual
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
/-! # Checked raw producers and ordinary cut fields construct the actual command

Only the three ordinary bad-cut tags are accepted. In particular the fourth
limit-coordinate ABI is not silently included. Specialized degrees remain
stored data checked against the original source cap.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralMixedHistory
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCutRecordConstructor.word IntegralMixedCausalRecordDegree.withDegree

theorem code_descriptor (n birth : ℕ) (w : List Bool) (H : IntegralMixedChronologicalFrameCode.Good n birth w)
    (g j tag choice degree : ℕ) :
    code n (IntegralMixedChronologicalFrameCode.labels (IntegralMixedChronologicalFrameCode.descriptor n birth w H))
      g j tag choice degree=code n w g j tag choice degree :=by
  have HR : IntegralMixedChronologicalFrameCode.rows n
      (IntegralMixedChronologicalFrameCode.labels (IntegralMixedChronologicalFrameCode.descriptor n birth w H))=
      IntegralMixedChronologicalFrameCode.rows n w:=by
    unfold IntegralMixedChronologicalFrameCode.rows
    apply congrArg WordList.encode
    apply List.map_congr_left
    intro i _
    exact IntegralMixedChronologicalFrameCode.row_descriptor n birth w H i
  unfold code
  rw [IntegralMixedChronologicalFrameCode.labels_count,IntegralMixedChronologicalFrameCode.descriptor_length,HR]

theorem raw_fit (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : Good n birth w g j) :
    (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1).labels.length<n+1 :=by
  rw [IntegralMixedChronologicalFrameCode.descriptor_length]
  have HG:=H.2.1
  have HN:=H.2.2.1
  omega

theorem raw_free_g (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : Good n birth w g j) :
    (⟨g,H.2.2.1⟩ : Fin (n+1))∉
      (frame (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1) (raw_fit n birth w g j H)).frozen :=by
  rw [free_iff,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact H.2.1

theorem raw_free_j (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : Good n birth w g j) :
    (⟨j,H.2.2.2.2⟩ : Fin (n+1))∉
      (frame (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1) (raw_fit n birth w g j H)).frozen :=by
  rw [free_iff,IntegralMixedChronologicalFrameCode.descriptor_length]
  exact H.2.2.2.1

noncomputable def rawData (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : Good n birth w g j) :=
  data (IntegralMixedChronologicalFrameCode.descriptor n birth w H.1) (raw_fit n birth w g j H)
    ⟨g,H.2.2.1⟩ ⟨j,H.2.2.2.2⟩ (raw_free_g n birth w g j H) (raw_free_j n birth w g j H)

def ordinaryTag (tag : ℕ) : Tag:=if tag=0 then .coordinate else if tag=1 then .squarefree else .value

theorem ordinaryTag_index (tag : ℕ) (ht : tag≤2) :
    IntegralMixedCutRecordConstructor.tagIndex (ordinaryTag tag)=tag :=by
  interval_cases tag <;> rfl

def Bounds (n birth B sourceCap : ℕ) (w : List Bool) (g j tag choice degree : ℕ) :=
  Good n birth w g j ∧ tag≤2 ∧ choice≤2^B ∧ degree≤sourceCap

theorem bounds_FP {n birth B sourceCap g j tag choice degree : List Bool→ℕ} {w : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (hB : UnaryFn B) (hcap : BinaryFn sourceCap)
    (hg : BinaryFn g) (hj : BinaryFn j) (ht : BinaryFn tag) (hc : BinaryFn choice)
    (hd : BinaryFn degree) (hw : w∈FP) :
    FPPred (fun q=>Bounds (n q) (birth q) (B q) (sourceCap q) (w q) (g q) (j q) (tag q) (choice q) (degree q)) :=
  (good_FP hn hb hg hj hw).and ((ht.le (BinaryFn.const 2)).and
    ((hc.le ((BinaryFn.const 2).powUnary hB)).and (hd.le hcap)))

theorem rawData_code (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : Good n birth w g j)
    (tag choice degree : ℕ) (ht : tag≤2) :
    (rawData n birth w g j H).code (ordinaryTag tag) choice degree=code n w g j tag choice degree :=by
  unfold rawData
  rw [data_code,code_descriptor,ordinaryTag_index tag ht]

theorem raw_command {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (w : List Bool) (g j tag choice degree : ℕ) (H : Good n birth w g j) (ht : tag≤2)
    (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n w g j tag choice degree) hcap).template.command Q hQ=
      .cut ((rawData n birth w g j H).rule Q hQ)
        (((rawData n birth w g j H).cut P (ordinaryTag tag) choice degree hd hcap).kind Q hQ)
        degree hd (hd.trans hcap) :=by
  rw [←rawData_code n birth w g j H tag choice degree ht]
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,
    IntegralMixedCutRecordConstructor.field_0,show ([] : List Bool)[0]?.getD false=false from rfl,
    Bool.false_eq_true,ite_false,Template.command]
  rw [IntegralMixedCutRecordConstructor.cut_decode]
  rfl

theorem raw_code_size (n birth B : ℕ) (w : List Bool) (g j tag choice degree : ℕ)
    (H : Good n birth w g j) (ht : tag≤2) (hc : choice≤2^B) (hd : degree≤2^B) :
    (code n w g j tag choice degree).length≤IntegralMixedCutRecordConstructor.codeBudget n birth B :=by
  rw [←rawData_code n birth w g j H tag choice degree ht]
  exact IntegralMixedCutRecordConstructor.Data.code_length _ (ordinaryTag tag) choice degree hc hd

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode
