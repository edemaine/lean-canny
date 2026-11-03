/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
/-! # Checked raw labels yield the actual prefix-frame point command

All raw producer and coordinate bounds are native polynomial-time checks.
Successful checks construct the semantic frame and identify the exact
critical command emitted by the existing decoder at its actual current Q.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def descriptor (n birth : ℕ) (w : List Bool) (H : Good n birth w) :
    IntegralMixedChronologicalFrame.Descriptor n birth where
  labels:=List.ofFn (fun i : Fin (WordListRecords.count w)=>
    ⟨Nat.fromBitsLE (WordList.get w i.val),H.2 i.val i.isLt⟩)
  length_le:=by simpa only [List.length_ofFn] using H.1

theorem descriptor_length (n birth : ℕ) (w : List Bool) (H : Good n birth w) :
    (descriptor n birth w H).labels.length=WordListRecords.count w:=List.length_ofFn

theorem descriptor_lookup (n birth : ℕ) (w : List Bool) (H : Good n birth w)
    (i : ℕ) (hi : i<WordListRecords.count w) :
    Nat.fromBitsLE (WordList.get (labels (descriptor n birth w H)) i)=Nat.fromBitsLE (WordList.get w i) :=by
  rw [labels_lookup _ i (by rw [descriptor_length];exact hi)]
  simp only [descriptor,List.get_eq_getElem,List.getElem_ofFn]

theorem row_descriptor (n birth : ℕ) (w : List Bool) (H : Good n birth w) (i : ℕ) :
    row (labels (descriptor n birth w H)) i=row w i :=by
  unfold row
  rw [labels_count,descriptor_length]
  split_ifs with hi
  · rw [descriptor_lookup n birth w H i hi]
  · rfl

theorem code_descriptor (n birth : ℕ) (w : List Bool) (H : Good n birth w) (g j : ℕ) :
    code n (labels (descriptor n birth w H)) g j=code n w g j :=by
  unfold code
  rw [labels_count,descriptor_length]
  have HE : rows n (labels (descriptor n birth w H))=rows n w:=by
    unfold rows
    apply congrArg WordList.encode
    apply List.map_congr_left
    intro i _
    exact row_descriptor n birth w H i
  rw [HE]

def PointGood (n birth : ℕ) (w : List Bool) (g j : ℕ) : Prop :=
  Good n birth w ∧ WordListRecords.count w≤g ∧ g<n+1 ∧ WordListRecords.count w≤j ∧ j<n+1

theorem pointGood_FP {n birth g j : List Bool→ℕ} {w : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (hg : BinaryFn g) (hj : BinaryFn j) (hw : w∈FP) :
    FPPred (fun q=>PointGood (n q) (birth q) (w q) (g q) (j q)) :=by
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)
  have HD:=BinaryFn.ofUnary (hn.add (UnaryFn.const 1))
  exact (good_FP hn hb hw).and ((HK.le hg).and ((hg.lt HD).and ((HK.le hj).and (hj.lt HD))))

noncomputable def rawData (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : PointGood n birth w g j) :
    IntegralMixedCriticalRecordConstructor.Data n birth :=
  data (descriptor n birth w H.1) ⟨g,H.2.2.1⟩ ⟨j,H.2.2.2.2⟩
    (by rw [(descriptor n birth w H.1).frozen_mem,descriptor_length];exact Nat.not_lt_of_ge H.2.1)
    (by rw [(descriptor n birth w H.1).frozen_mem,descriptor_length];exact Nat.not_lt_of_ge H.2.2.2.1)

theorem rawData_code (n birth : ℕ) (w : List Bool) (g j : ℕ) (H : PointGood n birth w g j) :
    (rawData n birth w g j H).code=code n w g j :=by
  unfold rawData
  rw [data_code,code_descriptor]

theorem raw_command {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (w : List Bool) (g j : ℕ) (H : PointGood n birth w g j)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n w g j) hcap).template.command Q hQ=
      .critical (rawData n birth w g j H).rule :=by
  rw [←rawData_code n birth w g j H]
  exact IntegralMixedCriticalRecordConstructor.command_decode P hn _ hcap Q hQ

end LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
