/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
/-! # Exact source-cap modulo readback of arbitrary stored cut degrees

Soundness does not assume that a raw hint degree is already within the
source cap.  The actual decoder reduces it modulo cap+1.  The rule, kind,
current-Q bit and all original affine rows remain those of the typed word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCutRecordConstructor
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 def degreeResidue {n : ℕ} (P : SpatialSource n) (d : ℕ):=
 d%(IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree+1)

theorem degreeResidue_le {n : ℕ} (P : SpatialSource n) (d : ℕ) :
    degreeResidue P d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree:=
 Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

theorem writtenDegree_mod {n birth : ℕ} (d : Data n birth) (P : SpatialSource n)
    (tag : Tag) (choice rawDegree : ℕ) :
    IntegralMixedCanonicalUnitRuleBits.writtenDegree P (d.code tag choice rawDegree)=degreeResidue P rawDegree:=by
 unfold IntegralMixedCanonicalUnitRuleBits.writtenDegree Data.code
 rw [IntegralMixedCausalRecordDegree.field_withDegree _ _ 9 (by decide)]
 simp only [ite_true,BinaryNatCode.encode,Nat.fromBitsLE_bits]
 rfl

theorem cut_decode_mod {n birth B : ℕ} (d : Data n birth) (P : SpatialSource n) (tag : Tag)
    (choice rawDegree : ℕ) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    IntegralMixedCausalUnitRecordBits.cut P d.ambient_positive birth (d.code tag choice rawDegree) hcap=
      d.cut P tag choice (degreeResidue P rawDegree) (degreeResidue_le P rawDegree) hcap:=by
 have HT : IntegralMixedCausalUnitRecordBits.tag (d.code tag choice rawDegree)=tag:=by
   simp only [IntegralMixedCausalUnitRecordBits.tag,field_11,BinaryNatCode.encode,Nat.fromBitsLE_bits]
   cases tag <;>rfl
 simp only [IntegralMixedCausalUnitRecordBits.cut,virtual_critical,virtual_height,HT,
   IntegralMixedCausalUnitRecordBits.current,field_10,List.getElem?_cons_zero,Option.getD_some,
   field_4,field_8,BinaryNatCode.encode,Nat.fromBitsLE_bits,writtenDegree_mod,Data.cut]

theorem command_decode_mod {n birth B : ℕ} (d : Data n birth) (P : SpatialSource n) (hn : 0<n)
    (tag : Tag) (choice rawDegree : ℕ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (d.code tag choice rawDegree) hcap).template.command Q hQ=
      .cut (d.rule Q hQ)
        ((d.cut P tag choice (degreeResidue P rawDegree) (degreeResidue_le P rawDegree) hcap).kind Q hQ)
        (degreeResidue P rawDegree) (degreeResidue_le P rawDegree) ((degreeResidue_le P rawDegree).trans hcap):=by
 simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,field_0,
   show ([] : List Bool)[0]?.getD false=false from rfl,Bool.false_eq_true,ite_false,Template.command]
 rw [cut_decode_mod]
 rfl

end LeanCanny.Encoding.IntegralMixedCutRecordConstructor

namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem raw_command_mod {n B birth : ℕ} (P : SpatialSource n) (hn : 0<n)
    (w : List Bool) (g j tag choice degree : ℕ) (H : Good n birth w g j) (ht : tag≤2)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n w g j tag choice degree) hcap).template.command Q hQ=
      .cut ((rawData n birth w g j H).rule Q hQ)
        (((rawData n birth w g j H).cut P (ordinaryTag tag) choice
          (IntegralMixedCutRecordConstructor.degreeResidue P degree)
          (IntegralMixedCutRecordConstructor.degreeResidue_le P degree) hcap).kind Q hQ)
        (IntegralMixedCutRecordConstructor.degreeResidue P degree)
        (IntegralMixedCutRecordConstructor.degreeResidue_le P degree)
        ((IntegralMixedCutRecordConstructor.degreeResidue_le P degree).trans hcap):=by
 rw [←rawData_code n birth w g j H tag choice degree ht]
 exact IntegralMixedCutRecordConstructor.command_decode_mod _ P hn _ _ _ hcap Q hQ

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode
