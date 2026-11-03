/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
public import LeanCanny.Geometry.IntegralMixedChronologicalFrameRetained

/-! # Canonical fresh endpoint specifications at the actual chronological birth -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory
open IntegralMixedChronologicalFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

@[simp] theorem field_spec_0 (a b c d e f : ℕ) : field (spec a b c d e f) 0=a :=by
  simp [field,spec,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]
@[simp] theorem field_spec_1 (a b c d e f : ℕ) : field (spec a b c d e f) 1=b :=by
  simp [field,spec,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]
@[simp] theorem field_spec_2 (a b c d e f : ℕ) : field (spec a b c d e f) 2=c :=by
  simp [field,spec,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]
@[simp] theorem field_spec_3 (a b c d e f : ℕ) : field (spec a b c d e f) 3=d :=by
  simp [field,spec,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]
@[simp] theorem field_spec_4 (a b c d e f : ℕ) : field (spec a b c d e f) 4=e :=by
  simp [field,spec,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]
@[simp] theorem field_spec_5 (a b c d e f : ℕ) : field (spec a b c d e f) 5=f :=by
  simp [field,spec,WordList.get_encode,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem canonical_spec (a b c d e f : ℕ) : canonical (spec a b c d e f)=spec a b c d e f :=by
  simp only [canonical,field_spec_0,field_spec_1,field_spec_2,field_spec_3,field_spec_4,field_spec_5]

def criticalSpec (d : Descriptor n birth) :=spec 1 birth d.labels.length 0 0 0
def cutSpec (_d : Descriptor n birth) (coordinate tag choice degree : ℕ) :=
  spec 2 birth coordinate tag choice degree

theorem criticalSpec_good (d : Descriptor n birth) (B sourceCap oldBirth : ℕ) :
    Good n B sourceCap oldBirth birth (IntegralMixedChronologicalFrameCode.labels d) (criticalSpec d) :=by
  refine ⟨(canonical_spec _ _ _ _ _ _).symm,Or.inr (Or.inl ?_)⟩
  simp only [criticalSpec,field_spec_0,field_spec_1,field_spec_2,field_spec_3,field_spec_4,field_spec_5,
    IntegralMixedChronologicalFrameCode.labels_count,and_self]

theorem cutSpec_good (d : Descriptor n birth) (B sourceCap oldBirth coordinate tag choice degree : ℕ)
    (H : IntegralMixedChronologicalCutCode.Bounds n birth B sourceCap
      (IntegralMixedChronologicalFrameCode.labels d) (d.labels.length+1) coordinate tag choice degree) :
    Good n B sourceCap oldBirth birth (IntegralMixedChronologicalFrameCode.labels d)
      (cutSpec d coordinate tag choice degree) :=by
  refine ⟨(canonical_spec _ _ _ _ _ _).symm,Or.inr (Or.inr ?_)⟩
  simpa only [cutSpec,field_spec_0,field_spec_1,field_spec_2,field_spec_3,field_spec_4,field_spec_5,
    IntegralMixedChronologicalFrameCode.labels_count,true_and] using H

theorem criticalSpec_code (d : Descriptor n birth) :
    code n (IntegralMixedChronologicalFrameCode.labels d) (criticalSpec d)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        d.labels.length d.labels.length :=by
  simp only [code,criticalSpec,field_spec_0,ite_true,IntegralMixedChronologicalFrameCode.labels_count]

theorem cutSpec_code (d : Descriptor n birth) (coordinate tag choice degree : ℕ) :
    code n (IntegralMixedChronologicalFrameCode.labels d) (cutSpec d coordinate tag choice degree)=
      IntegralMixedChronologicalCutCode.code n (IntegralMixedChronologicalFrameCode.labels d)
        (d.labels.length+1) coordinate tag choice degree :=by
  simp only [code,cutSpec,field_spec_0,show (2:ℕ)≠1 by decide,ite_false,field_spec_2,field_spec_3,
    field_spec_4,field_spec_5,IntegralMixedChronologicalFrameCode.labels_count]

theorem freshSpec_codes (d : Descriptor n birth) (kind coordinate tag choice degree : ℕ) (hk : kind≠0) :
    codes n (IntegralMixedChronologicalFrameCode.labels d) (spec kind birth coordinate tag choice degree)=
      [code n (IntegralMixedChronologicalFrameCode.labels d) (spec kind birth coordinate tag choice degree)] :=by
  simp only [codes,field_spec_0,ite_eq_right hk]

theorem labels_retain (d : Descriptor n birth) :
    IntegralMixedChronologicalFrameCode.labels d.retain=IntegralMixedChronologicalFrameCode.labels d :=by
  simp only [IntegralMixedChronologicalFrameCode.labels,Descriptor.retain,List.map_map,
    Function.comp_def,Fin.val_castSucc]

end LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
