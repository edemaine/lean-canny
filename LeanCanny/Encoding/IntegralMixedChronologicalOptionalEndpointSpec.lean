/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalEndpointSpec

/-! # Optional endpoints keep their original producer labels across fresh births -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedChronologicalFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def retainedSpec (_d : Descriptor n birth) (i : Fin birth) :=spec 0 (birth-1-i.val) 0 0 0 0

theorem retainedSpec_good (d : Descriptor n birth) (i : Fin birth) (B sourceCap current : ℕ) :
    Good n B sourceCap birth current (IntegralMixedChronologicalFrameCode.labels d) (retainedSpec d i) :=by
  refine ⟨(canonical_spec _ _ _ _ _ _).symm,Or.inl ?_⟩
  have HI:=i.isLt
  simpa only [retainedSpec,field_spec_0,field_spec_1,field_spec_2,field_spec_3,field_spec_4,field_spec_5,
    eq_self_iff_true,true_and,and_true] using (show birth-1-i.val<birth by omega)

theorem retainedSpec_fresh (d : Descriptor n birth) (i : Fin birth) : fresh (retainedSpec d i)=0 :=by
  simp only [fresh,retainedSpec,field_spec_0,ite_true]

theorem retainedSpec_codes (d : Descriptor n birth) (i : Fin birth) :
    codes n (IntegralMixedChronologicalFrameCode.labels d) (retainedSpec d i)=[] :=by
  simp only [codes,retainedSpec,field_spec_0,ite_true]

theorem retainedSpec_producer (d : Descriptor n birth) (i : Fin birth) :
    field (retainedSpec d i) 1=birth-1-i.val :=field_spec_1 _ _ _ _ _ _

/-- Changing the old-bank bound cannot affect a fresh branch. In particular a
fresh RIGHT keeps the original oldBirth even after a LEFT was appended. -/
theorem Good.fresh_oldBirth {B sourceCap oldBirth current : ℕ} {labels s : List Bool}
    (H : Good n B sourceCap oldBirth current labels s) (hk : field s 0≠0) (old : ℕ) :
    Good n B sourceCap old current labels s :=by
  refine ⟨H.1,?_⟩
  rcases H.2 with HR|HC|HC
  · exact (hk HR.1).elim
  · exact Or.inr (Or.inl HC)
  · exact Or.inr (Or.inr HC)

theorem fresh_eq_one {s : List Bool} (hk : field s 0≠0) : fresh s=1 :=ite_eq_right hk

end LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
