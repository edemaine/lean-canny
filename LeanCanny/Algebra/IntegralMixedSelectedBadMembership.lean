/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSelectedBadChoiceUnique
public import LeanCanny.Algebra.IntegralMixedSweepRetargetRealization
public import LeanCanny.Encoding.IntegralMixedCutRecordConstructor
/-! # Membership in the ordinary bad set uses exactly a valid actual factor

Valid native choices need not reproduce a separate classical Choices object.
Uniqueness of the first nonzero selected coefficient identifies the chosen
factor with the corresponding member of that object.  Limit-coordinate cuts
are excluded by their actual fourth ABI tag.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSelectedBadMembership
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
open LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open IntegralMixedCurrentQCoordinateScaling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def Ordinary (r : Rule n) (c : Kind P r) : Prop:=
 LeanCanny.Encoding.IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)<3

theorem selected_ordinary (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ) (j : Tag r) :
    Ordinary r (kind x hm r φ c j):=by
 rcases j with ⟨tag,j⟩
 fin_cases tag <;> norm_num [Ordinary,kind,IntegralMixedSweepRetarget.tag,
   LeanCanny.Encoding.IntegralMixedCutRecordConstructor.tagIndex]

theorem valid_kind_selected (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ) (k : Kind P r)
    (hk : Valid x hm r φ k) (ho : Ordinary r k) : ∃j : Tag r,kind x hm r φ c j=k:=by
 cases k with
 | coordinate j i=>
   have HE:=coordinate_index_unique x hm r j φ _ _ (c.coordinateValid j) hk
   exact ⟨(0,j),congrArg (Kind.coordinate j) HE⟩
 | squarefree j i=>
   have HE:=squarefree_index_unique x hm r j φ _ _ (c.squarefreeValid j) hk
   exact ⟨(1,j),congrArg (Kind.squarefree j) HE⟩
 | value j i=>
   have HE:=value_index_unique x hm r j φ _ _ (c.valueValid j) hk
   exact ⟨(2,j),congrArg (Kind.value j) HE⟩
 | limitCoordinate j i=>
   exact False.elim (Nat.lt_irrefl 3 ho)

theorem mem_bad_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ) (a : ℝ) :
    a∈bad x hm r φ c ↔ ∃k : Kind P r,Valid x hm r φ k ∧ Ordinary r k ∧
      (factor x hm r k).eval₂ φ.toRingHom a=0:=by
 constructor
 · rintro ⟨j,Hj⟩
   exact ⟨kind x hm r φ c j,kind_valid x hm r φ c j,selected_ordinary x hm r φ c j,Hj⟩
 · rintro ⟨k,hk,ho,ha⟩
   obtain ⟨j,hj⟩:=valid_kind_selected x hm r φ c k hk ho
   exact ⟨j,by change (factor x hm r (kind x hm r φ c j)).eval₂ φ.toRingHom a=0;rw [hj];exact ha⟩

theorem exists_bad_in_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ) (a b : ℝ) :
    (∃u∈Set.Ioo a b,u∈bad x hm r φ c) ↔
      ∃k : Kind P r,Valid x hm r φ k ∧ Ordinary r k ∧
        ∃u∈Set.Ioo a b,(factor x hm r k).eval₂ φ.toRingHom u=0:=by
 constructor
 · rintro ⟨u,hu,H⟩
   obtain ⟨k,hk,ho,Hk⟩:=(mem_bad_iff x hm r φ c u).mp H
   exact ⟨k,hk,ho,u,hu,Hk⟩
 · rintro ⟨k,hk,ho,u,hu,Hk⟩
   exact ⟨u,hu,(mem_bad_iff x hm r φ c u).mpr ⟨k,hk,ho,Hk⟩⟩

end LeanCanny.Algebra.IntegralMixedSelectedBadMembership
