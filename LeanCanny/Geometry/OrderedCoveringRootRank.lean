/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.RootCurveOrder
public import LeanCanny.Geometry.FiniteImageRank
/-! # Ordered real-root ranks persist under an actual scalar covering

The complete scalar fiber, including roots unused by a physical system,
provides the rank. A validated continuous root follows one anchored branch.
No enumeration or native root-cost premise is inferred from this theorem.
-/
@[expose] public section
namespace LeanCanny.Geometry.OrderedCoveringRootRank
open Set RootBranches
open scoped Classical

noncomputable def rank {a b : ℝ} (roots : Ioo a b→Finset ℝ) (t : Ioo a b) (v : ℝ) :=
  ((roots t).filter (fun u=>u<v)).card

theorem constant (H : ℝ×(Fin 1→ℝ)→(Fin 1→ℝ)) {a b : ℝ}
    (hcover : IsCoveringMap (RootBranches.projection H a b))
    (roots : Ioo a b→Finset ℝ) (hroot : ∀ t (v : Fin 1→ℝ),H (t.val,v)=0↔v 0∈roots t)
    (f : C(Ioo a b,Fin 1→ℝ)) (hf : ∀ t,H (t.val,f t)=0) (s t : Ioo a b) :
    rank roots s (f s 0)=rank roots t (f t 0) := by
  let J:=RootBranches.Index H a b s
  have HP (j : J) : j.val.val.val.1=s.val:=congrArg Subtype.val j.property
  let point (j : J) : ℝ:=j.val.val.val.2 0
  have HM (j : J) : point j∈roots s := by
    apply (hroot s _).mp
    have HZ:=j.val.val.property
    change H (j.val.val.val.1,j.val.val.val.2)=0 at HZ
    rw [HP j] at HZ
    exact HZ
  have HI : Function.Injective point := by
    intro j k h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (HP j).trans (HP k).symm
    · funext i
      have HE : i=0:=Subsingleton.elim _ _
      simpa only [HE] using h
  let encode (j : J) : roots s:=⟨point j,HM j⟩
  let : Finite J:=Finite.of_injective encode (fun j k h=>HI (congrArg Subtype.val h))
  let :=Fintype.ofFinite J
  let :=LinearOrder.lift' point HI
  obtain ⟨curve,_,HR,HE⟩:=RootBranches.exists_anchored_branches_of_covering H a b s hcover
  obtain ⟨j,Hj,_⟩:=(HE s (f s)).mp (hf s)
  have Hfollow (u : Ioo a b) : curve j u=f u :=
    (RootBranches.curves_eq_iff H hcover (curve j) f (HR j) hf s u).mp Hj
  have Himage (u : Ioo a b) : Finset.univ.image (fun j:J=>curve j u 0)=roots u := by
    ext v
    constructor
    · rintro hv
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
      exact (hroot u _).mp (HR k u)
    · intro hv
      have HZ : H (u.val,fun _=>v)=0:=(hroot u _).mpr hv
      obtain ⟨k,Hk,_⟩:=(HE u (fun _=>v)).mp HZ
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,congrFun Hk 0⟩
  have Hrank : FiniteImageRank.rank Finset.univ (fun k:J=>curve k s 0) (curve j s 0)=
      FiniteImageRank.rank Finset.univ (fun k:J=>curve k t 0) (curve j t 0) := by
    apply FiniteImageRank.rank_eq_of_comparisons
    · intro k _ l _
      constructor <;> intro heq
      · have HC : curve k s=curve l s:=by funext i; simpa only [Fin.eq_zero i] using heq
        exact congrFun ((RootBranches.curves_eq_iff H hcover (curve k) (curve l) (HR k) (HR l) s t).mp HC) 0
      · have HC : curve k t=curve l t:=by funext i; simpa only [Fin.eq_zero i] using heq
        exact congrFun ((RootBranches.curves_eq_iff H hcover (curve k) (curve l) (HR k) (HR l) s t).mpr HC) 0
    · intro k _
      exact RootBranches.scalar_order_iff H hcover (curve k) (curve j) (HR k) (HR j) s t
  rw [FiniteImageRank.rank_eq,FiniteImageRank.rank_eq,Himage s,Himage t,Hfollow s,Hfollow t] at Hrank
  exact Hrank

end LeanCanny.Geometry.OrderedCoveringRootRank
