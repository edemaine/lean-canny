/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ComponentSlabEndpointPaths

/-! # Remove auxiliary noncritical points from endpoint walks

Only the two requested endpoints and actual matched-branch endpoints must
be represented. Consecutive paths inside one fiber are composed before a
branch transition, so arbitrary component representatives need no labels.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ComponentSlabCover.InteriorData
open Set
open scoped Classical
variable {X J : Type*} [TopologicalSpace X] {p : X→ℝ} {a b : ℝ}
variable (D : InteriorData p a b J)

def FiberLink (_D : InteriorData p a b J) (x y : X) : Prop :=JoinedIn (p ⁻¹' {a}) x y∨JoinedIn (p ⁻¹' {b}) x y

theorem fiberLink_refl {x : X} (hx : p x=a∨p x=b) : FiberLink D x x :=by
  rcases hx with H|H
  · exact Or.inl (JoinedIn.refl H)
  · exact Or.inr (JoinedIn.refl H)

theorem fiberLink_trans (hab : a<b) {x y z : X} (H : FiberLink D x y)
    (K : FiberLink D y z) : FiberLink D x z :=by
  rcases H with H|H <;> rcases K with K|K
  · exact Or.inl (H.trans K)
  · have HE : a=b:=H.target_mem.symm.trans K.source_mem
    exact False.elim (hab.ne HE)
  · have HE : a=b:=K.source_mem.symm.trans H.target_mem
    exact False.elim (hab.ne HE)
  · exact Or.inr (H.trans K)

def AtomicEndpointStep (K : Set X) (x y : K) : Prop :=EndpointStep D x.val y.val
abbrev AtomicEndpointReach (K : Set X) :=Relation.ReflTransGen (AtomicEndpointStep D K)

theorem atomicEndpointReach_of_fiberLink {K : Set X} {x y : K}
    (H : FiberLink D x.val y.val) : AtomicEndpointReach D K x y :=by
  rcases H with H|H
  · exact .single (.left H)
  · exact .single (.right H)

theorem endpointReach_atomic (hab : a<b) (K : Set X)
    (HL : ∀j,D.arc j a∈K) (HR : ∀j,D.arc j b∈K)
    {x y : X} (hx : x∈K) (hy : y∈K) (hye : p y=a∨p y=b)
    (H : EndpointReach D x y) : AtomicEndpointReach D K ⟨x,hx⟩ ⟨y,hy⟩ :=by
  have HI : ∀w : K,FiberLink D y w.val→AtomicEndpointReach D K ⟨x,hx⟩ w:=by
    clear hy hye
    induction H with
    | refl=>
      intro w hw
      exact D.atomicEndpointReach_of_fiberLink hw
    | @tail u v H h IH=>
      intro w hw
      cases h with
      | left h=>exact IH w (D.fiberLink_trans hab (Or.inl h) hw)
      | right h=>exact IH w (D.fiberLink_trans hab (Or.inr h) hw)
      | forward j=>
        let l : K:=⟨D.arc j a,HL j⟩
        let r : K:=⟨D.arc j b,HR j⟩
        have HA : AtomicEndpointReach D K ⟨x,hx⟩ l:=IH l
          (D.fiberLink_refl (Or.inl (D.level_left j)))
        have HB : AtomicEndpointReach D K l r:=.single (.forward j)
        exact (HA.trans HB).trans (D.atomicEndpointReach_of_fiberLink hw)
      | backward j=>
        let l : K:=⟨D.arc j a,HL j⟩
        let r : K:=⟨D.arc j b,HR j⟩
        have HA : AtomicEndpointReach D K ⟨x,hx⟩ r:=IH r
          (D.fiberLink_refl (Or.inr (D.level_right j)))
        have HB : AtomicEndpointReach D K r l:=.single (.backward j)
        exact (HA.trans HB).trans (D.atomicEndpointReach_of_fiberLink hw)
  exact HI ⟨y,hy⟩ (D.fiberLink_refl hye)

theorem atomicEndpointReach_iff (hab : a<b) (K : Set X)
    (HL : ∀j,D.arc j a∈K) (HR : ∀j,D.arc j b∈K) (x y : K)
    (hye : p y.val=a∨p y.val=b) :
    AtomicEndpointReach D K x y↔EndpointReach D x.val y.val :=by
  constructor
  · intro H
    exact H.lift Subtype.val (fun _ _ h=>h)
  · exact D.endpointReach_atomic hab K HL HR x.property y.property hye

end LeanCanny.Connectivity.ComponentSlabCover.InteriorData
