/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ComponentSlabAnchorEndpoints

/-! # Paths through an actual slab use only fiber paths and paired branch endpoints

Interior labels are witnesses, not additional graph vertices. No test of
whether two midpoint anchors lie in one component is required.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ComponentSlabCover.InteriorData
open Set
open scoped Classical
variable {X J L R : Type*} [TopologicalSpace X] {p : X→ℝ} {a b : ℝ}

inductive EndpointStep (D : InteriorData p a b J) : X→X→Prop
  | left {x y} : JoinedIn (p ⁻¹' {a}) x y→EndpointStep D x y
  | right {x y} : JoinedIn (p ⁻¹' {b}) x y→EndpointStep D x y
  | forward (j : J) : EndpointStep D (D.arc j a) (D.arc j b)
  | backward (j : J) : EndpointStep D (D.arc j b) (D.arc j a)

abbrev EndpointReach (D : InteriorData p a b J) :=Relation.ReflTransGen (EndpointStep D)

variable (D : InteriorData p a b J)

theorem endpointStep_symm {x y : X} (H : EndpointStep D x y) : EndpointStep D y x :=by
  cases H with
  | left H=>exact .left H.symm
  | right H=>exact .right H.symm
  | forward j=>exact .backward j
  | backward j=>exact .forward j

theorem endpointReach_symm {x y : X} (H : EndpointReach D x y) : EndpointReach D y x :=by
  induction H with
  | refl=>exact .refl
  | tail H h IH=>exact (Relation.ReflTransGen.single (D.endpointStep_symm h)).trans IH

theorem endpointStep_joined (hab : a<b) {x y : X} (H : EndpointStep D x y) :
    JoinedIn (p ⁻¹' Icc a b) x y :=by
  have HS (j : J) : D.arc j '' Icc a b⊆p ⁻¹' Icc a b:=by
    rintro z ⟨t,ht,rfl⟩
    change p (D.arc j t)∈Icc a b
    rcases eq_or_lt_of_le ht.1 with HE|HL
    · rw [←HE,D.level_left]
      exact ⟨le_rfl,hab.le⟩
    · rcases eq_or_lt_of_le ht.2 with HE|HR
      · rw [HE,D.level_right]
        exact ⟨hab.le,le_rfl⟩
      · exact Ioo_subset_Icc_self (D.ambient_subset j (D.arc_mem j ⟨t,HL,HR⟩))
  have HB (j : J) : JoinedIn (p ⁻¹' Icc a b) (D.arc j a) (D.arc j b):=
    (((convex_Icc a b).isPathConnected ⟨a,le_rfl,hab.le⟩).joinedIn a ⟨le_rfl,hab.le⟩
      b ⟨hab.le,le_rfl⟩).map (D.continuous_arc j) |>.mono (HS j)
  cases H with
  | left H=>exact H.mono (fun z hz=>by change p z=a at hz;change p z∈Icc a b;rw [hz];exact ⟨le_rfl,hab.le⟩)
  | right H=>exact H.mono (fun z hz=>by change p z=b at hz;change p z∈Icc a b;rw [hz];exact ⟨hab.le,le_rfl⟩)
  | forward j=>exact HB j
  | backward j=>exact (HB j).symm

theorem endpointReach_joined (hab : a<b) {x y : X}
    (hx : x∈p ⁻¹' Icc a b) (H : EndpointReach D x y) : JoinedIn (p ⁻¹' Icc a b) x y :=by
  induction H with
  | refl=>exact JoinedIn.refl hx
  | tail H h IH=>exact IH.trans (D.endpointStep_joined hab h)

section Reduction
variable (left : ClopenPathCover (p ⁻¹' {a}) L) (right : ClopenPathCover (p ⁻¹' {b}) R)
variable (base : X)

private noncomputable def endpointRepresentative : ComponentSlabCover.Index J L R→X :=
  Sum.elim (fun t=>D.arc t.1 a) (Sum.elim
    (fun l=>if H : (left.imagePiece l).Nonempty then H.choose else base)
    (fun r=>if H : (right.imagePiece r).Nonempty then H.choose else base))

private theorem endpoint_in_piece (hp : Continuous p) (hab : a<b)
    (i : ComponentSlabCover.Index J L R) (z : X)
    (hz : z∈ComponentSlabCover.ambientPiece D left right i) (he : p z=a∨p z=b) :
    EndpointReach D z (endpointRepresentative D left right base i) :=by
  rcases i with ⟨j,l,r⟩ | (l|r)
  · by_cases HV : ComponentSlabCover.Valid D left right j l r
    · rw [ComponentSlabCover.ambientPiece_middle_eq D left right hp hab j l r HV] at hz
      rcases hz with (hz|hz)|hz
      · have HI:=D.ambient_subset j hz
        change p z∈Ioo a b at HI
        rcases he with HE|HE <;> rw [HE] at HI <;> linarith [HI.1,HI.2]
      · exact .single (.left ((left.imagePiece_paths l z hz _ HV.1).mono (left.imagePiece_subset l)))
      · exact (Relation.ReflTransGen.single (.right
          ((right.imagePiece_paths r z hz _ HV.2).mono (right.imagePiece_subset r)))).tail (.backward j)
    · simp only [ComponentSlabCover.ambientPiece,Sum.elim_inl,ite_eq_right HV,mem_empty_iff_false] at hz
  · have HN : (left.imagePiece l).Nonempty:=⟨z,hz⟩
    change EndpointReach D z (if H : (left.imagePiece l).Nonempty then H.choose else base)
    rw [dite_eq_left HN]
    exact .single (.left ((left.imagePiece_paths l z hz _ HN.choose_spec).mono (left.imagePiece_subset l)))
  · have HN : (right.imagePiece r).Nonempty:=⟨z,hz⟩
    change EndpointReach D z (if H : (right.imagePiece r).Nonempty then H.choose else base)
    rw [dite_eq_left HN]
    exact .single (.right ((right.imagePiece_paths r z hz _ HN.choose_spec).mono (right.imagePiece_subset r)))

private theorem interior_in_piece (hp : Continuous p) (hab : a<b)
    (i : ComponentSlabCover.Index J L R) (z : X)
    (hz : z∈ComponentSlabCover.ambientPiece D left right i) (he : p z∈Ioo a b) :
    ∃j,z∈D.ambient j ∧ endpointRepresentative D left right base i=D.arc j a :=by
  rcases i with ⟨j,l,r⟩ | (l|r)
  · by_cases HV : ComponentSlabCover.Valid D left right j l r
    · rw [ComponentSlabCover.ambientPiece_middle_eq D left right hp hab j l r HV] at hz
      rcases hz with (hz|hz)|hz
      · exact ⟨j,hz,rfl⟩
      · have HE:=left.imagePiece_subset l hz
        change p z=a at HE
        rw [HE] at he
        exact False.elim (lt_irrefl a he.1)
      · have HE:=right.imagePiece_subset r hz
        change p z=b at HE
        rw [HE] at he
        exact False.elim (lt_irrefl b he.2)
    · simp only [ComponentSlabCover.ambientPiece,Sum.elim_inl,ite_eq_right HV,mem_empty_iff_false] at hz
  · have HE:=left.imagePiece_subset l hz
    change p z=a at HE
    rw [HE] at he
    exact False.elim (lt_irrefl a he.1)
  · have HE:=right.imagePiece_subset r hz
    change p z=b at HE
    rw [HE] at he
    exact False.elim (lt_irrefl b he.2)

private theorem overlap_endpointReach (hp : Continuous p) (hab : a<b)
    (Hcl : ∀j,IsClopen (D.piece j)) {i j : ComponentSlabCover.Index J L R}
    (H : ClosedPathCover.Overlap (ComponentSlabCover.piece D left right) i j) :
    EndpointReach D (endpointRepresentative D left right base i) (endpointRepresentative D left right base j) :=by
  obtain ⟨z,hi,hj⟩:=H
  rcases eq_or_lt_of_le z.property.1 with HE|HL
  · have HE' : p z.val=a:=HE.symm
    exact (D.endpointReach_symm (endpoint_in_piece D left right base hp hab i z.val hi (Or.inl HE'))).trans
      (endpoint_in_piece D left right base hp hab j z.val hj (Or.inl HE'))
  · rcases eq_or_lt_of_le z.property.2 with HE|HR
    · exact (D.endpointReach_symm (endpoint_in_piece D left right base hp hab i z.val hi (Or.inr HE))).trans
        (endpoint_in_piece D left right base hp hab j z.val hj (Or.inr HE))
    · obtain ⟨u,hu,HU⟩:=interior_in_piece D left right base hp hab i z.val hi ⟨HL,HR⟩
      obtain ⟨v,hv,HV⟩:=interior_in_piece D left right base hp hab j z.val hj ⟨HL,HR⟩
      rw [HU,HV]
      have HO : ClosedPathCover.Overlap D.piece u v:=by
        obtain ⟨zu,hzu,Hzu⟩:=hu
        obtain ⟨zv,hzv,Hzv⟩:=hv
        have HEQ : zu=zv:=Subtype.ext (Hzu.trans Hzv.symm)
        exact ⟨zu,hzu,HEQ.symm ▸ hzv⟩
      exact .single (.left (D.left_endpoints_joined Hcl hab left HO))

variable [Finite J] [Finite L] [Finite R]

include left right in
theorem endpoint_joined_iff_reach (hp : Continuous p) (hab : a<b) (t₀ : Ioo a b)
    (Hcl : ∀j,IsClopen (D.piece j)) {x y : X} (hx : p x=a∨p x=b) (hy : p y=a∨p y=b) :
    JoinedIn (p ⁻¹' Icc a b) x y↔EndpointReach D x y :=by
  have HX : x∈p ⁻¹' Icc a b:=by change p x∈Icc a b;rcases hx with HE|HE <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  have HY : y∈p ⁻¹' Icc a b:=by change p y∈Icc a b;rcases hy with HE|HE <;> rw [HE] <;> exact ⟨by linarith,by linarith⟩
  constructor
  · intro H
    obtain ⟨i,hi⟩:=ComponentSlabCover.cover D left right hab ⟨x,HX⟩
    obtain ⟨j,hj⟩:=ComponentSlabCover.cover D left right hab ⟨y,HY⟩
    have HS:=Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image
      (F:=univ) (x:=(⟨x,HX⟩ : p ⁻¹' Icc a b)) (y:=⟨y,HY⟩) (mem_univ _) (mem_univ _)
    rw [image_univ,Subtype.range_val] at HS
    have Hsub : JoinedIn (univ : Set (p ⁻¹' Icc a b)) ⟨x,HX⟩ ⟨y,HY⟩:=HS.mp H
    have HW:=(ComponentSlabCover.joinedIn_iff_reachable D left right hp hab t₀ hi hj).mp Hsub
    have HR : EndpointReach D (endpointRepresentative D left right x i) (endpointRepresentative D left right x j):=
      HW.lift' (endpointRepresentative D left right x) (fun _ _ h=>overlap_endpointReach D left right x hp hab Hcl h)
    exact ((endpoint_in_piece D left right x hp hab i x hi hx).trans HR).trans
      (D.endpointReach_symm (endpoint_in_piece D left right x hp hab j y hj hy))
  · exact D.endpointReach_joined hab HX

end Reduction
end LeanCanny.Connectivity.ComponentSlabCover.InteriorData
