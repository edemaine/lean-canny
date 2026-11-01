/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaBoundedGate
public import LeanCanny.Connectivity.BoundedGateProjectionSurjective
public import LeanCanny.Connectivity.FrontierCover
/-! # Projected relative frontiers of the actual bounded closed-formula source

A boundary edge permits different circular witnesses over the same original
point. Properness makes projected closure exact. All closures remain relative
to the permitted source and original realization, so excluded points add no edge.
-/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaBoundedFrontier
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open ClosedFormulaGateTruth
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

noncomputable abbrev Source (c : List Bool) := BoundedGateCoordinates.NativeZero F c
noncomputable abbrev Target (p : Formula) (c : List Bool) := (Description.mk (F.dimension c) p).realization

noncomputable def oldCoordinates (c : List Bool) (z : Source c) : Fin (F.dimension c) → ℝ := fun i =>
  z.val ⟨i.val,by have H:=i.isLt; change i.val < F.dimension c+2*F.count c+F.count c+2*F.count c; omega⟩

variable {p : Formula} (hp : ClosedFormulaWitness.Closed p)
  (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)

theorem projection_coordinates (z : Source c) :
    (ClosedFormulaBoundedGate.projection hp c hc hs z).val=oldCoordinates c z := by
  funext i
  exact BoundedGateCoordinates.projection_old F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three z i

theorem projection_eq_iff (a b : Source c) :
    ClosedFormulaBoundedGate.projection hp c hc hs a=ClosedFormulaBoundedGate.projection hp c hc hs b ↔
      oldCoordinates c a=oldCoordinates c b := by
  rw [Subtype.ext_iff,projection_coordinates hp c hc hs a,projection_coordinates hp c hc hs b]

theorem projection_surjective : Function.Surjective (ClosedFormulaBoundedGate.projection hp c hc hs) :=
  (baseHomeomorph hp c hc hs).surjective.comp
    (BoundedGateCoordinates.projection_surjective F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three)

noncomputable def projected (s : Set (Source c)) : Set (Target p c) :=
  ClosedFormulaBoundedGate.projection hp c hc hs '' s

theorem closure_projected (s : Set (Source c)) :
    closure (projected hp c hc hs s)=projected hp c hc hs (closure s) :=
  (ClosedFormulaBoundedGate.proper_projection hp c hc hs).isClosedMap.closure_image_eq_of_continuous
    (ClosedFormulaBoundedGate.proper_projection hp c hc hs).continuous s

theorem accessible_projected {s : Set (Source c)} (h : FrontierCover.Accessible s) :
    FrontierCover.Accessible (projected hp c hc hs s) :=
  h.image (ClosedFormulaBoundedGate.proper_projection hp c hc hs).continuous
    (ClosedFormulaBoundedGate.proper_projection hp c hc hs).isClosedMap

def LiftedIncident (s t : Set (Source c)) : Prop :=
  (∃ a ∈ s, ∃ b ∈ closure t, oldCoordinates c a=oldCoordinates c b) ∨
  (∃ a ∈ t, ∃ b ∈ closure s, oldCoordinates c a=oldCoordinates c b)

theorem incident_iff {I : Type*} (s : I → Set (Source c)) (i j : I) :
    FrontierCover.Incident (fun k => projected hp c hc hs (s k)) i j ↔
      LiftedIncident c (s i) (s j) := by
  have HE (u v : Set (Source c)) :
      (projected hp c hc hs u ∩ closure (projected hp c hc hs v)).Nonempty ↔
        ∃ a ∈ u, ∃ b ∈ closure v, oldCoordinates c a=oldCoordinates c b := by
    rw [closure_projected]
    constructor
    · rintro ⟨x,⟨a,ha,rfl⟩,b,hb,H⟩
      exact ⟨a,ha,b,hb,(projection_eq_iff hp c hc hs a b).mp H.symm⟩
    · rintro ⟨a,ha,b,hb,H⟩
      exact ⟨_,⟨a,ha,rfl⟩,b,hb,(projection_eq_iff hp c hc hs a b).mpr H |>.symm⟩
  exact or_congr (HE _ _) (HE _ _)

theorem projected_cover {I : Type*} (s : I → Set (Source c))
    (cover : ∀ y, ∃ i, y ∈ s i) : ∀ x : Target p c, ∃ i, x ∈ projected hp c hc hs (s i) := by
  intro x
  obtain ⟨y,rfl⟩ := projection_surjective hp c hc hs x
  obtain ⟨i,hi⟩ := cover y
  exact ⟨i,y,hi,rfl⟩

theorem joined_iff_reachable {I : Type*} [Finite I] (s : I → Set (Source c))
    (cover : ∀ y, ∃ i, y ∈ s i) (access : ∀ i, FrontierCover.Accessible (s i))
    {i j : I} {x y : Target p c}
    (hx : x ∈ projected hp c hc hs (s i)) (hy : y ∈ projected hp c hc hs (s j)) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (fun i j => LiftedIncident c (s i) (s j)) i j := by
  rw [FrontierCover.joinedIn_iff_reachable (fun i => projected hp c hc hs (s i))
    (projected_cover hp c hc hs s cover) (fun i => accessible_projected hp c hc hs (access i)) hx hy]
  have HE : FrontierCover.Incident (fun i => projected hp c hc hs (s i)) =
      (fun i j => LiftedIncident c (s i) (s j)) := by
    funext i j
    exact propext (incident_iff hp c hc hs s i j)
  rw [HE]

end LeanCanny.Connectivity.ClosedFormulaBoundedFrontier
