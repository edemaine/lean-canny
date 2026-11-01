/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateEndpointSemantics
/-! # Canonical graph points lie in exactly the original weak-atom base -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateCanonicalPoint
open ETR Set LeanCanny.Encoding LeanCanny.Computation LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph MonotoneGateValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem point_zero_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (x : Fin (F.dimension c) → ℝ) :
    point F c x∈ZeroSet F c ↔
      MonotoneGateCircles.predicate F c (fun i => 0≤MonotoneGateCircles.atomValue F c i x) := by
  have HG : point F c x∈TriangularTermGraph.Solutions (base F c) (gate F c) (F.count c) :=
    TriangularTermGraph.equations _ _ _ (gate_scope F c ha) (canonicalPrefix F c x)
  have HE : point F c x∈ZeroSet F c ↔ rootValue F c (canonicalPrefix F c x)=0 := by
    rw [zero_iff]
    exact ⟨fun H => H.1,fun H => ⟨H,HG⟩⟩
  rw [HE]
  unfold canonicalPrefix
  rw [MonotoneGateCircles.root_equations F c ha hk]
  have HS : (fun i => MonotoneGateCircles.atomValue F c i x=
      ‖WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i x)‖^2)=
      (fun i => 0≤MonotoneGateCircles.atomValue F c i x) := by
    funext i
    exact propext (WeakBooleanWitness.canonical_equation _)
  rw [HS]

noncomputable def sourcePoint (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3)
    (x : WeakBooleanWitness.Base (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c)) : ZeroSet F c :=
  ⟨point F c x.val,(point_zero_iff F c ha hk x.val).mpr x.property⟩

theorem projection_val (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) (i : Fin (F.dimension c)) :
    (MonotoneGateCircles.projection F c ha hk y).val i=
      y.val ⟨i.val,by have HI:=i.isLt; dsimp [total,base]; omega⟩ := rfl

theorem projection_sourcePoint (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3)
    (x : WeakBooleanWitness.Base (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c)) :
    MonotoneGateCircles.projection F c ha hk (sourcePoint F c ha hk x)=x := by
  apply Subtype.ext
  funext i
  rw [projection_val]
  change (full F c (canonicalPrefix F c x.val)) (Fin.castAdd (F.count c) (Fin.castAdd (2*F.count c) i))=x.val i
  simp only [full,TriangularTermGraph.old]
  exact FiniteCircularCoordinates.encode_old _ _ _ i

theorem sourcePoint_joined_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3)
    (x y : WeakBooleanWitness.Base (MonotoneGateCircles.atomValue F c) (MonotoneGateCircles.predicate F c)) :
    JoinedIn univ (sourcePoint F c ha hk x) (sourcePoint F c ha hk y) ↔ JoinedIn univ x y := by
  rw [MonotoneGateCircles.joined_iff F c ha hk,projection_sourcePoint,projection_sourcePoint]

end LeanCanny.Connectivity.MonotoneGateCanonicalPoint
