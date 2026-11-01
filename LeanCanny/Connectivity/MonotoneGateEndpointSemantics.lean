/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateCanonicalPoint
/-! # Actual native endpoint formulas denote the unique canonical graph extension -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateCanonicalPoint
open ETR Set LeanCanny.Encoding LeanCanny.Computation LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph MonotoneGateValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem endpoint_full (F : Family) (c : List Bool) (s : Formula) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (z : (Fin (F.dimension c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane)) :
    (MonotoneGateEndpoint.endpoint F s c).Holds
      (Formula.extend (full F c (FiniteCircularCoordinates.encode _ _ z))) ↔
      s.Holds (Formula.extend z.1) ∧ ∀ i, z.2 i=WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i z.1) := by
  rw [MonotoneGateEndpoint.endpoint_holds]
  have HOld := (holds_prefix F c (FiniteCircularCoordinates.encode _ _ z) s
    (hs.trans (by dsimp [base]; omega))).trans (holds_old F c z s hs)
  apply and_congr HOld
  constructor
  · intro H i
    exact (circle_full F c ha z i).mp (H i.val i.isLt).1
  · intro H i hi
    exact ⟨(circle_full F c ha z ⟨i,hi⟩).mpr (H ⟨i,hi⟩),constraint_full F c ha _ ⟨i,hi⟩⟩

theorem point_endpoint (F : Family) (c : List Bool) (s : Formula) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (x : Fin (F.dimension c) → ℝ) (hx : s.Holds (Formula.extend x)) :
    (MonotoneGateEndpoint.endpoint F s c).Holds (Formula.extend (point F c x)) :=
  (endpoint_full F c s hs ha (x,fun i => WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i x))).mpr
    ⟨hx,fun _ => rfl⟩

theorem endpoint_denotes (F : Family) (c : List Bool) (s : Formula)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (x : Fin (F.dimension c) → ℝ) (hs : Denotes (F.dimension c) s x) :
    Denotes (total F c) (MonotoneGateEndpoint.endpoint F s c) (point F c x) := by
  refine ⟨MonotoneGateEndpoint.endpoint_arity F s c hs.1 ha,?_⟩
  intro y
  constructor
  · intro HY
    have HE := (MonotoneGateEndpoint.endpoint_holds F s c (Formula.extend y)).mp HY
    have HG : y∈TriangularTermGraph.Solutions (base F c) (gate F c) (F.count c) := by
      intro i
      exact (constraint_zero_iff F c i y).mp (HE.2 i.val i.isLt).2
    let old := TriangularTermGraph.projection (base F c) (F.count c) y
    have HU : full F c old=y := TriangularTermGraph.unique _ _ _ (gate_scope F c ha) ⟨y,HG⟩
    let z := FiniteCircularCoordinates.decode (F.dimension c) (F.count c) old
    have HZ : FiniteCircularCoordinates.encode _ _ z=old := FiniteCircularCoordinates.encode_decode _ _ old
    have HAt : (MonotoneGateEndpoint.endpoint F s c).Holds
        (Formula.extend (full F c (FiniteCircularCoordinates.encode _ _ z))) := by
      rw [HZ,HU]
      exact HY
    have HC := (endpoint_full F c s hs.1 ha z).mp HAt
    have HX : z.1=x := (hs.2 _).mp HC.1
    have HWP : z=(x,fun i => WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i x)) := by
      apply Prod.ext HX
      funext i
      exact (HC.2 i).trans (congrArg (fun u => WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i u)) HX)
    calc
      y=full F c old := HU.symm
      _=full F c (FiniteCircularCoordinates.encode _ _ z) := by rw [HZ]
      _=point F c x := by rw [HWP]; rfl
  · rintro rfl
    exact point_endpoint F c s hs.1 ha x ((hs.2 x).mpr rfl)

end LeanCanny.Connectivity.MonotoneGateCanonicalPoint
