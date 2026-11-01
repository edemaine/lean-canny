/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedMonotoneGateEndpoint
public import LeanCanny.Connectivity.BoundedGateCoordinates
public import LeanCanny.Connectivity.MonotoneGateEndpointSemantics
/-! # Bounded endpoint extensions are unique for every old candidate -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem holds_old (F : Family) (c : List Bool)
    (z : (Fin (total F c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane))
    (s : Formula) (hs : s.arity≤total F c) :
    s.Holds (Formula.extend (encode F c z)) ↔ s.Holds (Formula.extend z.1) := by
  apply Formula.holds_congr
  intro j hj
  have HJ := hj.trans_le hs
  have HJ' : j < BoundedMonotoneGateSource.total F c := by
    dsimp [BoundedMonotoneGateSource.total,total,base] at HJ ⊢; omega
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HJ']
  exact FiniteCircularCoordinates.encode_old _ _ z ⟨j,HJ⟩

theorem endpoint_condition (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (z : (Fin (total F c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane))
    (i : Fin (F.count c)) :
    (BoundedMonotoneGateEndpoint.condition F (BoundedMonotoneGateSource.query c i.val)).Holds
      (Formula.extend (encode F c z)) ↔ z.2 i=WeakBooleanWitness.canonical
        ((BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i.val)).eval
          (Formula.extend z.1)) := by
  rw [BoundedMonotoneGateEndpoint.condition,WeakCircleCanonicalFormula.holds_iff,
    old_eval F c z _ (BoundedMonotoneGateEndpoint.residual_arity F c i.val i.isLt ha)]
  have HU (j : Fin 2) : Formula.extend (encode F c z)
      (F.dimension c+3*F.count c+2*i.val+j.val)=z.2 i j := by
    have HE := FiniteCircularCoordinates.fresh_eval (total F c) (F.count c) z i j
    convert HE using 1; congr 1; dsimp [total,base]; omega
  have H0 := HU 0
  have H1 := HU 1
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero] at H0 H1
  simp only [BoundedMonotoneGateSource.slackIndex,dimension,count,index,BoundedMonotoneGateSource.query,
    pairFst_pair,pairSnd_pair,List.length_replicate,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  rw [H0,H1]
  exact WeakCircleCanonicalFormula.plane_iff _ _

theorem endpoint_encode (F : Family) (c : List Bool) (s : Formula) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (z : (Fin (total F c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane)) :
    (BoundedMonotoneGateEndpoint.endpoint F s c).Holds (Formula.extend (encode F c z)) ↔
      (MonotoneGateEndpoint.endpoint F s c).Holds (Formula.extend z.1) ∧
      ∀ i : Fin (F.count c), z.2 i=WeakBooleanWitness.canonical
        ((BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i.val)).eval
          (Formula.extend z.1)) := by
  change (_ ∧ _) ↔ _
  rw [holds_old F c z _ (MonotoneGateEndpoint.endpoint_arity F s c hs ha)]
  apply and_congr_right
  intro _
  simp only [FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds,
    List.forall_mem_map,List.mem_range]
  constructor
  · intro H i
    exact (endpoint_condition F c ha z i).mp (H i.val i.isLt)
  · intro H i hi
    exact (endpoint_condition F c ha z ⟨i,hi⟩).mpr (H ⟨i,hi⟩)

noncomputable def extendPoint (F : Family) (c : List Bool) (y : Fin (total F c) → ℝ) :
    Fin (BoundedMonotoneGateSource.total F c) → ℝ :=
  encode F c (y,fun i => WeakBooleanWitness.canonical
    ((BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i.val)).eval (Formula.extend y)))

theorem extension_denotes (F : Family) (c : List Bool) (s : Formula) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (y : Fin (total F c) → ℝ) (hy : Denotes (total F c) (MonotoneGateEndpoint.endpoint F s c) y) :
    Denotes (BoundedMonotoneGateSource.total F c) (BoundedMonotoneGateEndpoint.endpoint F s c) (extendPoint F c y) := by
  refine ⟨BoundedMonotoneGateEndpoint.endpoint_arity F s c hs ha,?_⟩
  intro z
  let w := FiniteCircularCoordinates.decode (total F c) (F.count c) z
  have HW : encode F c w=z := FiniteCircularCoordinates.encode_decode _ _ z
  constructor
  · intro HZ
    rw [← HW] at HZ
    have H := (endpoint_encode F c s hs ha w).mp HZ
    have HY := (hy.2 w.1).mp H.1
    have HE : w=(y,fun i => WeakBooleanWitness.canonical
        ((BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i.val)).eval (Formula.extend y))) := by
      apply Prod.ext HY
      funext i
      exact (H.2 i).trans (congrArg (fun v => WeakBooleanWitness.canonical
        ((BoundedMonotoneGateEndpoint.residual F (BoundedMonotoneGateSource.query c i.val)).eval (Formula.extend v))) HY)
    rw [← HW,HE]
    rfl
  · rintro rfl
    exact (endpoint_encode F c s hs ha _).mpr ⟨(hy.2 y).mpr rfl,fun _ => rfl⟩

theorem endpoint_denotes (F : Family) (c : List Bool) (s : Formula)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (x : Fin (F.dimension c) → ℝ) (hs : Denotes (F.dimension c) s x) :
    Denotes (BoundedMonotoneGateSource.total F c) (BoundedMonotoneGateEndpoint.endpoint F s c)
      (extendPoint F c (MonotoneGateCanonicalPoint.point F c x)) :=
  extension_denotes F c s hs.1 ha _ (MonotoneGateCanonicalPoint.endpoint_denotes F c s ha x hs)

end LeanCanny.Connectivity.BoundedGateCoordinates
