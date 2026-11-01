/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.MonotoneGateEndpoint
public import LeanCanny.Connectivity.MonotoneGateCircles
/-! # Canonical circle endpoints retain the old point and uniquely determine every gate -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateCanonicalPoint
open ETR Set LeanCanny.Encoding LeanCanny.Computation LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph MonotoneGateValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalPrefix (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) : Fin (base F c) → ℝ :=
  FiniteCircularCoordinates.encode (F.dimension c) (F.count c)
    (x,fun i => WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i x))
noncomputable def point (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) : Fin (total F c) → ℝ :=
  full F c (canonicalPrefix F c x)

theorem holds_prefix (F : Family) (c : List Bool) (z : Fin (base F c) → ℝ) (p : Formula)
    (hp : p.arity≤base F c) :
    p.Holds (Formula.extend (full F c z)) ↔ p.Holds (Formula.extend z) := by
  apply Formula.holds_congr
  intro i hi
  have HI : i < base F c := hi.trans_le hp
  have HT : i < total F c := by dsimp [total]; omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HT]
  exact TriangularTermGraph.old (base F c) (gate F c) z (F.count c) ⟨i,HI⟩

theorem holds_old (F : Family) (c : List Bool)
    (z : (Fin (F.dimension c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane))
    (p : Formula) (hp : p.arity≤F.dimension c) :
    p.Holds (Formula.extend (FiniteCircularCoordinates.encode _ _ z)) ↔ p.Holds (Formula.extend z.1) := by
  apply Formula.holds_congr
  intro i hi
  have HI : i < F.dimension c := hi.trans_le hp
  have HB : i < F.dimension c+2*F.count c := by omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HB]
  exact FiniteCircularCoordinates.encode_old _ _ z ⟨i,HI⟩

theorem circle_scope (F : Family) (c : List Bool) (i : Fin (F.count c))
    (ha : (F.atom (pair c (List.replicate i.val true))).arity≤F.dimension c) :
    (WeakCircleCanonicalFormula.formula (F.atom (pair c (List.replicate i.val true)))
      (witnessIndex F (pair c (List.replicate i.val true)) false)
      (witnessIndex F (pair c (List.replicate i.val true)) true)).arity≤base F c := by
  rw [WeakCircleCanonicalFormula.arity]
  simp only [witnessIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate,
    Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  have HI := i.isLt
  dsimp [base]
  omega

theorem circle_full (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (z : (Fin (F.dimension c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane))
    (i : Fin (F.count c)) :
    (WeakCircleCanonicalFormula.formula (F.atom (pair c (List.replicate i.val true)))
      (witnessIndex F (pair c (List.replicate i.val true)) false)
      (witnessIndex F (pair c (List.replicate i.val true)) true)).Holds
      (Formula.extend (full F c (FiniteCircularCoordinates.encode _ _ z))) ↔
      z.2 i=WeakBooleanWitness.canonical (MonotoneGateCircles.atomValue F c i z.1) := by
  rw [holds_prefix F c _ _ (circle_scope F c i (ha i.val i.isLt)),WeakCircleCanonicalFormula.holds_iff]
  have H0 := FiniteCircularCoordinates.fresh_eval (F.dimension c) (F.count c) z i 0
  have H1 := FiniteCircularCoordinates.fresh_eval (F.dimension c) (F.count c) z i 1
  simp only [Fin.val_zero,Nat.add_zero] at H0
  simp only [Fin.val_one] at H1
  simp only [witnessIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate,
    Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  rw [FiniteCircularCoordinates.old_eval _ _ z _ (ha i.val i.isLt),H0,H1]
  exact WeakCircleCanonicalFormula.plane_iff _ _

theorem constraint_full (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (z : Fin (base F c) → ℝ) (i : Fin (F.count c)) :
    (constraint F (pair c (List.replicate i.val true))).eval (Formula.extend (full F c z))=0 :=
  (constraint_zero_iff F c i _).mpr
    (TriangularTermGraph.equations _ _ _ (gate_scope F c ha) z i)

end LeanCanny.Connectivity.MonotoneGateCanonicalPoint
