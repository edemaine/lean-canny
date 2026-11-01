/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateRoot
public import LeanCanny.Geometry.FiniteCircularCoordinates
public import LeanCanny.Geometry.WeakBooleanWitness
public import LeanCanny.Connectivity.FormulaStrictWitness
/-! # The literal native gate zero set preserves the weak-atom base's components -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateCircles
open ETR Set LeanCanny.Encoding LeanCanny.Computation LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph MonotoneGateArithmetic
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def atomValue (F : Family) (c : List Bool) (i : Fin (F.count c))
    (x : Fin (F.dimension c) → ℝ) : ℝ :=
  (F.atom (pair c (List.replicate i.val true))).eval (Formula.extend x)

def predicate (F : Family) (c : List Bool) : (Fin (F.count c) → Prop) → Prop :=
  MonotoneBooleanCircuit.predicate (circuit F) c

theorem atom_continuous (F : Family) (c : List Bool) (i : Fin (F.count c)) :
    Continuous (atomValue F c i) := by
  exact FormulaStrictWitness.continuous_eval _ _

theorem atom_equation (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (z : (Fin (F.dimension c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane))
    (i : Fin (F.count c)) :
    MonotoneGateValues.status F c (FiniteCircularCoordinates.encode _ _ z) i ↔
      atomValue F c i z.1=‖z.2 i‖^2 := by
  have H0 := FiniteCircularCoordinates.fresh_eval (F.dimension c) (F.count c) z i 0
  have H1 := FiniteCircularCoordinates.fresh_eval (F.dimension c) (F.count c) z i 1
  simp only [Fin.val_zero,Nat.add_zero] at H0
  simp only [Fin.val_one] at H1
  have HA := FiniteCircularCoordinates.old_eval (F.dimension c) (F.count c) z
    (F.atom (pair c (List.replicate i.val true))) (ha i.val i.isLt)
  have HN : ‖z.2 i‖^2=(z.2 i 0)^2+(z.2 i 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  simp only [MonotoneGateValues.status,atomBody,Term.eval,witnessIndex,dimension,index,
    pairFst_pair,pairSnd_pair,List.length_replicate,Bool.toNat_false,Bool.toNat_true,
    Nat.add_zero,Int.cast_neg,Int.cast_one,neg_one_mul,← sub_eq_add_neg]
  rw [HA,H0,H1,HN]
  change _ ↔ _
  unfold atomValue
  constructor <;> intro H <;> nlinarith

theorem root_equations (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3)
    (z : (Fin (F.dimension c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane)) :
    rootValue F c (FiniteCircularCoordinates.encode _ _ z)=0 ↔
      predicate F c (fun i => atomValue F c i z.1=‖z.2 i‖^2) := by
  rw [MonotoneGateRoot.root_zero F c _ ha hk]
  have HE : MonotoneGateValues.status F c (FiniteCircularCoordinates.encode _ _ z)=
      (fun i => atomValue F c i z.1=‖z.2 i‖^2) := by
    funext i
    exact propext (atom_equation F c ha z i)
  rw [HE]
  rfl

noncomputable def witnessHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :
    WeakBooleanWitness.Space (atomValue F c) (predicate F c) ≃ₜ
      {x : Fin (base F c) → ℝ // rootValue F c x=0} :=
  (FiniteCircularCoordinates.homeomorph (F.dimension c) (F.count c)).subtype
    (fun z => (root_equations F c ha hk z).symm)

noncomputable def zeroWitnessHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :
    ZeroSet F c ≃ₜ WeakBooleanWitness.Space (atomValue F c) (predicate F c) :=
  (zeroHomeomorph F c ha).trans (witnessHomeomorph F c ha hk).symm

noncomputable def projection (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (z : ZeroSet F c) :
    WeakBooleanWitness.Base (atomValue F c) (predicate F c) :=
  WeakBooleanWitness.projection _ _ (predicate_mono F c hk) (zeroWitnessHomeomorph F c ha hk z)

private theorem homeomorph_joined' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

theorem joined_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y z : ZeroSet F c) :
    JoinedIn univ y z ↔ JoinedIn univ (projection F c ha hk y) (projection F c ha hk z) := by
  exact (homeomorph_joined' (zeroWitnessHomeomorph F c ha hk) y z).trans
    (WeakBooleanWitness.joined_iff _ _ (predicate_mono F c hk) (atom_continuous F c) _ _)

theorem preconnected_iff (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) :
    IsPreconnected (ZeroSet F c) ↔
      IsPreconnected (univ : Set (WeakBooleanWitness.Base (atomValue F c) (predicate F c))) := by
  have HE := (zeroWitnessHomeomorph F c ha hk).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (zeroWitnessHomeomorph F c ha hk).surjective] at HE
  exact (isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ).trans
    (HE.symm.trans (WeakBooleanWitness.preconnected_iff _ _ (predicate_mono F c hk) (atom_continuous F c)))

end LeanCanny.Connectivity.MonotoneGateCircles
