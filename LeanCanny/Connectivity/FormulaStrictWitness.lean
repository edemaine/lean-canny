/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.StrictInequalityWitness
public import LeanCanny.Connectivity.Problem
public import LeanCanny.ETR.EquationDegree
public import Mathlib.Topology.Homeomorph.Lemmas
/-! # Literal two-coordinate polynomial witnesses for strict formula conjuncts -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaStrictWitness
open ETR Set LeanCanny.Geometry
open CircularWitness
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def squares (n : ℕ) : Term := .add (.mul (.var n) (.var n)) (.mul (.var (n+1)) (.var (n+1)))
def term (n : ℕ) (t : Term) : Term := .add (.mul (.mul (.const (-1)) t) (squares n)) (.const (-1))
def original (n : ℕ) (p : Formula) (t : Term) : Description := ⟨n,.and p (.ltZero t)⟩
def lifted (n : ℕ) (p : Formula) (t : Term) : Description := ⟨n+2,.and p (.eqZero (term n t))⟩

theorem term_arity (n : ℕ) (t : Term) (ht : t.arity ≤ n) : (term n t).arity ≤ n+2 := by
  simp only [term,squares,Term.arity]
  omega

theorem term_degree (n : ℕ) (t : Term) : (term n t).degreeBound = t.degreeBound+2 := by
  simp [term,squares,Term.degreeBound]

theorem lifted_wellFormed (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n) :
    (lifted n p t).WellFormed := by
  change max p.arity (term n t).arity ≤ n+2
  exact max_le (hp.trans (by omega)) (term_arity n t ht)

noncomputable def tuple (n : ℕ) : ((Fin n → ℝ) × Plane) ≃ₜ (Fin (n+2) → ℝ) :=
  ((Homeomorph.refl (Fin n → ℝ)).prodCongr (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ))).trans (Fin.appendHomeomorph n 2)

theorem tuple_apply (n : ℕ) (x : Fin n → ℝ) (w : Plane) : tuple n (x,w) = Fin.append x w := rfl

theorem extend_tuple_old (n : ℕ) (x : Fin n → ℝ) (w : Plane) (i : ℕ) (hi : i<n) :
    Formula.extend (tuple n (x,w)) i = Formula.extend x i := by
  simp only [Formula.extend,tuple_apply,dite_eq_left hi,dite_eq_left (show i<n+2 by omega)]
  exact Fin.append_left x (fun j => w j) ⟨i,hi⟩

theorem eval_old (n : ℕ) (t : Term) (ht : t.arity ≤ n) (x : Fin n → ℝ) (w : Plane) :
    t.eval (Formula.extend (tuple n (x,w))) = t.eval (Formula.extend x) :=
  t.eval_congr _ _ (fun i hi => extend_tuple_old n x w i (hi.trans_le ht))

theorem holds_old (n : ℕ) (p : Formula) (hp : p.arity ≤ n) (x : Fin n → ℝ) (w : Plane) :
    p.Holds (Formula.extend (tuple n (x,w))) ↔ p.Holds (Formula.extend x) :=
  p.holds_congr _ _ (fun i hi => extend_tuple_old n x w i (hi.trans_le hp))

theorem extend_tuple_fresh (n : ℕ) (x : Fin n → ℝ) (w : Plane) (j : Fin 2) :
    Formula.extend (tuple n (x,w)) (n+j.val) = w j := by
  simp only [Formula.extend,tuple_apply,dite_eq_left (show n+j.val<n+2 by have H:=j.isLt; omega)]
  exact Fin.append_right x (fun j => w j) j

theorem term_eval (n : ℕ) (t : Term) (ht : t.arity ≤ n) (x : Fin n → ℝ) (w : Plane) :
    (term n t).eval (Formula.extend (tuple n (x,w))) =
      (-t.eval (Formula.extend x)) * ‖w‖^2-1 := by
  simp only [term,squares,Term.eval,eval_old n t ht x w]
  have H0 := extend_tuple_fresh n x w 0
  have H1 := extend_tuple_fresh n x w 1
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_one] at H0 H1
  rw [H0,H1,EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  ring

theorem lifted_tuple (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (x : Fin n → ℝ) (w : Plane) :
    tuple n (x,w) ∈ (lifted n p t).realization ↔
      p.Holds (Formula.extend x) ∧ (-t.eval (Formula.extend x))*‖w‖^2=1 := by
  change p.Holds _ ∧ (term n t).eval _=0 ↔ _
  rw [holds_old n p hp x w,term_eval n t ht x w,sub_eq_zero]



theorem continuous_eval (n : ℕ) (t : Term) : Continuous (fun x : Fin n → ℝ => t.eval (Formula.extend x)) := by
  induction t with
  | const _ => exact continuous_const
  | var i =>
    by_cases H : i<n
    · simpa only [Term.eval,Formula.extend,dite_eq_left H] using (continuous_apply (⟨i,H⟩ : Fin n))
    · simpa only [Term.eval,Formula.extend,dite_eq_right H] using (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))
  | add _ _ HA HB => exact HA.add HB
  | mul _ _ HA HB => exact HA.mul HB

def context (n : ℕ) (p : Formula) : Description := ⟨n,p⟩
noncomputable def function (n : ℕ) (p : Formula) (t : Term) (x : (context n p).realization) : ℝ :=
  -t.eval (Formula.extend x.val)

theorem continuous_function (n : ℕ) (p : Formula) (t : Term) : Continuous (function n p t) :=
  (continuous_eval n t).neg.comp continuous_subtype_val

noncomputable def contextHomeomorph (n : ℕ) (p : Formula) (t : Term) :
    StrictInequalityWitness.equation (function n p t) ≃ₜ
      {q : (Fin n → ℝ) × Plane // p.Holds (Formula.extend q.1) ∧ (-t.eval (Formula.extend q.1))*‖q.2‖^2=1} where
  toFun z := ⟨(z.val.1.val,z.val.2),z.val.1.property,z.property⟩
  invFun z := ⟨(⟨z.val.1,z.property.1⟩,z.val.2),z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

noncomputable def liftedHomeomorph (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n) :
    StrictInequalityWitness.equation (function n p t) ≃ₜ (lifted n p t).realization :=
  (contextHomeomorph n p t).trans ((tuple n).subtype (fun q => (lifted_tuple n p t hp ht q.1 q.2).symm))

noncomputable def originalHomeomorph (n : ℕ) (p : Formula) (t : Term) :
    StrictInequalityWitness.positive (function n p t) ≃ₜ (original n p t).realization where
  toFun x := ⟨x.val.val,⟨x.val.property,by
    have H := x.property
    change 0 < -t.eval (Formula.extend x.val.val) at H
    change t.eval (Formula.extend x.val.val) < 0
    linarith⟩⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,by
    have H := x.property.2
    change t.eval (Formula.extend x.val) < 0 at H
    change 0 < -t.eval (Formula.extend x.val)
    linarith⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

noncomputable def projection (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (z : (lifted n p t).realization) : (original n p t).realization :=
  originalHomeomorph n p t (StrictInequalityWitness.projection _ ((liftedHomeomorph n p t hp ht).symm z))

theorem projection_val (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (z : (lifted n p t).realization) (i : Fin n) :
    (projection n p t hp ht z).val i = z.val (Fin.castAdd 2 i) := by
  have H : tuple n ((projection n p t hp ht z).val,((liftedHomeomorph n p t hp ht).symm z).val.2) = z.val :=
    congrArg Subtype.val ((liftedHomeomorph n p t hp ht).apply_symm_apply z)
  have HI := congrFun H (Fin.castAdd 2 i)
  rw [tuple_apply,Fin.append_left] at HI
  exact HI

private theorem homeomorph_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

private theorem homeomorph_preconnected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : IsPreconnected (univ : Set X) ↔ IsPreconnected (univ : Set Y) := by
  have H := e.isPreconnected_image (s := (univ : Set X))
  rw [Set.image_univ_of_surjective e.surjective] at H
  exact H.symm

theorem joined_iff (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (y z : (lifted n p t).realization) :
    JoinedIn univ y z ↔ JoinedIn univ (projection n p t hp ht y) (projection n p t hp ht z) := by
  exact (homeomorph_joined (liftedHomeomorph n p t hp ht).symm y z).trans
    ((StrictInequalityWitness.joined_iff _ (continuous_function n p t) _ _).trans
      (homeomorph_joined (originalHomeomorph n p t) _ _))

private theorem subtype_preconnected {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsPreconnected S ↔ IsPreconnected (univ : Set S) :=
  isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ

theorem preconnected_iff (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n) :
    IsPreconnected (lifted n p t).realization ↔ IsPreconnected (original n p t).realization := by
  have H := homeomorph_preconnected (liftedHomeomorph n p t hp ht).symm
  have H' := (subtype_preconnected (StrictInequalityWitness.equation (function n p t))).symm.trans
    ((StrictInequalityWitness.preconnected_iff _ (continuous_function n p t)).trans
      (subtype_preconnected (StrictInequalityWitness.positive (function n p t))))
  exact (subtype_preconnected _).trans (H.trans (H'.trans
    ((homeomorph_preconnected (originalHomeomorph n p t)).trans (subtype_preconnected _).symm)))

end LeanCanny.Connectivity.FormulaStrictWitness
