/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TermCoordinateGraph
public import LeanCanny.ETR.CenteredSquaredDistanceTerm
public import LeanCanny.Geometry.SquaredDistanceFibers
/-! # A universal radial graph with coordinate freezes for every center

Center coordinates are part of the initial spatial source. A chosen center
and radius therefore use only coordinate-height rows, with integer normals.
-/
@[expose] public section
namespace LeanCanny.Geometry.CenteredRadialGraph
open ETR Set LeanCanny.Connectivity
open scoped Classical
variable (N m : ℕ) (p : Term) (hp : p.arity≤N) (hm : m≤N)

def description : Description := TermCoordinateGraph.description (N+m) (.eqZero p) (CenteredSquaredDistanceTerm.term N m)
abbrev Graph := (description N m p).realization
abbrev Original := (Description.mk N (.eqZero p)).realization

noncomputable def base : Graph N m p ≃ₜ (Description.mk (N+m) (.eqZero p)).realization :=
  TermCoordinateGraph.homeomorph _ _ _ (hp.trans (Nat.le_add_right N m)) (CenteredSquaredDistanceTerm.scope N m)

noncomputable def oldPoint (y : Graph N m p) : Original N p :=
  ⟨fun i => (base N m p hp y).val (Fin.castAdd m i),by
    have H := (base N m p hp y).property
    change p.eval (Formula.extend (base N m p hp y).val)=0 at H
    change p.eval (Formula.extend (fun i => (base N m p hp y).val (Fin.castAdd m i)))=0
    apply Eq.trans _ H
    apply Term.eval_congr
    intro i hi
    have HI : i<N := hi.trans_le hp
    have HJ : i<N+m := HI.trans_le (Nat.le_add_right N m)
    simp only [Formula.extend,dite_eq_left HI,dite_eq_left HJ]
    rfl⟩

noncomputable def center (y : Graph N m p) : Fin m → ℝ :=
  fun i => (base N m p hp y).val (Fin.natAdd N i)

theorem old_coordinate (y : Graph N m p) (i : Fin N) :
    (oldPoint N m p hp y).val i=y.val (Fin.castAdd 1 (Fin.castAdd m i)) := rfl

theorem center_coordinate (y : Graph N m p) (i : Fin m) :
    center N m p hp y i=y.val (Fin.castAdd 1 (Fin.natAdd N i)) := rfl

theorem oldPoint_continuous : Continuous (oldPoint N m p hp) :=
  (continuous_pi (fun i => (continuous_apply (Fin.castAdd m i)).comp
    (continuous_subtype_val.comp (base N m p hp).continuous))).subtype_mk _

theorem radius_coordinate (y : Graph N m p) : y.val (Fin.last (N+m))=
    SquaredDistanceFibers.value (center N m p hp y)
      (fun i => (oldPoint N m p hp y).val (Fin.castLE hm i)) := by
  have H := TermCoordinateGraph.objective_coordinate (N+m) (.eqZero p) _
    (hp.trans (Nat.le_add_right N m)) (CenteredSquaredDistanceTerm.scope N m) y
  rw [CenteredSquaredDistanceTerm.eval] at H
  apply H.trans
  apply Finset.sum_congr rfl
  intro i _
  have HI : i.val<N := i.isLt.trans_le hm
  have HJ : i.val<N+m := HI.trans_le (Nat.le_add_right N m)
  have HK : N+i.val<N+m := Nat.add_lt_add_left i.isLt N
  change (Formula.extend (base N m p hp y).val i-
    Formula.extend (base N m p hp y).val (N+i.val))^2=_
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HK]
  rfl

include hp in
theorem eval_append (x : Original N p) (a : Fin m → ℝ) :
    p.eval (Formula.extend (Fin.append x.val a))=0 := by
  apply Eq.trans _ x.property
  apply Term.eval_congr
  intro i hi
  have HI : i<N := hi.trans_le hp
  have HJ : i<N+m := HI.trans_le (Nat.le_add_right N m)
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HJ]
  change Fin.append x.val a (Fin.castAdd m ⟨i,HI⟩)=x.val ⟨i,HI⟩
  exact Fin.append_left _ _ _

noncomputable def lift (a : Fin m → ℝ) (x : Original N p) : Graph N m p :=
  (base N m p hp).symm ⟨Fin.append x.val a,eval_append N m p hp x a⟩

theorem oldPoint_section (a : Fin m → ℝ) (x : Original N p) :
    oldPoint N m p hp (lift N m p hp a x)=x := by
  apply Subtype.ext
  funext i
  change (base N m p hp ((base N m p hp).symm _)).val (Fin.castAdd m i)=x.val i
  rw [Homeomorph.apply_symm_apply]
  exact Fin.append_left _ _ _

theorem center_section (a : Fin m → ℝ) (x : Original N p) :
    center N m p hp (lift N m p hp a x)=a := by
  funext i
  change (base N m p hp ((base N m p hp).symm _)).val (Fin.natAdd N i)=a i
  rw [Homeomorph.apply_symm_apply]
  exact Fin.append_right _ _ _

theorem lift_continuous (a : Fin m → ℝ) : Continuous (lift N m p hp a) :=
  (base N m p hp).symm.continuous.comp
    (((Fin.appendHomeomorph N m).continuous.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _)

theorem lift_forget (y : Graph N m p) :
    lift N m p hp (center N m p hp y) (oldPoint N m p hp y)=y := by
  apply (base N m p hp).injective
  apply Subtype.ext
  unfold lift
  rw [Homeomorph.apply_symm_apply]
  change Fin.append (fun i => (base N m p hp y).val (Fin.castAdd m i))
    (fun i => (base N m p hp y).val (Fin.natAdd N i))=(base N m p hp y).val
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left _ _ _
  · exact Fin.append_right _ _ _

end LeanCanny.Geometry.CenteredRadialGraph
