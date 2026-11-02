/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialFiniteComponents
public import LeanCanny.Geometry.SquaredDistanceFibers
public import Mathlib.Topology.Connected.TotallyDisconnected
/-! # Actual closed-ball polynomial lifts have finite connected components

One squared slack coordinate realizes the old squared-distance sublevel. Its
projection retains the literal old tuple and is surjective, so finite components
of the constructed polynomial zero set pass to every old closed-ball section.
The new degree is bounded once by 2D+4, independent of the center and radius.
-/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialBallComponents
open Set MvPolynomial CoerciveComponentSampling
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def polynomial (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  (rename Fin.castSucc q)^2+((∑ i, (X i.castSucc-C (a i))^2)+X (Fin.last n)^2-C r)^2

noncomputable def old (x : Fin (n+1) → ℝ) : Fin n → ℝ := fun i => x i.castSucc
noncomputable def Section (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ) :=
  {x : Zeros q | SquaredDistanceFibers.value a x.val≤r}

theorem zero_iff (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ) (x : Fin (n+1) → ℝ) :
    (polynomial q a r).eval x=0 ↔ q.eval (old x)=0 ∧ SquaredDistanceFibers.value a (old x)+x (Fin.last n)^2=r := by
  simp only [polynomial,eval_add,eval_pow,eval_rename,eval_sub,eval_sum,eval_X,eval_C]
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp only [sq_eq_zero_iff,sub_eq_zero,SquaredDistanceFibers.value,old]
  rfl

noncomputable def projection (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ)
    (x : Zeros (polynomial q a r)) : Section q a r :=
  ⟨⟨old x.val,((zero_iff q a r x.val).mp x.property).1⟩,by
    have H := ((zero_iff q a r x.val).mp x.property).2
    change SquaredDistanceFibers.value a (old x.val)≤r
    linarith [sq_nonneg (x.val (Fin.last n))]⟩

theorem continuous_projection (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ) : Continuous (projection q a r) :=
  ((continuous_pi (fun i => (continuous_apply i.castSucc).comp continuous_subtype_val)).subtype_mk _).subtype_mk _

theorem projection_surjective (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ) : Function.Surjective (projection q a r) := by
  intro x
  let s := Real.sqrt (r-SquaredDistanceFibers.value a x.val.val)
  let y : Fin (n+1) → ℝ := Fin.snoc (α := fun _ : Fin (n+1) => ℝ) x.val.val s
  have HE : old y=x.val.val := by
    funext i
    change Fin.snoc (α := fun _ : Fin (n+1) => ℝ) x.val.val s i.castSucc=x.val.val i
    exact Fin.snoc_castSucc (α := fun _ : Fin (n+1) => ℝ) s x.val.val i
  have HL : y (Fin.last n)=s := Fin.snoc_last _ _
  have HQ : (polynomial q a r).eval y=0 := by
    rw [zero_iff,HE,HL]
    refine ⟨x.val.property,?_⟩
    have HS : s^2=r-SquaredDistanceFibers.value a x.val.val := Real.sq_sqrt (sub_nonneg.mpr x.property)
    linarith
  refine ⟨⟨y,HQ⟩,?_⟩
  apply Subtype.ext
  exact Subtype.ext HE

theorem degree (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) (a : Fin n → ℝ) (r : ℝ) :
    (polynomial q a r).totalDegree≤2*D+4 := by
  have Hq : ((rename Fin.castSucc q)^2).totalDegree≤2*D :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ((totalDegree_rename_le _ _).trans hD))
  have Hs (i : Fin n) : ((X i.castSucc-C (a i) : MvPolynomial (Fin (n+1)) ℝ)^2).totalDegree≤2 := by
    have HL : (X i.castSucc-C (a i) : MvPolynomial (Fin (n+1)) ℝ).totalDegree≤1 :=
      (totalDegree_sub _ _).trans (by simp)
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 HL)
  have HI : ((∑ i, (X i.castSucc-C (a i))^2)+X (Fin.last n)^2-C r : MvPolynomial (Fin (n+1)) ℝ).totalDegree≤2 := by
    apply (totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    apply (totalDegree_add _ _).trans
    exact max_le (totalDegree_finsetSum_le (fun i _ => Hs i)) (by simp)
  have HB : (((∑ i, (X i.castSucc-C (a i))^2)+X (Fin.last n)^2-C r : MvPolynomial (Fin (n+1)) ℝ)^2).totalDegree≤4 :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 HI)
  exact (totalDegree_add _ _).trans (max_le (Hq.trans (Nat.le_add_right _ 4)) (HB.trans (Nat.le_add_left 4 _)))

theorem components_finite (q : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (r : ℝ) :
    Finite (ConnectedComponents (Section q a r)) := by
  let : Finite (ConnectedComponents (Zeros (polynomial q a r))) :=
    PolynomialFiniteComponents.components_finite _ (2*q.totalDegree+4) (degree q _ le_rfl a r)
  exact Finite.of_surjective _ ((continuous_projection q a r).connectedComponentsMap_surjective (projection_surjective q a r))
end LeanCanny.Geometry.PolynomialBallComponents
