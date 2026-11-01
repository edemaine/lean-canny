/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateCoordinates
/-! # The literal native radius term bounds every original atom -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def radius (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) : ℝ :=
  (BoundedMonotoneGateSource.budget F c).eval (Formula.extend x)

theorem radius_continuous (F : Family) (c : List Bool) : Continuous (radius F c) :=
  FormulaStrictWitness.continuous_eval _ _

private theorem member_square (ts : List Term) (t : Term) (ht : t∈ts) (env : ℕ → ℝ) :
    (t.eval env)^2≤(Term.sumSquares ts).eval env := by
  induction ts with
  | nil => simp at ht
  | cons p ps IH =>
    rcases List.mem_cons.mp ht with H | H
    · subst t
      have HN := Term.eval_sumSquares_nonneg ps env
      change (p.eval env)^2≤p.eval env*p.eval env+(Term.sumSquares ps).eval env
      nlinarith
    · have HE := IH H
      change (t.eval env)^2≤p.eval env*p.eval env+(Term.sumSquares ps).eval env
      nlinarith [sq_nonneg (p.eval env)]

theorem atom_radius (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ)
    (i : Fin (F.count c)) : max (MonotoneGateCircles.atomValue F c i x) 0≤radius F c x := by
  have HT : F.atom (BoundedMonotoneGateSource.query c i.val)∈BoundedMonotoneGateSource.atoms F c :=
    List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩
  have HE := member_square _ _ HT (Formula.extend x)
  have HN := Term.eval_sumSquares_nonneg (BoundedMonotoneGateSource.atoms F c) (Formula.extend x)
  change max ((F.atom (BoundedMonotoneGateSource.query c i.val)).eval (Formula.extend x)) 0≤_
  simp only [radius,BoundedMonotoneGateSource.budget,Term.eval,Int.cast_one,SumSquares.eval_accumulate,
    Int.cast_zero,zero_add]
  rw [max_le_iff]
  constructor
  · nlinarith [sq_nonneg ((F.atom (BoundedMonotoneGateSource.query c i.val)).eval (Formula.extend x)-1/2)]
  · linarith

theorem radius_eval (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c) :
    (BoundedMonotoneGateSource.budget F c).eval (Formula.extend y.val)=
      radius F c (circles F c ha hk y).val.1 := by
  apply Term.eval_congr
  intro j hj
  have HJ : j < F.dimension c := hj.trans_le (BoundedMonotoneGateSource.budget_arity F c ha)
  have HY : j < total F c := by dsimp [total,base]; omega
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HY]
  exact (circles_old F c ha hk y ⟨j,HJ⟩).symm

theorem slack_eval (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) (y : ZeroSet F c)
    (u : Fin (F.count c) → CircularWitness.Plane) (i : Fin (F.count c)) :
    (BoundedMonotoneGateSource.slack F (BoundedMonotoneGateSource.query c i.val)).eval
      (Formula.extend (encode F c (y.val,u)))=
      ‖(circles F c ha hk y).val.2 i‖^2+‖u i‖^2-radius F c (circles F c ha hk y).val.1 := by
  have HW (j : Fin 2) : Formula.extend (encode F c (y.val,u)) (F.dimension c+2*i.val+j.val)=
      (circles F c ha hk y).val.2 i j := by
    have HJ : F.dimension c+2*i.val+j.val < total F c := by
      have H:=i.isLt; have H':=j.isLt; dsimp [total,base]; omega
    have HJ' : F.dimension c+2*i.val+j.val < BoundedMonotoneGateSource.total F c := by
      dsimp [BoundedMonotoneGateSource.total,total,base] at HJ ⊢; omega
    simp only [Formula.extend,dite_eq_left HJ']
    rw [circles_fresh]
    exact FiniteCircularCoordinates.encode_old _ _ (y.val,u) ⟨_,HJ⟩
  have HU (j : Fin 2) : Formula.extend (encode F c (y.val,u))
      (F.dimension c+3*F.count c+2*i.val+j.val)=u i j := by
    have HE := FiniteCircularCoordinates.fresh_eval (total F c) (F.count c) (y.val,u) i j
    convert HE using 1; congr 1; dsimp [total,base]; omega
  have HB : (BoundedMonotoneGateSource.budget F c).eval (Formula.extend (encode F c (y.val,u)))=
      radius F c (circles F c ha hk y).val.1 := by
    rw [old_eval F c _ _ ((BoundedMonotoneGateSource.budget_arity F c ha).trans (by dsimp [total,base]; omega)),
      radius_eval F c ha hk y]
  have HN (w : CircularWitness.Plane) : ‖w‖^2=(w 0)^2+(w 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  have HW0 := HW 0
  have HW1 := HW 1
  have HU0 := HU 0
  have HU1 := HU 1
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero] at HW0 HW1 HU0 HU1
  simp only [BoundedMonotoneGateSource.slack,Term.eval,witnessIndex,BoundedMonotoneGateSource.slackIndex,
    dimension,count,index,BoundedMonotoneGateSource.query,pairFst_pair,pairSnd_pair,
    List.length_replicate,Bool.toNat_false,Bool.toNat_true,Nat.add_zero,Int.cast_neg,Int.cast_one]
  rw [HW0,HW1,HU0,HU1,HB,HN,HN]
  ring

end LeanCanny.Connectivity.BoundedGateCoordinates
