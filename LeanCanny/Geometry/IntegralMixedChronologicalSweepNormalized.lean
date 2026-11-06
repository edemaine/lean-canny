/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
public import LeanCanny.Algebra.IntegralMixedNumericalSweepBad
/-! # Literal chronological frozen heights determine the normalized sweep -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem normalized_data {n m : ℕ} (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (Q : ℤ) (hQ : Q≠0) (values : Fin m→ℝ) (i : ℕ) (hi : i<d.labels.length+1) :
    IntegralMixedNumericalSweep.normalized ((data d hk g j hg hj).rule Q hQ) values i=
      if h : i<d.labels.length then C (values (d.reference ⟨i,h⟩)) else X := by
  let k : Fin (n+1) := ⟨i,by omega⟩
  have HE : i=k.val := rfl
  rw [HE,IntegralMixedNumericalSweep.normalized_at]
  have HP := (prefix_frozen d hk).permutation
  simp only [IntegralMixedCutRecordConstructor.Data.rule,data,pointData_rule,pointRule,critical,HP,
    Equiv.refl_apply]
  change (C (((frame d hk).heights k).evaluate values/((frame d hk).scales k:ℝ))+
    if k=next d hk then (C (((frame d hk).scales k:ℝ)⁻¹))*X else 0)=
      if h : k.val<d.labels.length then C (values (d.reference ⟨k.val,h⟩)) else X
  by_cases h : i<d.labels.length
  · have Hkh : k≠next d hk := by intro E;have :=congrArg Fin.val E;change i=d.labels.length at this;omega
    rw [ite_eq_right Hkh]
    have HH := d.height ⟨i,h⟩
    change (frame d hk).heights k=_ at HH
    have HS : (frame d hk).scales k=1 := rfl
    rw [HH,HS]
    simp only [Int.cast_one,div_one,add_zero,dite_eq_left (show k.val<d.labels.length from h)]
    apply congrArg C
    change (if _ : (d.reference ⟨i,h⟩).val<m then _ else 0)=_
    rw [dite_eq_left (d.reference ⟨i,h⟩).isLt]
    rfl
  · have Hke : k=next d hk := Fin.ext (by change i=d.labels.length;omega)
    rw [Hke,ite_eq_left rfl]
    have HN := d.free_normal (next d hk) (next_free d hk)
    change (frame d hk).scales (next d hk)=1 ∧(frame d hk).heights (next d hk)=.constant 0 at HN
    rw [HN.1,HN.2]
    simp only [AffineExpr.evaluate,Int.cast_zero,zero_div,C_0,zero_add,Int.cast_one,inv_one,C_1,one_mul,
      next,dite_eq_right (Nat.lt_irrefl _)]

theorem data_rule_offset {n m : ℕ} (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (Q : ℤ) (hQ : Q≠0) : ((data d hk g j hg hj).rule Q hQ).critical.offset.val=d.labels.length+1 :=
  pointData_offset d hk g j hg hj

theorem data_rule_objective {n m : ℕ} (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (Q : ℤ) (hQ : Q≠0) : ((data d hk g j hg hj).rule Q hQ).critical.objective=g.val-(d.labels.length+1) := by
  change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm g).val-
    (frame d hk).frozen.card=_
  rw [(prefix_frozen d hk).permutation,frozen_card]
  rfl

end LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
