/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenization
/-! # Polynomial expression-size bounds for partial homogenization

These bounds concern the actual expression tree, including balancing powers;
no expanded-monomial representation is used.
-/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenization

theorem size_power (t : Term) (n : ℕ) :
    (t.power n).toData.size = 14+n*(t.toData.size+10) := by
  induction n with
  | zero => simp [Term.power]
  | succ n ih => simp only [Term.power,Term.dataSize_mul,ih,Nat.add_mul,Nat.one_mul]; omega

theorem size_homogenize (k D : ℕ) (t : Term) (ht : t.degreeBound ≤ D) :
    (homogenize k t).toData.size ≤ (36*D+60)*t.toData.size := by
  induction t with
  | const z => exact Nat.le_mul_of_pos_left _ (by omega)
  | var i => simp only [homogenize,Term.dataSize_var]; nlinarith
  | add t u ihT ihU =>
      have HDt : t.degreeBound ≤ D := (Nat.le_max_left _ _).trans ht
      have HDu : u.degreeBound ≤ D := (Nat.le_max_right _ _).trans ht
      have HT := ihT HDt
      have HU := ihU HDu
      have HPt := (physicalDegree_le k t).trans HDt
      have HPu := (physicalDegree_le k u).trans HDu
      simp only [homogenize,Term.dataSize_add,Term.dataSize_mul,size_power,Term.dataSize_var]
      have Ht : max (physicalDegree k t) (physicalDegree k u)-physicalDegree k t ≤ D := by omega
      have Hu : max (physicalDegree k t) (physicalDegree k u)-physicalDegree k u ≤ D := by omega
      nlinarith
  | mul t u ihT ihU =>
      have HDt : t.degreeBound ≤ D := by change t.degreeBound+u.degreeBound ≤ D at ht; omega
      have HDu : u.degreeBound ≤ D := by change t.degreeBound+u.degreeBound ≤ D at ht; omega
      have HT := ihT HDt
      have HU := ihU HDu
      simp only [homogenize,Term.dataSize_mul]
      nlinarith

theorem size_padded (k D : ℕ) (t : Term) (ht : t.degreeBound ≤ D) :
    (padded k D t).toData.size ≤ (54*D+84)*(t.toData.size+1) := by
  have H := size_homogenize k D t ht
  have HP : D-physicalDegree k t ≤ D := Nat.sub_le _ _
  simp only [padded,Term.dataSize_mul,size_power,Term.dataSize_var]
  nlinarith

end LeanCanny.ETR.PartialHomogenization
