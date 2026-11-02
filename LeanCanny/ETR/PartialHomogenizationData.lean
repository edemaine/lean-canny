/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationSize
public import LeanCanny.ETR.NNFEncoding

/-! # Total bounded raw-data algebra for partial homogenization

The annotation is capped at the original allowance. Oversized nodes use zero.
For a genuine input expression and its original syntax degree/size bounds,
every subtree retains the exact division-free homogenization.
-/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationData
open LeanCanny.Encoding
open PartialHomogenization

def degree (k D : ℕ) : Data → ℕ
  | .l [tag,a] => if tag=Codec.unary 1 then
      if (a.size-2)/2 < k then 0 else min 1 D else 0
  | .l [tag,a,b] => if tag=Codec.unary 2 then max (degree k D a) (degree k D b)
      else if tag=Codec.unary 3 then min (degree k D a+degree k D b) D else 0
  | _ => 0

theorem degree_le (k D : ℕ) (d : Data) : degree k D d ≤ D := by
  induction d using Data.inductionChildren with
  | node xs ih =>
      rcases xs with _ | ⟨tag,_ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩⟩
      · simp [degree]
      · simp [degree]
      · simp only [degree]; split_ifs <;> omega
      · have HA := ih a (by simp)
        have HB := ih b (by simp)
        simp only [degree]
        split_ifs <;> omega
      · simp [degree]

def raw (k D : ℕ) : Data → Data
  | .l [tag,a] => if tag=Codec.unary 0 then .l [tag,a]
      else if tag=Codec.unary 1 then (Term.var ((a.size-2)/2+1)).toData
      else (Term.const 0).toData
  | .l [tag,a,b] => if tag=Codec.unary 2 then
      let d := max (degree k D a) (degree k D b)
      .l [Codec.unary 2,
        .l [Codec.unary 3,((Term.var 0).power (d-degree k D a)).toData,raw k D a],
        .l [Codec.unary 3,((Term.var 0).power (d-degree k D b)).toData,raw k D b]]
      else if tag=Codec.unary 3 then .l [Codec.unary 3,raw k D a,raw k D b]
      else (Term.const 0).toData
  | _ => (Term.const 0).toData

def bounded (k D L : ℕ) (d : Data) : Data :=
  if d.size ≤ L then raw k D d else (Term.const 0).toData

theorem degree_term (k D : ℕ) (t : Term) (ht : t.degreeBound ≤ D) :
    degree k D t.toData = physicalDegree k t := by
  induction t with
  | const z => simp [Term.toData,degree,physicalDegree,Codec.unary]
  | var i =>
      have HD : 1 ≤ D := ht
      simp only [Term.toData,degree,Codec.unary_size,physicalDegree]
      simp [Nat.min_eq_left HD]
  | add t u ihT ihU =>
      have HT : t.degreeBound ≤ D := (Nat.le_max_left _ _).trans ht
      have HU : u.degreeBound ≤ D := (Nat.le_max_right _ _).trans ht
      simp [Term.toData,degree,Codec.unary,physicalDegree,ihT HT,ihU HU]
  | mul t u ihT ihU =>
      have HT : t.degreeBound ≤ D := by change t.degreeBound+u.degreeBound ≤ D at ht; omega
      have HU : u.degreeBound ≤ D := by change t.degreeBound+u.degreeBound ≤ D at ht; omega
      have HD : physicalDegree k t+physicalDegree k u ≤ D :=
        (Nat.add_le_add (physicalDegree_le k t) (physicalDegree_le k u)).trans ht
      simp [Term.toData,degree,Codec.unary,physicalDegree,ihT HT,ihU HU,Nat.min_eq_left HD]

theorem raw_term (k D : ℕ) (t : Term) (ht : t.degreeBound ≤ D) :
    raw k D t.toData = (homogenize k t).toData := by
  induction t with
  | const z => simp [Term.toData,raw,homogenize,Codec.unary]
  | var i =>
      have HI : (2*i+2-2)/2=i := by omega
      have H01 : Codec.unary 1 ≠ Codec.unary 0 := by simp [Codec.unary]
      simp only [Term.toData,raw,homogenize,Codec.unary_size,HI,ite_true]
      exact ite_eq_right H01
  | add t u ihT ihU =>
      have HT : t.degreeBound ≤ D := (Nat.le_max_left _ _).trans ht
      have HU : u.degreeBound ≤ D := (Nat.le_max_right _ _).trans ht
      simp [Term.toData,raw,Codec.unary,homogenize,degree_term k D t HT,degree_term k D u HU,ihT HT,ihU HU]
  | mul t u ihT ihU =>
      have HT : t.degreeBound ≤ D := by change t.degreeBound+u.degreeBound ≤ D at ht; omega
      have HU : u.degreeBound ≤ D := by change t.degreeBound+u.degreeBound ≤ D at ht; omega
      simp [Term.toData,raw,Codec.unary,homogenize,ihT HT,ihU HU]

theorem bounded_term (k D L : ℕ) (t : Term) (ht : t.degreeBound ≤ D) (hL : t.toData.size ≤ L) :
    bounded k D L t.toData = (homogenize k t).toData := by
  rw [bounded,ite_eq_left hL,raw_term k D t ht]

end LeanCanny.ETR.PartialHomogenizationData
