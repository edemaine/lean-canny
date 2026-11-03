/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SingleRootSignCount
public import Mathlib.Topology.Instances.Real.Lemmas
/-! # Open root intervals from two one-sided Tarski queries

A common small positive epsilon excludes roots at either endpoint. Counts
use all distinct real roots, including repeated roots of the polynomial.
-/
@[expose] public section
namespace LeanCanny.Algebra.RealRootOpenIntervalQueries
open Polynomial Set
open scoped Classical BigOperators

private theorem point_signs (a b r : ℝ) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→
      SignType.sign (r-(a+ε))=(if r≤a then SignType.neg else SignType.pos) ∧
      SignType.sign (r-(b-ε))=(if r<b then SignType.neg else SignType.pos) :=by
  let u:=if r≤a then 1 else r-a
  let v:=if r<b then b-r else 1
  have HU : 0<u:=by dsimp only [u];split_ifs <;> linarith
  have HV : 0<v:=by dsimp only [v];split_ifs <;> linarith
  refine ⟨min u v,lt_min HU HV,fun ε he heη=>?_⟩
  have hU:=heη.trans_le (min_le_left u v)
  have hV:=heη.trans_le (min_le_right u v)
  constructor
  · by_cases hr : r≤a
    · rw [ite_eq_left hr]
      exact sign_neg (by linarith)
    · rw [ite_eq_right hr]
      rw [show u=r-a from ite_eq_right hr] at hU
      exact sign_pos (by linarith)
  · by_cases hr : r<b
    · rw [ite_eq_left hr]
      rw [show v=b-r from ite_eq_left hr] at hV
      exact sign_neg (by linarith)
    · rw [ite_eq_right hr]
      exact sign_pos (by linarith)

private theorem finite_point_signs (s : Finset ℝ) (a b : ℝ) :
    ∃η : ℝ,0<η ∧ ∀r∈s,∀ε : ℝ,0<ε→ε<η→
      SignType.sign (r-(a+ε))=(if r≤a then SignType.neg else SignType.pos) ∧
      SignType.sign (r-(b-ε))=(if r<b then SignType.neg else SignType.pos) :=by
  induction s using Finset.induction_on with
  | empty=>exact ⟨1,by norm_num,by simp⟩
  | @insert r s _ ih=>
    obtain ⟨η,hη,HS⟩:=ih
    obtain ⟨ζ,hζ,HR⟩:=point_signs a b r
    refine ⟨min η ζ,lt_min hη hζ,fun x hx ε he heη=>?_⟩
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact HR ε he (heη.trans_le (min_le_right _ _))
    · exact HS x hx ε he (heη.trans_le (min_le_left _ _))

theorem count_identity (p : ℝ[X]) {a b : ℝ} (hab : a<b) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→
      RootSignQueries.tarskiQuery p (X-C (a+ε))-RootSignQueries.tarskiQuery p (X-C (b-ε))=
        2*((p.roots.toFinset.filter (fun r=>a<r ∧ r<b)).card:ℤ) :=by
  obtain ⟨η,hη,HS⟩:=finite_point_signs p.roots.toFinset a b
  refine ⟨η,hη,fun ε he heη=>?_⟩
  have HC : ((p.roots.toFinset.filter (fun r=>a<r ∧ r<b)).card:ℤ)=
      ∑r∈p.roots.toFinset,if a<r ∧ r<b then (1:ℤ) else 0 :=by
    rw [←Finset.sum_filter]
    simp
  rw [HC,Finset.mul_sum]
  simp only [RootSignQueries.tarskiQuery,RootSignQueries.signSum,Polynomial.eval_sub,Polynomial.eval_X,
    Polynomial.eval_C,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rcases HS r hr ε he heη with ⟨HL,HR⟩
  rw [HL,HR]
  by_cases ha : r≤a
  · have hb : r<b:=ha.trans_lt hab
    norm_num [ha,hb,not_lt.mpr ha]
  · by_cases hb : r<b
    · norm_num [ha,hb,lt_of_not_ge ha]
    · norm_num [ha,hb]

theorem finite_empty_iff (p : ℝ[X]) {a b : ℝ} (hab : a<b) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→
      ((∀ r ∈ p.roots.toFinset, r ∉ Ioo a b)↔
        RootSignQueries.tarskiQuery p (X-C (a+ε))=RootSignQueries.tarskiQuery p (X-C (b-ε))) :=by
  obtain ⟨η,hη,HS⟩:=count_identity p hab
  refine ⟨η,hη,fun ε he heη=>?_⟩
  have HZ : (p.roots.toFinset.filter (fun r=>a<r ∧ r<b)).card=0↔∀ r ∈ p.roots.toFinset, r ∉ Ioo a b:=by
    rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    rfl
  have HE:=HS ε he heη
  rw [←HZ]
  omega

theorem empty_iff (p : ℝ[X]) (hp : p≠0) {a b : ℝ} (hab : a<b) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→
      ((∀ r, p.eval r=0 → r ∉ Ioo a b)↔
        RootSignQueries.tarskiQuery p (X-C (a+ε))=RootSignQueries.tarskiQuery p (X-C (b-ε))) :=by
  simpa only [Multiset.mem_toFinset,Polynomial.mem_roots hp,Polynomial.IsRoot] using finite_empty_iff p hab

end LeanCanny.Algebra.RealRootOpenIntervalQueries
