/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitnessCanonical
public import LeanCanny.Connectivity.EndpointValidation
/-! # The strict-conjunct reduction retains the original singleton validation

A witness equation can discard old endpoint candidates. Original endpoint
validation is therefore retained explicitly. The exact canonical-language
identity below covers inconsistent, nonunique and outside-space endpoints;
the existing native endpoint validator supplies its first conjunct.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaStrictWitness
open ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem endpoint_projection_holds (n : ℕ) (p s : Formula) (t : Term)
    (hp : p.arity ≤ n) (ht : t.arity ≤ n) (hs : s.arity ≤ n)
    (z : (lifted n p t).realization) (HZ : (endpoint n s t).Holds (Formula.extend z.val)) :
    s.Holds (Formula.extend (projection n p t hp ht z).val) := by
  have HS : s.Holds (Formula.extend z.val) := HZ.1
  apply (s.holds_congr _ _ (fun i hi => ?_)).mp HS
  have HI : i<n := hi.trans_le hs
  change (if h : i<n+2 then z.val ⟨i,h⟩ else 0) =
    (if h : i<n then (projection n p t hp ht z).val ⟨i,h⟩ else 0)
  simp only [dite_eq_left HI,dite_eq_left (show i<n+2 by omega)]
  exact (projection_val n p t hp ht z ⟨i,HI⟩).symm

theorem reachable_iff_of_denotes (n : ℕ) (p s d : Formula) (t : Term)
    (hp : p.arity ≤ n) (ht : t.arity ≤ n) (a b : Fin n → ℝ)
    (hs : Denotes n s a) (hd : Denotes n d b) :
    (PointQuery.mk (lifted n p t) (endpoint n s t) (endpoint n d t)).Reachable ↔
      (PointQuery.mk (original n p t) s d).Reachable := by
  constructor
  · rintro ⟨_,y,z,HY,HZ,HJ⟩
    let Y : (lifted n p t).realization := ⟨y,HJ.source_mem⟩
    let Z : (lifted n p t).realization := ⟨z,HJ.target_mem⟩
    have HYa : (projection n p t hp ht Y).val = a := (hs.2 _).mp
      (endpoint_projection_holds n p s t hp ht hs.1 Y ((HY.2 y).mpr rfl))
    have HZb : (projection n p t hp ht Z).val = b := (hd.2 _).mp
      (endpoint_projection_holds n p d t hp ht hd.1 Z ((HZ.2 z).mpr rfl))
    apply (PointQuery.reachable_iff hs hd).mpr
    refine ⟨max_le hp ht,?_⟩
    rw [← HYa,← HZb]
    exact (ambient_joined_iff n p t hp ht Y Z).mp HJ
  · intro H
    obtain ⟨_,x,y,HX,HY,HJ⟩ := H
    let X : (original n p t).realization := ⟨x,HJ.source_mem⟩
    let Y : (original n p t).realization := ⟨y,HJ.target_mem⟩
    exact (reachable_iff n p s d t hp ht X Y HX HY).mpr
      ⟨max_le hp ht,x,y,HX,HY,HJ⟩

theorem point_language_guarded_iff (n : ℕ) (p s d : Formula) (t : Term)
    (hp : p.arity ≤ n) (ht : t.arity ≤ n) :
    (Input.point (PointQuery.mk (original n p t) s d)).encode ∈ pointLanguage ↔
      (Input.point (PointQuery.mk (original n p t) s d)).encode ∈ EndpointValidation.validEndpointLanguage ∧
      (Input.point (PointQuery.mk (lifted n p t) (endpoint n s t) (endpoint n d t))).encode ∈ pointLanguage := by
  rw [point_encode_mem_iff,EndpointValidation.validEndpoint_encode,point_encode_mem_iff]
  constructor
  · intro H
    obtain ⟨HW,a,b,HA,HB,HJ⟩ := H
    exact ⟨⟨⟨a,HA⟩,⟨b,HB⟩⟩,(reachable_iff_of_denotes n p s d t hp ht a b HA HB).mpr ⟨HW,a,b,HA,HB,HJ⟩⟩
  · rintro ⟨⟨⟨a,HA⟩,⟨b,HB⟩⟩,H⟩
    exact (reachable_iff_of_denotes n p s d t hp ht a b HA HB).mp H

end LeanCanny.Connectivity.FormulaStrictWitness
