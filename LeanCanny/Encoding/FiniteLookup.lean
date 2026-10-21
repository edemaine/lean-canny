/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BracketsFP

/-! # Polynomial-time replacement through a fixed finite lookup table -/

@[expose] public section

namespace LeanCanny.Encoding.FiniteLookup

open Brackets

variable {ι : Type*}

/-- Match a polynomial-time key against finitely many fixed words. A match writes
the corresponding fixed output prefix followed by the polynomial-time tail. -/
def rewrite (keys : List ι) (pattern output : ι → List Bool)
    (key tail : List Bool → List Bool) (fallback : List Bool) (xs : List Bool) : List Bool :=
  keys.foldr (fun i rest => if key xs = pattern i then output i ++ tail xs else rest) fallback

theorem rewrite_mem_FP (keys : List ι) (pattern output : ι → List Bool)
    {key tail : List Bool → List Bool} (hkey : key ∈ FP) (htail : tail ∈ FP)
    (fallback : List Bool) : rewrite keys pattern output key tail fallback ∈ FP := by
  induction keys with
  | nil => exact constFn_mem_FP fallback
  | cons i keys ih =>
      exact (stringEq_fppred hkey (constFn_mem_FP (pattern i))).ite_mem_FP
        (appendFn_mem_FP (constFn_mem_FP (output i)) htail) ih

theorem rewrite_match (keys : List ι) (pattern output : ι → List Bool)
    (key tail : List Bool → List Bool) (fallback xs : List Bool)
    (hpattern : Function.Injective pattern) (i : ι) (hi : i ∈ keys)
    (hkey : key xs = pattern i) :
    rewrite keys pattern output key tail fallback xs = output i ++ tail xs := by
  induction keys with
  | nil => simp at hi
  | cons j keys ih =>
      by_cases hj : pattern j = pattern i
      · have heq := hpattern hj
        subst j
        simp [rewrite, hkey]
      · have hij : i ≠ j := by intro h; subst j; exact hj rfl
        have himem : i ∈ keys := (List.mem_cons.mp hi).resolve_left hij
        have htest : key xs ≠ pattern j := by intro he; exact hj (he.symm.trans hkey)
        simp only [rewrite, List.foldr_cons, ite_eq_right htest]
        exact ih himem

theorem rewrite_miss (keys : List ι) (pattern output : ι → List Bool)
    (key tail : List Bool → List Bool) (fallback xs : List Bool)
    (h : ∀ i ∈ keys, key xs ≠ pattern i) :
    rewrite keys pattern output key tail fallback xs = fallback := by
  induction keys with
  | nil => rfl
  | cons i keys ih =>
      simp only [rewrite, List.foldr_cons, ite_eq_right (h i (List.mem_cons_self ..))]
      exact ih (fun j hj => h j (List.mem_cons_of_mem i hj))

end LeanCanny.Encoding.FiniteLookup
