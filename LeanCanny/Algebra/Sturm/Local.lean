/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/Sturm/Local.lean.
Changes: selected proof slice, project namespace, real specialization where needed,
and compatibility with the pinned Mathlib. See STURM_SOURCES.md.
-/
module

public import LeanCanny.Algebra.Sturm.Signs

/-! # Local variation jumps for alternating polynomial chains

`IsAlternating` records the sign conditions of a chain whose last entry has no roots.
Interior zeros preserve sign variations. Crossing a simple root of the first
entry changes the variation by the sign of its derivative times the second entry.
These local identities supply the signed root sum in `Sturm.Sum`.
-/

public section

namespace LeanCanny.Algebra.Sturm

open Polynomial List

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- An alternating chain has opposite neighbors at every interior zero and
no real zero in its last entry. These are the properties of a signed remainder
chain after its common polynomial factor has been removed. -/
structure IsAlternating (cs : List (Polynomial R)) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero : ∀ q ∈ cs, q ≠ 0
  /-- The terminal polynomial has no root in the coefficient ring. -/
  last : ∀ q, cs.getLast? = some q → ∀ r, q.eval r ≠ 0
  /-- At an interior zero the adjacent values are nonzero and have opposite signs. -/
  alternate : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
    cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → ∀ r, q1.eval r = 0 →
    q0.eval r * q2.eval r < 0

namespace IsAlternating

omit [IsStrictOrderedRing R] in
theorem tail {p : Polynomial R} {cs : List (Polynomial R)} (h : IsAlternating (p :: cs)) :
    IsAlternating cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  last q hq r := by
    cases cs with
    | nil => simp at hq
    | cons q0 rest => exact h.last q (by simpa using hq) r
  alternate i q0 q1 q2 h0 h1 h2 r hz :=
    h.alternate (i + 1) q0 q1 q2
      (by simpa using h0) (by simpa using h1) (by simpa using h2) r hz

/-- An alternating chain has the same variations at two points if no entry vanishes
at the first, the head does not vanish at the second, and all surviving signs agree. -/
theorem signVariationsAt_eq {cs : List (Polynomial R)} (h : IsAlternating cs) (a r : R)
    (hne : ∀ q ∈ cs, q.eval a ≠ 0)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hsame : ∀ q ∈ cs, q.eval r ≠ 0 →
      SignType.sign (q.eval a) = SignType.sign (q.eval r)) :
    signVariationsAt cs a = signVariationsAt cs r :=
  signVariationsAt_eq_of_alternate cs a r hne hfront (fun q hq => h.last q hq r)
    (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 r) hsame

omit [IsStrictOrderedRing R] in
/-- Consecutive entries of an alternating chain cannot both vanish. -/
theorem second_eval_ne_zero {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : IsAlternating (p :: q :: cs)) {r : R} (hr : p.eval r = 0) : q.eval r ≠ 0 := by
  cases cs with
  | nil => exact h.last q (by simp) r
  | cons s cs =>
    intro hq
    exact left_ne_zero_of_mul (h.alternate 0 p q s rfl rfl rfl r hq).ne hr

end IsAlternating

end OrderedRing



namespace IsAlternating

/-- Crossing isolated interior zeros does not change variations. -/
theorem signVariationsAt_nonroot {cs : List (Polynomial ℝ)} (h : IsAlternating cs) {a r b : ℝ}
    (har : a < r) (hrb : r < b)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hz : ∀ q ∈ cs, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    signVariationsAt cs a = signVariationsAt cs r ∧
      signVariationsAt cs r = signVariationsAt cs b := by
  have hab := (har.trans hrb).le
  constructor
  · refine h.signVariationsAt_eq a r
      (fun q hq => hz q hq a ⟨le_rfl, hab⟩ har.ne) hfront ?_
    intro q hq hqr
    exact (signs_at_nonroot q har hrb hqr (hz q hq)).1
  · symm
    refine h.signVariationsAt_eq b r
      (fun q hq => hz q hq b ⟨hab, le_rfl⟩ hrb.ne.symm) hfront ?_
    intro q hq hqr
    exact (signs_at_nonroot q har hrb hqr (hz q hq)).2

/-- At a simple root of the head, the variation jump is the sign of the
product of the head derivative and the second entry. -/
theorem root_jump {p q : Polynomial ℝ} {cs : List (Polynomial ℝ)}
    (h : IsAlternating (p :: q :: cs)) {a r b : ℝ} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ s ∈ p :: q :: cs, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  have hq := h.second_eval_ne_zero hr
  have hab := (har.trans hrb).le
  have ht := h.tail.signVariationsAt_nonroot har hrb
    (fun s hs => by cases hs; simpa using hq)
    (fun s hs => hz s (List.mem_cons_of_mem _ hs))
  have hpz := hz p (by simp)
  obtain ⟨hpa, hpb⟩ := signs_at_root p har hrb hr hd hpz
  obtain ⟨hqa, hqb⟩ := signs_at_nonroot q har hrb hq (hz q (by simp))
  have hqa0 := hz q (by simp) a ⟨le_rfl, hab⟩ har.ne
  have hqb0 := hz q (by simp) b ⟨hab, le_rfl⟩ hrb.ne.symm
  have ha : signVariationsAt (p :: q :: cs) a =
      (if -SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
      signVariationsAt (q :: cs) a := by
    rw [signVariationsAt_cons, List.map_cons, firstSign_cons_of_ne_zero _ hqa0,
      hpa, hqa, neg_mul, ← sign_mul]
  have hb : signVariationsAt (p :: q :: cs) b =
      (if SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
      signVariationsAt (q :: cs) b := by
    rw [signVariationsAt_cons, List.map_cons, firstSign_cons_of_ne_zero _ hqb0,
      hpb, hqb, ← sign_mul]
  rw [ha, hb, ht.1.trans ht.2, Nat.cast_add, Nat.cast_add]
  have numeric (s : SignType) :
      ((if -s = -1 then 1 else 0 : ℕ) : ℤ) -
        ((if s = -1 then 1 else 0 : ℕ) : ℤ) = (s : ℤ) := by
    cases s <;> decide
  have := numeric (SignType.sign (p.derivative.eval r * q.eval r))
  omega


end IsAlternating

end LeanCanny.Algebra.Sturm
