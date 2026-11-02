/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedLeadingTiltedGradient
/-! # Exact source correction when one more original coordinate is frozen

The old physical value is Y_k=s*x_k; the new parameter is x_k itself.
Partial homogenization and the tilt agree after this change. The Fermat
term changes by (1-s^M)*x_k^M, so the old level equation is not silently reused.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedLeadingDilationStep
open LeanCanny.ETR PartialHomogenization FixedLeadingTiltedSource
open MvPolynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] {n k D : ℕ}

theorem lifted_step (s : R) (x : ℕ → R) (i : ℕ) :
    lifted (k+1) s x i = if i=k+1 then x k else lifted k s x i := by
  cases i with
  | zero => simp [lifted]
  | succ i =>
    by_cases hi : i=k
    · subst i
      simp [lifted]
    · have H : (i<k+1) ↔ i<k := by omega
      simp [lifted,H,hi]

theorem low_value_step (u : ℕ) (t : Term) (ht : t.degreeBound ≤ D)
    (hu : k+1 ≤ u) (s : R) (x : ℕ → R) :
    (lowTerm (k+1) D u t).eval (lifted (k+1) s x)=
      (lowTerm k D u t).eval (lifted k s x) := by
  rw [eval_lowTerm (k+1) D u t ht hu,eval_lowTerm k D u t ht (by omega)]

theorem fermat_value_step (hkn : k<n) (s : R) (x : ℕ → R) :
    (∑ i : Fin (n+1), lifted (k+1) s x i.val ^ degree D)=
      (∑ i : Fin (n+1), lifted k s x i.val ^ degree D)+(1-s^degree D)*x k^degree D := by
  let j : Fin (n+1) := ⟨k+1,by omega⟩
  have HE : ∀ i : Fin (n+1), lifted (k+1) s x i.val ^ degree D =
      lifted k s x i.val ^ degree D + if i=j then (1-s^degree D)*x k^degree D else 0 := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [j,lifted,Nat.lt_succ_self,ite_true,lt_self_iff_false,ite_false,mul_pow]
      ring
    · have HN : i.val≠k+1 := fun h => hi (Fin.ext h)
      rw [lifted_step,ite_eq_right HN,ite_eq_right hi,add_zero]
  calc
    _ = ∑ i : Fin (n+1), (lifted k s x i.val ^ degree D +
      if i=j then (1-s^degree D)*x k^degree D else 0) := Finset.sum_congr rfl (fun i _ => HE i)
    _ = _ := by simp [Finset.sum_add_distrib]

theorem source_value_step (hkn : k<n) (u : Fin n) (t : Term) (ht : t.degreeBound ≤ D)
    (ha : t.arity ≤ n) (hu : k+1 ≤ u.val) (s : R) (x : ℕ → R) :
    (FixedLeadingTiltedSource.polynomial (k+1) D u t ht).eval₂ (Int.castRingHom R)
        (fun i => lifted (k+1) s x i.val)=
      (FixedLeadingTiltedSource.polynomial k D u t ht).eval₂ (Int.castRingHom R)
        (fun i => lifted k s x i.val)+(1-s^degree D)*x k^degree D := by
  have HK : (lowTerm k D u.val t).arity ≤ n+1 := (lowTerm_arity k D u.val t).trans (by omega)
  have HN : (lowTerm (k+1) D u.val t).arity ≤ n+1 := (lowTerm_arity (k+1) D u.val t).trans (by omega)
  simp only [FixedLeadingTiltedSource.polynomial,source,eval₂_add,eval₂_sum,eval₂_pow,eval₂_X]
  rw [finite_eval _ _ _ HN,finite_eval _ _ _ HK,low_value_step u.val t ht hu,
    fermat_value_step hkn s x]
  ring

end LeanCanny.Algebra.FixedLeadingDilationStep
