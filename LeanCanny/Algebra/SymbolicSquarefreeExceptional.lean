/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefreeSmall

/-! # Explicit exceptional parameters for root-preserving squarefree families

The leading coefficient and selected principal subresultant give a nonzero
integer exceptional polynomial with a source degree bound. Outside its finite
real root set, preprocessing retains every original root and makes it simple.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicScaledSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical

noncomputable def exceptional (p : Polynomial Coefficient) : Coefficient :=
  p.leadingCoeff * if p.natDegree = 0 then 1 else
    psc p p.derivative p.natDegree p.derivative.natDegree (degree p)

theorem exceptional_ne_zero (p : Polynomial Coefficient) (hp : p ≠ 0) : exceptional p ≠ 0 := by
  apply mul_ne_zero (leadingCoeff_ne_zero.mpr hp)
  split_ifs with hd
  · exact one_ne_zero
  · exact degree_psc_ne_zero p hd

theorem exceptional_conditions {L : Type*} [Field L] (phi : Coefficient →+* L)
    (p : Polynomial Coefficient) (h : phi (exceptional p) ≠ 0) :
    phi p.leadingCoeff ≠ 0 ∧ (p.natDegree ≠ 0 →
      phi (psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≠ 0) := by
  rw [exceptional, map_mul] at h
  refine ⟨(mul_ne_zero_iff.mp h).1, ?_⟩
  intro hd
  simpa only [ite_eq_right hd] using (mul_ne_zero_iff.mp h).2

theorem exceptional_degree (p : Polynomial Coefficient) (E : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) : (exceptional p).natDegree ≤ (2 * p.natDegree + 1) * E := by
  have hl : p.leadingCoeff.natDegree ≤ E := hE p.natDegree
  have hq : (if p.natDegree = 0 then (1 : Coefficient) else
      psc p p.derivative p.natDegree p.derivative.natDegree (degree p)).natDegree ≤ 2 * p.natDegree * E := by
    split_ifs with hd
    · simp
    · simpa only [subresultantCoeff_self] using subresultant_inner_degree p E hE (degree p) (degree p)
  exact natDegree_mul_le.trans ((Nat.add_le_add hl hq).trans (by nlinarith))

theorem separable_away (p : Polynomial Coefficient) (t : ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) :
    ((polynomial p).map (scalarEvaluation t)).Separable := by
  obtain ⟨hl, hs⟩ := exceptional_conditions (scalarEvaluation t) p ht
  exact specialized_separable _ p hl hs

theorem roots_away (p : Polynomial Coefficient) (t x : ℝ)
    (ht : scalarEvaluation t (exceptional p) ≠ 0) :
    (polynomial p).eval₂ (scalarEvaluation t) x = 0 ↔ p.eval₂ (scalarEvaluation t) x = 0 := by
  obtain ⟨hl, hs⟩ := exceptional_conditions (scalarEvaluation t) p ht
  exact specialized_roots_iff _ p hl hs x

theorem finite_exceptional (p : Polynomial Coefficient) (hp : p ≠ 0) :
    {t : ℝ | scalarEvaluation t (exceptional p) = 0}.Finite := by
  have hmap : (exceptional p).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (exceptional_ne_zero p hp)
  simpa only [scalarEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.IsRoot, Polynomial.eval_map] using
    Polynomial.finite_setOfPred_isRoot hmap
end LeanCanny.Algebra.SymbolicScaledSquarefree
