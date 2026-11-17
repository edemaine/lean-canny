/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Separation
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Integer annihilators of polynomial values at algebraic roots

The outer resultant variable is the source root and the surviving variable
is the test value. The source polynomial need not be monic or squarefree.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

@[expose] noncomputable def polynomialValueResultant (p g : Polynomial ℤ) : Polynomial ℤ :=
  (p.map Polynomial.C).resultant (Polynomial.C Polynomial.X - g.map Polynomial.C)

private theorem eval_parameter_map (p : Polynomial ℤ) (z : ℂ) :
    (p.map Polynomial.C).map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) z) =
      p.map (Int.castRingHom ℂ) := by
  rw [Polynomial.map_map]
  congr 1
  ext a
  simp

/-- Every value of the integer resultant is the product of the shifted
 test values, with the source leading-coefficient factor included. -/
theorem polynomialValueResultant_eval_prod (p g : Polynomial ℤ) (z : ℂ) :
    (polynomialValueResultant p g).eval₂ (Int.castRingHom ℂ) z =
      (p.map (Int.castRingHom ℂ)).leadingCoeff ^
        (Polynomial.C Polynomial.X - g.map Polynomial.C).natDegree *
      ((p.map (Int.castRingHom ℂ)).roots.map
        (fun a => z - (g.map (Int.castRingHom ℂ)).eval a)).prod := by
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℂ) z
  let q := Polynomial.C Polynomial.X - g.map Polynomial.C
  have hm : (p.map Polynomial.C).natDegree = (p.map (Int.castRingHom ℂ)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
  have hq : q.map φ = Polynomial.C z - g.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_sub, Polynomial.map_C, eval_parameter_map]
    simp only [φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hbound : (Polynomial.C z - g.map (Int.castRingHom ℂ)).natDegree ≤ q.natDegree := by
    rw [← hq]
    exact Polynomial.natDegree_map_le
  change φ ((p.map Polynomial.C).resultant q) = _
  rw [← Polynomial.resultant_map_map, eval_parameter_map, hq, hm,
    Polynomial.resultant_eq_prod_eval _ _ _ hbound (IsAlgClosed.splits _)]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, q]

/-- Every test value at a source root is a root of the constructed integer
 annihilator, even if some of the other test values vanish. -/
theorem polynomialValueResultant_root (p g : Polynomial ℤ) (hp : p ≠ 0) (a : ℂ)
    (ha : p.eval₂ (Int.castRingHom ℂ) a = 0) :
    (polynomialValueResultant p g).eval₂ (Int.castRingHom ℂ)
      (g.eval₂ (Int.castRingHom ℂ) a) = 0 := by
  rw [polynomialValueResultant_eval_prod]
  apply mul_eq_zero_of_right
  apply Multiset.prod_eq_zero
  apply Multiset.mem_map.mpr
  refine ⟨a, ?_, ?_⟩
  · exact (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp)).mpr
      (by simpa only [Polynomial.IsRoot, Polynomial.eval_map] using ha)
  · simp only [Polynomial.eval_map, sub_self]

/-- The value resultant is nonzero whenever the source polynomial is
 nonzero. No test-nonvanishing or squarefree hypothesis is required. -/
theorem polynomialValueResultant_ne_zero (p g : Polynomial ℤ) (hp : p ≠ 0) :
    polynomialValueResultant p g ≠ 0 := by
  let q := p.map (Int.castRingHom ℂ)
  let bad := q.roots.toFinset.image (fun a => (g.map (Int.castRingHom ℂ)).eval a)
  obtain ⟨e, _he, hnot⟩ := LeanCanny.Algebra.exists_nat_le_card_notMem bad
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hprod : (q.roots.map (fun a => (e : ℂ) - (g.map (Int.castRingHom ℂ)).eval a)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hv
    obtain ⟨a, ha, hz⟩ := Multiset.mem_map.mp hv
    apply hnot
    have hh : (e : ℂ) = (g.map (Int.castRingHom ℂ)).eval a := sub_eq_zero.mp hz
    rw [hh]
    exact Finset.mem_image.mpr ⟨a, Multiset.mem_toFinset.mpr ha, rfl⟩
  intro hz
  have heval := polynomialValueResultant_eval_prod p g (e : ℂ)
  rw [hz, Polynomial.eval₂_zero] at heval
  exact (mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hq)) hprod) heval.symm

end LeanCanny.CountingHierarchy
