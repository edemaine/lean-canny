/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DerivativeTestBounds
public import LeanCanny.CountingHierarchy.RootLabelPolynomial
public import LeanCanny.CountingHierarchy.SparseRootSelection

/-! # Fixed-width integer labels for derivative-sign tests

Only the first `N` tests are used. Missing entries impose the identically zero
condition, so all degree and mass bounds are independent of the supplied list.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped Classical

@[expose] noncomputable def derivativeListTest {D : ℕ} (p : Polynomial ℤ)
    (c : Option (Fin D × SignType)) : Polynomial ℤ :=
  c.elim 0 (fun t => Polynomial.derivative^[t.1.val + 1] p)

@[expose] def derivativeListTarget {D : ℕ} (c : Option (Fin D × SignType)) : SignType :=
  c.elim 0 Prod.snd

@[expose] noncomputable def derivativeLabelTests {D : ℕ} (p b₀ : Polynomial ℤ)
    (N : ℕ) (L : List (Fin D × SignType)) : Fin (N + 1) → Polynomial ℤ :=
  Fin.cases b₀ (fun j => derivativeListTest p L[j.val]?)

@[expose] def derivativeLabelTargets {D : ℕ} (N : ℕ)
    (L : List (Fin D × SignType)) : Fin (N + 1) → SignType :=
  Fin.cases 1 (fun j => derivativeListTarget L[j.val]?)

theorem derivativeListTest_sign {D : ℕ} (p : Polynomial ℤ) (x : ℝ) (c : Option (Fin D × SignType)) :
    (SignType.sign ((derivativeListTest p c).eval₂ (Int.castRingHom ℝ) x) = derivativeListTarget c) ↔
      c.elim True (fun t => LeanCanny.Algebra.ThomEncoding.sign (p.map (Int.castRingHom ℝ)) x (t.1.val + 1) = t.2) := by
  cases c with
  | none => simp only [derivativeListTest, derivativeListTarget, Option.elim_none,
      Polynomial.eval₂_zero, sign_zero]
  | some c => simp only [derivativeListTest, derivativeListTarget, Option.elim_some,
      LeanCanny.Algebra.ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map]

theorem derivativeLabelTests_match_iff {D : ℕ} (p b₀ : Polynomial ℤ) (N : ℕ)
    (L : List (Fin D × SignType)) (hL : L.length ≤ N) (x : ℝ) :
    (∀ i, SignType.sign ((derivativeLabelTests p b₀ N L i).eval₂ (Int.castRingHom ℝ) x) =
      derivativeLabelTargets N L i) ↔
      0 < b₀.eval₂ (Int.castRingHom ℝ) x ∧
        matchesTests (fun i : Fin D => fun y =>
          LeanCanny.Algebra.ThomEncoding.sign (p.map (Int.castRingHom ℝ)) y (i.val + 1)) L x := by
  rw [Fin.forall_fin_succ]
  simp only [derivativeLabelTests, derivativeLabelTargets, Fin.cases_zero, Fin.cases_succ,
    sign_eq_one_iff, derivativeListTest_sign]
  apply and_congr_right
  intro _
  constructor
  · intro h c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    have hi := h ⟨j, hj.trans_le hL⟩
    simpa only [List.getElem?_eq_getElem hj, Option.elim_some] using hi
  · intro h j
    cases he : L[j.val]? with
    | none => simp only [Option.elim_none]
    | some c =>
      simpa only [Option.elim_some] using h c (List.mem_of_getElem? he)

theorem derivativeLabelTests_bounds {D : ℕ} (p b₀ : Polynomial ℤ) (N b : ℕ)
    (L : List (Fin D × SignType)) (hp : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b) (i : Fin (N + 1)) :
    (derivativeLabelTests p b₀ N L i).natDegree ≤ D ∧
      coefficientMass (derivativeLabelTests p b₀ N L i) ≤ 2 ^ derivativeTestMassExponent D b := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨hb₀, hb₀m.trans (Nat.pow_le_pow_right (by decide) (by unfold derivativeTestMassExponent; omega))⟩
  · cases he : L[j.val]? with
    | none => simp only [derivativeLabelTests, Fin.cases_succ, he, derivativeListTest,
        Option.elim_none, Polynomial.natDegree_zero, coefficientMass_zero, Nat.zero_le, and_self]
    | some c =>
      simp only [derivativeLabelTests, Fin.cases_succ, he, derivativeListTest, Option.elim_some]
      exact ⟨(Polynomial.natDegree_iterate_derivative p _).trans ((Nat.sub_le _ _).trans hp),
        iterated_derivative_mass_le p D b hp hpm _⟩

end LeanCanny.CountingHierarchy
