/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DerivativeRootLabels
public import LeanCanny.CountingHierarchy.RootLabelPolynomialBounds

/-! # Integer labels select a qualifying real root with a short list of tests -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped Classical

@[expose] noncomputable def sparseIntegerRootLabel {D : ℕ} (p b₀ : Polynomial ℤ)
    (N b : ℕ) (L : List (Fin D × SignType)) : Polynomial ℤ :=
  rootLabelPolynomial (algebraicTestPrecision D D b (derivativeTestMassExponent D b)) (16 * (N + 1))
    (derivativeLabelTests p b₀ N L) (derivativeLabelTargets N L)

@[expose] def sparseRootLabelDegreeBound (D N b : ℕ) : ℕ :=
  rootLabelDegreeBound (N + 1) (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (N + 1)) D

@[expose] def sparseRootLabelMassExponent (D N b : ℕ) : ℕ :=
  rootLabelMassExponent (N + 1) (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (N + 1)) (derivativeTestMassExponent D b)

/-- Bounds depend on the fixed width, not on the supplied list or signs. -/
theorem sparseIntegerRootLabel_bounds {D : ℕ} (p b₀ : Polynomial ℤ) (N b : ℕ)
    (L : List (Fin D × SignType)) (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b) :
    (sparseIntegerRootLabel p b₀ N b L).natDegree ≤ sparseRootLabelDegreeBound D N b ∧
      coefficientMass (sparseIntegerRootLabel p b₀ N b L) ≤ 2 ^ sparseRootLabelMassExponent D N b := by
  have hg := derivativeLabelTests_bounds p b₀ N b L hD hb₀ hpm hb₀m
  exact ⟨rootLabelPolynomial_degree_le _ _ D (derivativeTestMassExponent D b)
    _ _ (fun i => (hg i).1) (fun i => (hg i).2),
    rootLabelPolynomial_mass_le _ _ D (derivativeTestMassExponent D b)
    _ _ (fun i => (hg i).1) (fun i => (hg i).2)⟩

/-- The margin property is uniform even on malformed overlong lists,
 because the construction uses only its fixed-width prefix. -/
theorem sparseIntegerRootLabel_margin {D : ℕ} (p b₀ : Polynomial ℤ) (hp : p ≠ 0) (N b : ℕ)
    (L : List (Fin D × SignType)) (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b)
    (x : ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) :
    ((1 : ℝ) / 2 ≤ (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) x ∨
      (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) x ≤ -(1 : ℝ) / 2) ∧
    (0 < (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) x ↔
      ∀ i, SignType.sign ((derivativeLabelTests p b₀ N L i).eval₂ (Int.castRingHom ℝ) x) =
        derivativeLabelTargets N L i) := by
  apply rootLabelPolynomial_margin (by omega : 1 ≤ N + 1)
  intro i
  have hi := derivativeLabelTests_bounds p b₀ N b L hD hb₀ hpm hb₀m i
  exact algebraic_test_value_range p _ hp D D b (derivativeTestMassExponent D b)
    hD hi.1 hpm hi.2 x hx

/-- On an allowed short list the positivity condition is exactly the
 requested derivative signs and the distinguished positive test. -/
theorem sparseIntegerRootLabel_pos_iff {D : ℕ} (p b₀ : Polynomial ℤ) (hp : p ≠ 0) (N b : ℕ)
    (L : List (Fin D × SignType)) (hL : L.length ≤ N)
    (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b)
    (x : ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) :
    (0 < (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) x) ↔
      0 < b₀.eval₂ (Int.castRingHom ℝ) x ∧
        matchesTests (fun i : Fin D => fun y =>
          LeanCanny.Algebra.ThomEncoding.sign (p.map (Int.castRingHom ℝ)) y (i.val + 1)) L x :=
  (sparseIntegerRootLabel_margin p b₀ hp N b L hD hb₀ hpm hb₀m x hx).2.trans
    (derivativeLabelTests_match_iff p b₀ N L hL x)

/-- If any qualifying root exists, a list of at most `N` derivative tests
 gives an integer label positive at one such root and negative at all other
 real roots. The bound is `D <= 2^N`, not an expanded sign string. -/
theorem exists_sparseIntegerRootLabel {D : ℕ} (p b₀ : Polynomial ℤ) (hp : p ≠ 0) (N b : ℕ)
    (hD : p.natDegree ≤ D) (hDN : D ≤ 2 ^ N) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b)
    (hex : ∃ x : ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 ∧ 0 < b₀.eval₂ (Int.castRingHom ℝ) x) :
    ∃ L : List (Fin D × SignType), L.length ≤ N ∧ ∃ x : ℝ,
      p.eval₂ (Int.castRingHom ℝ) x = 0 ∧
      0 < (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) x ∧
      ∀ y : ℝ, p.eval₂ (Int.castRingHom ℝ) y = 0 → y ≠ x →
        (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) y < 0 := by
  let q := p.map (Int.castRingHom ℝ)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  let S := q.roots.toFinset.filter (fun x => 0 < b₀.eval₂ (Int.castRingHom ℝ) x)
  have hmem (x : ℝ) : x ∈ S ↔ p.eval₂ (Int.castRingHom ℝ) x = 0 ∧
      0 < b₀.eval₂ (Int.castRingHom ℝ) x := by
    simp only [S, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hq,
      Polynomial.IsRoot, q, Polynomial.eval_map]
  have hS : S.Nonempty := by obtain ⟨x, hx⟩ := hex; exact ⟨x, (hmem x).mpr hx⟩
  have hroot (x : ℝ) (hx : x ∈ S) : q.eval x = 0 := by
    simpa only [q, Polynomial.eval_map] using ((hmem x).mp hx).1
  obtain ⟨L, hL, x, hxS, hselect⟩ := exists_sparse_root_selector_of_degree q hq D N
    (Polynomial.natDegree_map_le.trans hD) hDN S hS hroot
  have hx := (hmem x).mp hxS
  refine ⟨L, hL, x, hx.1, ?_, ?_⟩
  · exact (sparseIntegerRootLabel_pos_iff p b₀ hp N b L hL hD hb₀ hpm hb₀m x hx.1).mpr
      ⟨hx.2, (hselect x hxS).mpr rfl⟩
  · intro y hy hne
    have hnot : ¬0 < (sparseIntegerRootLabel p b₀ N b L).eval₂ (Int.castRingHom ℝ) y := by
      intro hpos
      obtain ⟨hy₀, hmatch⟩ :=
        (sparseIntegerRootLabel_pos_iff p b₀ hp N b L hL hD hb₀ hpm hb₀m y hy).mp hpos
      exact hne ((hselect y ((hmem y).mpr ⟨hy, hy₀⟩)).mp hmatch)
    rcases (sparseIntegerRootLabel_margin p b₀ hp N b L hD hb₀ hpm hb₀m y hy).1 with hm | hm
    · linarith
    · linarith

end LeanCanny.CountingHierarchy
