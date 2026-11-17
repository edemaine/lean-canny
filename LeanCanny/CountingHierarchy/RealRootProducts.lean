/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ConjugateProducts
public import LeanCanny.CountingHierarchy.ShiftedRootTests
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.RCLike.Lemmas

/-! # Real signs in products over the complex roots of real polynomials -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Complex
open scoped ComplexConjugate BigOperators Classical

@[expose] noncomputable def complexRootSet (p : Polynomial ℝ) : Finset ℂ :=
  (p.map (algebraMap ℝ ℂ)).roots.toFinset

theorem mem_complexRootSet (p : Polynomial ℝ) (hp : p ≠ 0) (z : ℂ) :
    z ∈ complexRootSet p ↔ Polynomial.aeval z p = 0 := by
  rw [complexRootSet, Multiset.mem_toFinset, Polynomial.mem_roots
    ((Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp)]
  simp only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def]

theorem complexRootSet_conj (p : Polynomial ℝ) (hp : p ≠ 0) (z : ℂ)
    (hz : z ∈ complexRootSet p) : conj z ∈ complexRootSet p := by
  rw [mem_complexRootSet p hp] at hz ⊢
  rw [Polynomial.aeval_conj, hz, map_zero]

theorem complexRootSet_card_le (p : Polynomial ℝ) :
    (complexRootSet p).card ≤ p.natDegree := by
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (Polynomial.natDegree_map_le))

theorem real_aeval_at_real_complex_point (p : Polynomial ℝ) (z : ℂ) (hz : z.im = 0) :
    Polynomial.aeval z p = ((p.eval z.re : ℝ) : ℂ) := by
  have he : ((z.re : ℝ) : ℂ) = z := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hz.symm
  calc
    Polynomial.aeval z p = Polynomial.aeval ((z.re : ℝ) : ℂ) p := congrArg (fun w => Polynomial.aeval w p) he.symm
    _ = _ := Polynomial.aeval_ofReal (K := ℂ) p z.re

/-- Evaluation at a complex number cast from a real point. -/
theorem real_polynomial_aeval_ofReal (p : Polynomial ℝ) (x : ℝ) :
    Polynomial.aeval (x : ℂ) p = ((p.eval x : ℝ) : ℂ) :=
  Polynomial.aeval_ofReal (K := ℂ) p x

/-- A negative spectral product for a real polynomial test has a real
 source root where that test is negative. -/
theorem exists_real_root_negative_of_product_neg (p g : Polynomial ℝ) (hp : p ≠ 0)
    (hneg : (∏ z ∈ complexRootSet p, Polynomial.aeval z g).re < 0) :
    ∃ x : ℝ, p.eval x = 0 ∧ g.eval x < 0 := by
  obtain ⟨z, hz, him, hgz⟩ := exists_negative_real_factor_of_product_neg
    (complexRootSet p) (fun z => Polynomial.aeval z g) (Polynomial.aeval_conj g)
    (complexRootSet_conj p hp) hneg
  refine ⟨z.re, ?_, ?_⟩
  · have he := (mem_complexRootSet p hp z).mp hz
    rw [real_aeval_at_real_complex_point p z him] at he
    exact Complex.ofReal_injective he
  · simpa only [real_aeval_at_real_complex_point g z him, Complex.ofReal_re] using hgz

/-- A short integer shift can avoid zeros at every complex root. -/
theorem exists_shift_nonzero_on_complex_roots (p : Polynomial ℝ) (D : ℕ)
    (hD : p.natDegree ≤ D) (g : Polynomial ℝ) :
    ∃ e : ℕ, e ≤ D ∧ ∀ z ∈ complexRootSet p, Polynomial.aeval z g + (e : ℂ) ≠ 0 :=
  exists_bounded_shift_ne_zero (complexRootSet p) D ((complexRootSet_card_le p).trans hD)
    (fun z => Polynomial.aeval z g)

/-- A test negative at exactly one real root has negative spectral product
 whenever it is nonzero at every nonreal root. -/
theorem product_neg_of_unique_negative_real_root (p g : Polynomial ℝ) (hp : p ≠ 0)
    (x : ℝ) (hx : p.eval x = 0) (hg : g.eval x < 0)
    (hpos : ∀ y : ℝ, p.eval y = 0 → y ≠ x → 0 < g.eval y)
    (hnz : ∀ z ∈ complexRootSet p, z.im ≠ 0 → Polynomial.aeval z g ≠ 0) :
    (∏ z ∈ complexRootSet p, Polynomial.aeval z g).re < 0 := by
  have hxS : (x : ℂ) ∈ complexRootSet p := by
    rw [mem_complexRootSet p hp]
    simp only [real_polynomial_aeval_ofReal p x, hx, Complex.ofReal_zero]
  apply conjugate_product_neg_of_unique_negative_real_factor
    (complexRootSet p) (fun z => Polynomial.aeval z g) (Polynomial.aeval_conj g)
    (complexRootSet_conj p hp) (x : ℂ) hxS (by simp)
    (by simpa only [real_polynomial_aeval_ofReal g x, Complex.ofReal_re] using hg) _ hnz
  intro z hz him hne
  have hy : p.eval z.re = 0 := by
    have he := (mem_complexRootSet p hp z).mp hz
    rw [real_aeval_at_real_complex_point p z him] at he
    exact Complex.ofReal_injective he
  have hneq : z.re ≠ x := by
    intro he
    apply hne
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using he
    · simpa only [Complex.ofReal_im] using him
  simpa only [real_aeval_at_real_complex_point g z him, Complex.ofReal_re] using hpos z.re hy hneq

end LeanCanny.CountingHierarchy
