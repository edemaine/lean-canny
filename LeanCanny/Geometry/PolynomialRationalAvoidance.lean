/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialGridAvoidance
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Order.Interval.Set.Infinite

/-! # Rational points avoiding exceptional polynomials in open boxes

Every nonempty real interval contains arbitrarily large finite sets of
rational points. Applying polynomial grid avoidance to their real images
avoids a nonzero real polynomial inside any prescribed open coordinate box.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialRationalAvoidance
open Set
open scoped BigOperators

theorem rational_finset_in_interval (a b : ℝ) (hab : a < b) (n : ℕ) :
    ∃ S : Finset ℚ, S.card = n ∧ ∀ q ∈ S, a < (q : ℝ) ∧ (q : ℝ) < b := by
  classical
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  obtain ⟨r, hqr, hrb⟩ := exists_rat_btwn hqb
  have hqr' : q < r := by exact_mod_cast hqr
  let : Infinite (Ioo q r) := Set.Ioo.infinite hqr'
  obtain ⟨T, hT⟩ := Finset.exists_card_eq (α := Ioo q r) n
  refine ⟨T.image Subtype.val, ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ Subtype.val_injective]
  · intro s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    have hqt : (q : ℝ) < (t.val : ℝ) := by exact_mod_cast t.property.1
    have htr : (t.val : ℝ) < (r : ℝ) := by exact_mod_cast t.property.2
    exact ⟨haq.trans hqt, htr.trans hrb⟩

theorem exists_in_intervals {ι : Type*} [Finite ι] (p : MvPolynomial ι ℝ) (hp : p ≠ 0)
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∃ u : ι → ℚ, (∀ i, a i < (u i : ℝ) ∧ (u i : ℝ) < b i) ∧
      MvPolynomial.eval (fun i => (u i : ℝ)) p ≠ 0 := by
  classical
  choose S hcard hinterval using fun i => rational_finset_in_interval (a i) (b i) (hab i) (p.totalDegree + 1)
  let T : ι → Finset ℝ := fun i => (S i).image (fun q : ℚ => (q : ℝ))
  have hTcard (i : ι) : (T i).card = p.totalDegree + 1 := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ Rat.cast_injective, hcard]
  obtain ⟨x, hx, he⟩ := Algebra.PolynomialGridAvoidance.exists_on_grid p hp T (fun i => by
    rw [hTcard i]
    exact Nat.lt_succ_of_le (MvPolynomial.degreeOf_le_totalDegree p i))
  choose u hu hcast using fun i => Finset.mem_image.mp (hx i)
  refine ⟨u, fun i => hinterval i (u i) (hu i), ?_⟩
  have hfun : (fun i => (u i : ℝ)) = x := funext hcast
  rwa [hfun]

theorem exists_common_in_intervals {ι σ : Type*} [Finite ι] [Fintype σ]
    (p : σ → MvPolynomial ι ℝ) (hp : ∀ j, p j ≠ 0)
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∃ u : ι → ℚ, (∀ i, a i < (u i : ℝ) ∧ (u i : ℝ) < b i) ∧
      ∀ j, MvPolynomial.eval (fun i => (u i : ℝ)) (p j) ≠ 0 := by
  classical
  have hprod : (∏ j, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  obtain ⟨u, hu, he⟩ := exists_in_intervals (∏ j, p j) hprod a b hab
  rw [map_prod] at he
  exact ⟨u, hu, fun j => Finset.prod_ne_zero_iff.mp he j (Finset.mem_univ j)⟩

end LeanCanny.Geometry.PolynomialRationalAvoidance
