/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.LinearCombination

/-!
# Bounded separating linear forms

The finite-set separation step in Canny's Lemma 2.1: for `m` points `(a,b)` in a
characteristic-zero field, some integer `0 ≤ c ≤ m²` makes `a+c*b` injective on the points.
The proof bounds the exceptional slopes and avoids them by the pigeonhole principle.

Lagrange interpolation then recovers both coordinates from the separating values. These
interpolants have coefficients in the ambient field. Descent to the input coefficient field
and the space complexity of computing them are not asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra

variable {K : Type*} [Field K] [CharZero K]

/-- Project a point along the integer direction `(1,c)`. -/
def shear (c : ℕ) (p : K × K) : K := p.1 + (c : K) * p.2

/-- Any `m` field elements omit one of the integers `0,...,m`. -/
theorem exists_nat_le_card_notMem (s : Finset K) :
    ∃ c : ℕ, c ≤ s.card ∧ (c : K) ∉ s := by
  classical
  let candidates := (Finset.range (s.card + 1)).image (Nat.cast : ℕ → K)
  have hcard : candidates.card = s.card + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨x, hx, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card < candidates.card by omega)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨c, Nat.le_of_lt_succ (Finset.mem_range.mp hc), hnot⟩

/-- A separating direction can be chosen among quadratically many nonnegative integers. -/
theorem exists_bounded_separating_shear (s : Finset (K × K)) :
    ∃ c : ℕ, c ≤ s.card ^ 2 ∧ Set.InjOn (shear (K := K) c) (s : Set (K × K)) := by
  classical
  let bad := (s ×ˢ s).image (fun pq => (pq.1.1 - pq.2.1) / (pq.2.2 - pq.1.2))
  obtain ⟨c, hc, hnot⟩ := exists_nat_le_card_notMem bad
  have hbad : bad.card ≤ s.card ^ 2 := by
    exact (Finset.card_image_le).trans (by simp [Finset.card_product, pow_two])
  refine ⟨c, hc.trans hbad, ?_⟩
  intro p hp q hq heq
  by_cases hsecond : p.2 = q.2
  · apply Prod.ext _ hsecond
    simpa only [shear, hsecond, add_left_inj] using heq
  · exfalso
    apply hnot
    have hden : q.2 - p.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hsecond)
    have hslope : (c : K) = (p.1 - q.1) / (q.2 - p.2) := by
      apply (eq_div_iff hden).mpr
      unfold shear at heq
      linear_combination -heq
    rw [hslope]
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩

/-- A separating value is a root of a monic polynomial of degree exactly the number of points,
and two degree-bounded univariate polynomials recover the original coordinates at those roots. -/
theorem exists_univariate_coordinates (s : Finset (K × K)) :
    ∃ (c : ℕ) (q r₁ r₂ : Polynomial K),
      c ≤ s.card ^ 2 ∧ q.Monic ∧ q.natDegree = s.card ∧
      r₁.degree < (s.card : WithBot ℕ) ∧ r₂.degree < (s.card : WithBot ℕ) ∧
      ∀ p ∈ s, q.eval (shear c p) = 0 ∧
        r₁.eval (shear c p) = p.1 ∧ r₂.eval (shear c p) = p.2 := by
  classical
  obtain ⟨c, hc, hinj⟩ := exists_bounded_separating_shear s
  refine ⟨c, Lagrange.nodal s (shear c),
    Lagrange.interpolate s (shear c) Prod.fst,
    Lagrange.interpolate s (shear c) Prod.snd,
    hc, Lagrange.nodal_monic, Lagrange.natDegree_nodal,
    Lagrange.degree_interpolate_lt _ hinj, Lagrange.degree_interpolate_lt _ hinj, ?_⟩
  intro p hp
  exact ⟨Lagrange.eval_nodal_at_node hp,
    Lagrange.eval_interpolate_at_node _ hinj hp,
    Lagrange.eval_interpolate_at_node _ hinj hp⟩

end LeanCanny.Algebra
