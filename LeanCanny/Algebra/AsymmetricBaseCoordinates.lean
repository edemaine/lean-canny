/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.VectorGaloisDescent

/-! # Bounded asymmetric rational coordinates over the input field

For a finite Galois-stable vector set, shifted nodal polynomials descend to the
base field. Univariate recovery can be performed over that base field while
retaining correctness at every point of the extension field. The construction
is algebraic existence, with no encoded multivariate eliminant algorithm.
-/

@[expose] public section

namespace LeanCanny.Algebra.AsymmetricBaseCoordinates
open Polynomial AsymmetricProjection

variable {ι K L : Type*} [Fintype ι] [Field K] [Field L] [Algebra K L]

omit [Fintype ι] in
private theorem rootPairs_eq_of_nodal_maps (s : Finset (ι → L)) (f g : (ι → L) → L)
    (p q : K[X]) (hp : p.map (algebraMap K L) = Lagrange.nodal s f)
    (hq : q.map (algebraMap K L) = Lagrange.nodal s g) :
    rootPairs (L := L) p q =
      rootPairs (K := L) (L := L) (Lagrange.nodal s f) (Lagrange.nodal s g) := by
  classical
  simp only [rootPairs, rootsFinset, hp, hq, Algebra.algebraMap_self, Polynomial.map_id]

/-- Base-field shifted polynomials suffice to recover extension-field coordinates. -/
theorem exists_rational_coordinates (s : Finset (ι → L)) (c : ι → ℕ) (k : ℕ) (j : ι)
    (hinj : Set.InjOn (pairValue (K := L) c k j)
      ((s ×ˢ s : Finset ((ι → L) × (ι → L))) : Set ((ι → L) × (ι → L))))
    (pPlus pMinus : K[X])
    (hp : pPlus.map (algebraMap K L) = Lagrange.nodal s (plus c k j))
    (hm : pMinus.map (algebraMap K L) = Lagrange.nodal s (minus c j)) :
    ∃ n d : K[X], n.natDegree ≤ 1 + max 1 ((s.card - 1) * s.card) ∧
      d.natDegree ≤ max 1 ((s.card - 1) * s.card) ∧
      ∀ x ∈ s, Polynomial.aeval (projection c x) d ≠ 0 ∧
        Polynomial.aeval (projection c x) n / Polynomial.aeval (projection c x) d = x j := by
  let N := coordinateNumerator pPlus pMinus k
  let D := coordinateDenominator pPlus pMinus k
  let scale : K[X] := C ((k : K) + 1) * X
  let d := D.comp scale
  let n := X * d + N.comp scale
  have hpdeg : pPlus.natDegree = s.card := by
    rw [← Polynomial.natDegree_map (algebraMap K L), hp, Lagrange.natDegree_nodal]
  have hmdeg : pMinus.natDegree = s.card := by
    rw [← Polynomial.natDegree_map (algebraMap K L), hm, Lagrange.natDegree_nodal]
  have hlinear : scale.natDegree ≤ 1 := natDegree_mul_le.trans (by simp)
  have hcomp (p : K[X]) : (p.comp scale).natDegree ≤ p.natDegree :=
    natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left p.natDegree hlinear)
  have hD : d.natDegree ≤ max 1 ((s.card - 1) * s.card) := (hcomp D).trans (by
    simpa only [hpdeg, hmdeg] using coordinateDenominator_natDegree_le pPlus pMinus k)
  have hN : (N.comp scale).natDegree ≤ max 1 ((s.card - 1) * s.card) := (hcomp N).trans (by
    simpa only [hpdeg, hmdeg] using coordinateNumerator_natDegree_le pPlus pMinus k)
  refine ⟨n, d, ?_, hD, ?_⟩
  · exact (natDegree_add_le _ _).trans (max_le
      (natDegree_mul_le.trans (by simpa only [natDegree_X] using Nat.add_le_add_left hD 1))
      (by omega))
  · intro x hx
    have hpne : pPlus ≠ 0 := by
      intro hz
      have he : (0 : L[X]) = Lagrange.nodal s (plus c k j) := by simpa [hz] using hp
      exact Lagrange.nodal_ne_zero he.symm
    have hsep : pMinus.Separable := by
      apply (Polynomial.separable_map (algebraMap K L)).mp
      rw [hm]
      exact separable_prod_X_sub_C_iff'.mpr (minus_injective s c k j hinj)
    have hsplit : (pMinus.map (algebraMap K L)).Splits := by rw [hm]; exact nodal_splits s _
    have hpair : Set.InjOn (LeanCanny.Algebra.shear k) (rootPairs (L := L) pPlus pMinus : Set (L × L)) := by
      rw [rootPairs_eq_of_nodal_maps s _ _ _ _ hp hm]
      exact nodal_rootPairs_injective s _ _ k hinj
    have hr := coordinate_recovery_spec pPlus pMinus k (plus c k j x) (minus c j x)
      hpne hsep hsplit hpair
      (by rw [← Polynomial.eval_map_algebraMap, hp]; exact Lagrange.eval_nodal_at_node hx)
      (by rw [← Polynomial.eval_map_algebraMap, hm]; exact Lagrange.eval_nodal_at_node hx)
    dsimp only at hr
    rw [show LeanCanny.Algebra.shear k (plus c k j x, minus c j x) =
      ((k : L) + 1) * projection c x from diagonal_pairValue c k j x] at hr
    have hdval (t : L) : Polynomial.aeval t d = Polynomial.aeval (((k : L) + 1) * t) D := by
      simp [d, scale, Polynomial.aeval_comp]
    have hnval (t : L) : Polynomial.aeval t n = t * Polynomial.aeval t d +
        Polynomial.aeval (((k : L) + 1) * t) N := by
      simp [n, scale, Polynomial.aeval_comp]
    have hd : Polynomial.aeval (projection c x) d ≠ 0 := by rw [hdval]; exact hr.1
    refine ⟨hd, ?_⟩
    rw [hnval, add_div, mul_div_cancel_right₀ _ hd, hdval]
    have he := hr.2.1
    change projection c x - x j = _ at he
    rw [neg_div] at he
    symm
    linear_combination -he

/-- All finite-set coordinate formulas can be chosen over the input field,
with bounded integer projection data and explicit polynomial degree bounds. -/
theorem exists_bounded_coordinates [IsGalois K L] [CharZero L]
    (s : Finset (ι → L)) (hs : VectorGaloisDescent.Stable (K := K) s) :
    ∃ (k : ℕ) (c : ι → ℕ) (q : K[X]) (num den : ι → K[X]),
      0 < k ∧ k ≤ s.card ^ 4 + 1 ∧
      (∀ i, c i ≤ (Fintype.card ι + 1) * s.card ^ 4) ∧
      Set.InjOn (projection (K := L) c) (s : Set (ι → L)) ∧
      q.Monic ∧ q.Separable ∧ q.natDegree = s.card ∧
      (∀ θ : L, Polynomial.aeval θ q = 0 ↔ ∃ x ∈ s, projection c x = θ) ∧
      ∀ j, (num j).natDegree ≤ 1 + max 1 ((s.card - 1) * s.card) ∧
        (den j).natDegree ≤ max 1 ((s.card - 1) * s.card) ∧
        ∀ x ∈ s, Polynomial.aeval (projection c x) (den j) ≠ 0 ∧
          Polynomial.aeval (projection c x) (num j) /
            Polynomial.aeval (projection c x) (den j) = x j := by
  classical
  obtain ⟨k, c, hk, hkb, hc, hproj, hpair⟩ := exists_bounded_direction s
  obtain ⟨q, hq⟩ := VectorGaloisDescent.exists_projection_polynomial s hs c
  choose pPlus hp using fun j => VectorGaloisDescent.exists_plus_polynomial s hs c k j
  choose pMinus hm using fun j => VectorGaloisDescent.exists_minus_polynomial s hs c j
  choose num den hn hd hr using fun j =>
    exists_rational_coordinates s c k j (hpair j) (pPlus j) (pMinus j) (hp j) (hm j)
  refine ⟨k, c, q, num, den, hk, hkb, hc, hproj, ?_, ?_, ?_, ?_, fun j => ⟨hn j, hd j, hr j⟩⟩
  · apply Polynomial.monic_of_injective (algebraMap K L).injective
    rw [hq]
    exact Lagrange.nodal_monic
  · apply (Polynomial.separable_map (algebraMap K L)).mp
    rw [hq]
    exact separable_prod_X_sub_C_iff'.mpr hproj
  · rw [← Polynomial.natDegree_map (algebraMap K L), hq, Lagrange.natDegree_nodal]
  · intro θ
    rw [← Polynomial.eval_map_algebraMap, hq]
    exact nodal_zero_iff s (projection c) θ

end LeanCanny.Algebra.AsymmetricBaseCoordinates
