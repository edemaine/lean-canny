/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerResidueMap

/-! # Expanding a specialized residue kernel by its coefficients -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical BigOperators

variable {S A : Type*} [CommRing S] [CommRing A] {n ell : ℕ}

theorem residue_kernel_expansion (φ : S →+* A) (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (K : MvPolynomial (Fin n) A) (q : MvPolynomial (Fin n) S) :
    residue ell (fun i => (r i).map φ) (K * q.map φ) =
      ∑ e ∈ K.support, K.coeff e * φ (residue ell r (monomial e 1 * q)) := by
  have hr' (i : Fin n) : ((r i).map φ).totalDegree < ell :=
    (map_degree_le φ (r i)).trans_lt (hr i)
  conv_lhs => rw [K.as_sum]
  rw [Finset.sum_mul, ← linear_apply hell _ hr', map_sum]
  apply Finset.sum_congr rfl
  intro e _
  have heq : monomial e (K.coeff e) * q.map φ =
      K.coeff e • (monomial e (1 : S) * q).map φ := by
    simp only [map_mul, map_monomial, map_one]
    rw [← smul_mul_assoc]
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [heq, map_smul, linear_apply, ← residue_map φ hell r hr, smul_eq_mul]

end LeanCanny.CountingHierarchy.PurePowerResidue
