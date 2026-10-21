/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayIdealImage
public import LeanCanny.Algebra.MacaulayProjectiveRoots

/-! # Ideal certificates supplied by a nonzero polynomial quotient

The proved common-root implication excludes nonzero common roots when
the quotient is nonzero. Over an algebraically closed field the projective
Nullstellensatz then supplies a power of the variable ideal in the input
ideal, and homogeneous Bezout expressions at every sufficiently large
degree. No explicit degree bound or converse quotient implication is
asserted.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical BigOperators
variable {n : ℕ} {K : Type*} [Field K]

theorem no_nonzero_root_of_polynomialValue_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hq : polynomialValue d W hdegree hW p ≠ 0)
    (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) : x = 0 := by
  by_contra hn
  have hnz : ∃ j, x j ≠ 0 := by simpa only [Pi.zero_apply] using Function.ne_iff.mp hn
  exact hq (polynomialValue_eq_zero_of_common_root d W hdegree hW p hp hd x hx hnz)

variable [IsAlgClosed K]

theorem variable_ideal_pow_le_of_polynomialValue_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hq : polynomialValue d W hdegree hW p ≠ 0) :
    ∃ N : ℕ, MvPolynomial.idealOfVars (Fin (n + 1)) K ^ N ≤ ProjectiveNullstellensatz.generated p :=
  (ProjectiveNullstellensatz.no_nonzero_root_iff_variable_ideal_pow p).mp
    (no_nonzero_root_of_polynomialValue_ne_zero d W hdegree hW p hp hd hq)

theorem eventual_homogeneous_multipliers_of_polynomialValue_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hq : polynomialValue d W hdegree hW p ≠ 0) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous t →
      ∃ q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K,
        (∀ i m, m ∈ (q i).support → m.degree + d i = t) ∧ (∑ i, q i * p i) = f := by
  obtain ⟨N, hN⟩ := variable_ideal_pow_le_of_polynomialValue_ne_zero d W hdegree hW p hp hd hq
  refine ⟨N, ?_⟩
  intro t ht f hf
  exact HomogeneousIdealMembership.multiplier_support_grade p d hp t f hf
    (ProjectiveNullstellensatz.homogeneous_mem_of_variable_ideal_pow_le p N t hN ht f hf)

end LeanCanny.Algebra.MacaulayUniversal
