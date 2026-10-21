/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalOrdering

/-! # Polynomial cancellation of all universal extraneous determinants

The proved ordering comparisons and coefficient-group denominator argument
give a unique common polynomial quotient, normalized to one at coordinate
powers. Its factorization holds for every input/spatial ordering.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

theorem exists_unique_ordering_quotient (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) :
    ∃! q : CoefficientRing (n + 1) R,
      (∀ π : Equiv.Perm (Fin (n + 1)), numerator d W π = denominator d W π * q) ∧
        MvPolynomial.eval (powerPoint (R := R) d) q = 1 := by
  have hcross : ∀ i j, numeratorFamily (R := R) d W i * denominatorFamily d W j =
      numeratorFamily d W j * denominatorFamily d W i :=
    fun i j => ordering_cross d W hdegree hW (orderingFor i) (orderingFor j)
  obtain ⟨q, hq, hunique⟩ := (comparison_iff_unique_normalized_quotient (R := R) d W hdegree).mp hcross
  have href : numerator (R := R) d W (Equiv.refl _) = denominator d W (Equiv.refl _) * q := by
    simpa only [numeratorFamily, denominatorFamily, orderingFor, Equiv.swap_self] using hq.1 (Fin.last n)
  have hall (π : Equiv.Perm (Fin (n + 1))) : numerator (R := R) d W π = denominator d W π * q := by
    apply mul_right_cancel₀ (denominator_ne_zero (R := R) d W hdegree (Equiv.refl _))
    calc
      _ = numerator d W (Equiv.refl _) * denominator d W π := ordering_cross d W hdegree hW π (Equiv.refl _)
      _ = _ := by rw [href]; ring
  refine ⟨q, ⟨hall, hq.2⟩, ?_⟩
  intro q' hq'
  exact hunique q' ⟨fun i => hq'.1 (orderingFor i), hq'.2⟩

theorem denominator_dvd_numerator (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (π : Equiv.Perm (Fin (n + 1))) :
    denominator (R := R) d W π ∣ numerator (R := R) d W π := by
  obtain ⟨q, hq, _⟩ := exists_unique_ordering_quotient (R := R) d W hdegree hW
  exact ⟨q, hq.1 π⟩

end LeanCanny.Algebra.MacaulayUniversal
