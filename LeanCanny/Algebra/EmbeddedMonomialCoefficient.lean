/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.EmbeddedCoefficient

/-! # An embedded polynomial multiplied by a disjoint monomial

The source exponent is the restriction of the requested exponent vector.
A single equality checks all remaining coordinates. Failure forces coefficient
zero; success gives exactly one source coefficient.
-/

@[expose] public section

namespace LeanCanny.Algebra.EmbeddedCoefficient
open MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

theorem embedding_pattern_iff (f : σ → τ) (hf : Function.Injective f) (m s : τ →₀ ℕ)
    (hs : ∀ i, s (f i) = 0) :
    (m.comapDomain f hf.injOn).mapDomain f + s = m ↔ ∀ j, j ∉ Set.range f → m j = s j := by
  classical
  constructor
  · intro h j hj
    have he := congrArg (fun u : τ →₀ ℕ => u j) h
    simpa only [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, zero_add] using he.symm
  · intro h
    ext j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      simp only [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective hf, Finsupp.comapDomain_apply, hs, add_zero]
    · rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, zero_add, h j hj]

theorem coeff_rename_mul_monomial [DecidableEq τ] (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R)
    (m s : τ →₀ ℕ) (hs : ∀ i, s (f i) = 0) :
    (rename f p * monomial s 1).coeff m =
      if (m.comapDomain f hf.injOn).mapDomain f + s = m then p.coeff (m.comapDomain f hf.injOn) else 0 := by
  classical
  split_ifs with h
  · calc
      _ = (rename f p * monomial s 1).coeff ((m.comapDomain f hf.injOn).mapDomain f + s) := congrArg _ h.symm
      _ = _ := by rw [MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain f hf, mul_one]
  · by_contra hne
    rw [MvPolynomial.coeff_mul_monomial'] at hne
    by_cases hsm : s ≤ m
    · rw [ite_eq_left hsm, mul_one] at hne
      obtain ⟨u, hu, _⟩ := MvPolynomial.coeff_rename_ne_zero f p (m - s) hne
      have he : u.mapDomain f + s = m := by rw [hu, tsub_add_cancel_of_le hsm]
      have hum : u = m.comapDomain f hf.injOn := by
        ext i
        have hi := congrArg (fun v : τ →₀ ℕ => v (f i)) he
        simpa only [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective hf, hs, add_zero,
          Finsupp.comapDomain_apply] using hi
      exact h (hum ▸ he)
    · exact hne (ite_eq_right hsm)

end LeanCanny.Algebra.EmbeddedCoefficient
