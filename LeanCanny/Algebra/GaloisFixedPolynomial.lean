/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Algebra.Polynomial.Lifts

/-! # Polynomial descent in arbitrary Galois extensions

A polynomial fixed by all base-field automorphisms descends to the base field.
The extension need not be finite, so this also applies in an algebraic closure
of a characteristic-zero field. No coefficient algorithm or size bound is supplied.
-/

@[expose] public section

namespace LeanCanny.Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

theorem exists_polynomial_of_galois_fixed (g : Polynomial L)
    (hg : ∀ σ : L ≃ₐ[K] L, g.map (σ : L →+* L) = g) :
    ∃ q : Polynomial K, q.map (algebraMap K L) = g := by
  apply (Polynomial.mem_lifts g).mp
  apply (Polynomial.lifts_iff_coeff_lifts g).mpr
  intro n
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (g.coeff n)).mpr
  intro σ
  have h := congrArg (fun p : Polynomial L => p.coeff n) (hg σ)
  simpa using h

end LeanCanny.Algebra
