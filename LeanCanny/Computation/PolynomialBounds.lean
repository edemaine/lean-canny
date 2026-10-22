/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTime

/-! # Explicit polynomials at the boundary of native resource bounds

Resource composition uses native `PolyBounded`. Extract a polynomial only when
an interface needs its coefficients rather than a growth certificate.
-/

@[expose] public section
namespace Turing.MultiTapeTM.PolyBounded

/-- An explicit natural polynomial dominating a native bound at every input. -/
theorem exists_polynomial {α : Type*} {size u : α → ℕ} (h : PolyBounded size u) :
    ∃ p : Polynomial ℕ, ∀ a, u a ≤ p.eval (size a) := by
  obtain ⟨c, d, hc⟩ := h.exists_le
  exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun a => by
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using hc a⟩

/-- Supply an explicit polynomial at the native resource-bound interface. -/
theorem of_polynomial {α : Type*} {size u : α → ℕ} (p : Polynomial ℕ)
    (h : ∀ a, u a ≤ p.eval (size a)) : PolyBounded size u :=
  (PolyBounded.of_polynomiallyBounded size (.polynomial_eval p)).mono h

end Turing.MultiTapeTM.PolyBounded
