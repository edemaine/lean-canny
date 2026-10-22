/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanCanny.Computation.PolynomialBounds

/-!
# Polynomial bounds on natural-number functions

`PolyBound f` says `f` is dominated pointwise (at every argument, not merely
eventually) by the evaluation of a natural polynomial. Resource bookkeeping
assembles time and space bounds by addition, multiplication, and monotonicity,
so an everywhere-bound closed under those operations is convenient for
compositional machine certificates. The predicate is the native `PolyBounded`
specialization, so closure operations keep native growth certificates throughout.
Explicit polynomials are recovered only by `iff_exists_polynomial`.

## Main results

- `PolyBound` — pointwise domination by a natural polynomial
- `PolyBound.const`, `.id`, `.add`, `.mul`, `.pow`, `.mono`, `.max`, `.eval` —
  the closure API
- `PolyBound.exists_mul_pow_bound` — a polynomial bound is an `A * (n + 1) ^ B` bound
-/


@[expose] public section

namespace LeanCanny

/-- Native polynomial growth on natural inputs. The explicit polynomial
characterization is `PolyBound.iff_exists_polynomial`. -/
abbrev PolyBound (f : ℕ → ℕ) : Prop :=
  Turing.MultiTapeTM.PolyBounded (fun n : ℕ => n) f

namespace PolyBound

theorem polyBounded {α : Type*} (size : α → ℕ) {f : ℕ → ℕ} (hf : PolyBound f) :
    Turing.MultiTapeTM.PolyBounded size (fun a => f (size a)) :=
  Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded size hf.polynomiallyBounded

/-- Compatibility with explicit natural-polynomial bounds, at every input. -/
theorem iff_exists_polynomial {f : ℕ → ℕ} :
    PolyBound f ↔ ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n :=
  ⟨fun hf => hf.exists_polynomial, fun ⟨p, hp⟩ =>
    Turing.MultiTapeTM.PolyBounded.of_polynomial p hp⟩

theorem const (value : ℕ) : PolyBound (fun _ => value) :=
  Turing.MultiTapeTM.PolyBounded.const value

theorem id : PolyBound (fun inputLength => inputLength) :=
  Turing.MultiTapeTM.PolyBounded.self

theorem add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength + g inputLength) :=
  Turing.MultiTapeTM.PolyBounded.add hf hg

theorem mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength * g inputLength) :=
  Turing.MultiTapeTM.PolyBounded.mul hf hg

theorem mono {f g : ℕ → ℕ} (hg : PolyBound g)
    (hle : ∀ inputLength, f inputLength ≤ g inputLength) : PolyBound f :=
  Turing.MultiTapeTM.PolyBounded.mono hg hle

theorem max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => max (f inputLength) (g inputLength)) :=
  (hf.add hg).mono fun _ => Nat.max_le.mpr
    ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem eval (p : Polynomial ℕ) :
    PolyBound (fun inputLength => p.eval inputLength) :=
  Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded _ (.polynomial_eval p)

theorem pow {f : ℕ → ℕ} (hf : PolyBound f) (exponent : ℕ) :
    PolyBound (fun inputLength => f inputLength ^ exponent) :=
  Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded _
    (hf.polynomiallyBounded.pow exponent)

/-- A polynomial bound has the standard native machine-calculus growth form. -/
theorem exists_mul_pow_bound {f : ℕ → ℕ} (hf : PolyBound f) :
    ∃ A B : ℕ, ∀ n, f n ≤ A * (n + 1) ^ B :=
  hf.exists_le

end PolyBound

end LeanCanny
