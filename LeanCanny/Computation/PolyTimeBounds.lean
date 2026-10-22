/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanCanny.Computation.PolyTime

/-!
# Polynomial bounds on natural-number functions

`PolyBound f` says `f` is dominated pointwise (at every argument, not merely
eventually) by the evaluation of a natural polynomial. Resource bookkeeping
assembles time and space bounds by addition, multiplication, and monotonicity,
so an everywhere-bound closed under those operations is convenient for
compositional machine certificates.

## Main results

- `PolyBound` — pointwise domination by a natural polynomial
- `PolyBound.const`, `.id`, `.add`, `.mul`, `.pow`, `.mono`, `.max`, `.eval` —
  the closure API
- `PolyBound.exists_mul_pow_bound` — a polynomial bound is an `A * (n + 1) ^ B` bound
-/


@[expose] public section

namespace LeanCanny

/-- Pointwise domination by the evaluation of a natural polynomial. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ inputLength, f inputLength ≤ p.eval inputLength

namespace PolyBound

theorem polyBounded {α : Type*} (size : α → ℕ) {f : ℕ → ℕ} (hf : PolyBound f) :
    Turing.MultiTapeTM.PolyBounded size (fun a => f (size a)) := by
  obtain ⟨p, hp⟩ := hf
  exact (Turing.MultiTapeTM.PolyBounded.of_polynomiallyBounded size
    (.polynomial_eval p)).mono fun a => hp (size a)

theorem const (value : ℕ) : PolyBound (fun _ => value) :=
  ⟨Polynomial.C value, fun _ => by simp⟩

theorem id : PolyBound (fun inputLength => inputLength) :=
  ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength + g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun inputLength => by
    rw [Polynomial.eval_add]
    exact Nat.add_le_add (hp inputLength) (hq inputLength)⟩

theorem mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength * g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun inputLength => by
    rw [Polynomial.eval_mul]
    exact Nat.mul_le_mul (hp inputLength) (hq inputLength)⟩

theorem mono {f g : ℕ → ℕ} (hg : PolyBound g)
    (hle : ∀ inputLength, f inputLength ≤ g inputLength) : PolyBound f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun inputLength => le_trans (hle inputLength) (hp inputLength)⟩

theorem max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => max (f inputLength) (g inputLength)) :=
  (hf.add hg).mono fun _ => Nat.max_le.mpr
    ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem eval (p : Polynomial ℕ) :
    PolyBound (fun inputLength => p.eval inputLength) :=
  ⟨p, fun _ => le_rfl⟩

theorem pow {f : ℕ → ℕ} (hf : PolyBound f) (exponent : ℕ) :
    PolyBound (fun inputLength => f inputLength ^ exponent) := by
  induction exponent with
  | zero => simpa using const 1
  | succ exponent ih => simpa [pow_succ] using ih.mul hf

/-- A polynomial bound has the standard native machine-calculus growth form. -/
theorem exists_mul_pow_bound {f : ℕ → ℕ} (hf : PolyBound f) :
    ∃ A B : ℕ, ∀ n, f n ≤ A * (n + 1) ^ B := by
  exact (hf.polyBounded (fun n : ℕ => n)).exists_le

end PolyBound

end LeanCanny
