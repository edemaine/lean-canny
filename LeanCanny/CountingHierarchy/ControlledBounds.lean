/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled

/-! # Replacing controlled-family budgets by uniform source bounds -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def withBounds {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (D b cutoff : α → ℕ)
    (hD : ComputableInPolyTime D enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (hc : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w, (P w).totalDegree ≤ D w) (hmass : ∀ w, LeanCanny.Algebra.MvMass.mass (P w) ≤ 2 ^ b w)
    (hcut : ∀ w, C.cutoff w ≤ cutoff w) : Controlled P enc a where
  arity_computable := C.arity_computable
  degreeBound := D
  degree_computable := hD
  degree_le := hdeg
  massExponent := b
  mass_computable := hb
  mass_le := hmass
  cutoff := cutoff
  cutoff_computable := hc
  evaluate := C.evaluate
  evaluate_mem := C.evaluate_mem
  evaluate_eq w p z hp h := C.evaluate_eq w p z hp ((hcut w).trans_lt h)

end LeanCanny.CountingHierarchy.Controlled
