/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled

/-! # Changing polynomial specifications while retaining the constructed access data -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def congr {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P Q : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled P enc a) (h : ∀ w, P w = Q w) : Controlled Q enc a where
  arity_computable := C.arity_computable
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := h w ▸ C.degree_le w
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := h w ▸ C.mass_le w
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate := C.evaluate
  evaluate_mem := C.evaluate_mem
  evaluate_eq w p z hp hc := h w ▸ C.evaluate_eq w p z hp hc

end LeanCanny.CountingHierarchy.Controlled
