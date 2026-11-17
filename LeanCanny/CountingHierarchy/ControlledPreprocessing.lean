/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled

/-! # Polynomial-time reindexing of controlled polynomial families -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The same polynomial and source bounds can be used in a larger context,
for example when a short witness and an evaluation prime are appended. -/
@[expose] noncomputable def preprocess {α β : Type} {n : β → ℕ}
    {P : (w : β) → MvPolynomial (Fin (n w)) ℤ}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {a : ℕ}
    (C : Controlled P encB a) (g : α → β) (hg : ComputableInPolyTime g encA encB) :
    Controlled (fun w => P (g w)) encA a where
  arity_computable := C.arity_computable.comp hg
  degreeBound := fun w => C.degreeBound (g w)
  degree_computable := C.degree_computable.comp hg
  degree_le w := C.degree_le (g w)
  massExponent := fun w => C.massExponent (g w)
  mass_computable := C.mass_computable.comp hg
  mass_le w := C.mass_le (g w)
  cutoff := fun w => C.cutoff (g w)
  cutoff_computable := C.cutoff_computable.comp hg
  evaluate := fun q => C.evaluate (g q.1, q.2)
  evaluate_mem := CountingFunction.preprocess C.evaluate_mem (by fun_prop)
  evaluate_eq w p z hp hcut := C.evaluate_eq (g w) p z hp hcut

end LeanCanny.CountingHierarchy.Controlled
