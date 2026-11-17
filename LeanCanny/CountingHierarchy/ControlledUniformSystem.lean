/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledIndexedSystem

/-! # Existential systems whose resource bounds are shared across all indices -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P Q : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ}

def UniformBounds (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) : Prop :=
  ∀ w i, C.degreeBound (w, i) = C.degreeBound (w, 0) ∧
    C.massExponent (w, i) = C.massExponent (w, 0) ∧ C.cutoff (w, i) = C.cutoff (w, 0)

noncomputable def uniformSystem
    (CP : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a)
    (CQ : Controlled (fun q : α × ℕ => Q q.1 q.2) (encPair enc encNat) a)
    (hP : CP.UniformBounds) (hQ : CQ.UniformBounds) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (e k : α → ℕ)
    (he : ComputableInPolyTime e enc encNat) (hk : ComputableInPolyTime k enc encUnary) :
    Controlled (fun w => indexedEquationPositivityPolynomial (P w) (Q w) (e w) (k w)) enc (a + 1) := by
  have hz : ComputableInPolyTime (fun w : α => (w, (0 : ℕ))) enc (encPair enc encNat) :=
    ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 0)
  apply CP.indexedSystem CQ E hn e k
    (fun w => max (CP.degreeBound (w, 0)) (CQ.degreeBound (w, 0)))
    (fun w => max (CP.massExponent (w, 0)) (CQ.massExponent (w, 0)))
    (fun w => max (CP.cutoff (w, 0)) (CQ.cutoff (w, 0))) he hk
    (ComputableInPolyTime.binary_max' (CP.degree_computable.comp hz) (CQ.degree_computable.comp hz))
    (ComputableInPolyTime.binary_max' (CP.mass_computable.comp hz) (CQ.mass_computable.comp hz))
    (ComputableInPolyTime.binary_max' (CP.cutoff_computable.comp hz) (CQ.cutoff_computable.comp hz))
  · intro w i
    exact (CP.degree_le (w, i)).trans ((hP w i).1.le.trans (le_max_left _ _))
  · intro w i
    exact (CQ.degree_le (w, i)).trans ((hQ w i).1.le.trans (le_max_right _ _))
  · intro w i
    exact (CP.mass_le (w, i)).trans (Nat.pow_le_pow_right (by decide)
      ((hP w i).2.1.le.trans (le_max_left _ _)))
  · intro w i
    exact (CQ.mass_le (w, i)).trans (Nat.pow_le_pow_right (by decide)
      ((hQ w i).2.1.le.trans (le_max_right _ _)))
  · intro w i
    exact (hP w i).2.2.le.trans (le_max_left _ _)
  · intro w i
    exact (hQ w i).2.2.le.trans (le_max_right _ _)

end LeanCanny.CountingHierarchy.Controlled
