/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitiveResultant

/-! # Canny's shifted resultant with supplied Sylvester orders

Every pair of natural orders defines a Sylvester determinant, independently
of the actual source degrees. Exact source degrees recover `cannyResultant`.
This total version supports encoded metadata tables before their consistency
with the intended polynomial tree has been proved.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

noncomputable def cannyResultantWithDegrees {R : Type*} [CommRing R]
    (p q : Polynomial R) (direction leftOrder rightOrder : ℕ) : Polynomial R :=
  (shiftFamily p direction).resultant (q.map C) leftOrder rightOrder

theorem cannyResultantWithDegrees_exact {R : Type*} [CommRing R]
    (p q : Polynomial R) (direction : ℕ) :
    cannyResultantWithDegrees p q direction p.natDegree q.natDegree = cannyResultant p q direction := rfl

theorem cannyResultantWithDegrees_eq {R : Type*} [CommRing R]
    (p q : Polynomial R) (direction leftOrder rightOrder : ℕ)
    (hl : leftOrder = p.natDegree) (hr : rightOrder = q.natDegree) :
    cannyResultantWithDegrees p q direction leftOrder rightOrder = cannyResultant p q direction := by
  rw [hl, hr]
  rfl

end LeanCanny.Algebra
