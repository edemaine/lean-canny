/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPowerAccess
public import LeanCanny.Algebra.MatrixPowerSpaceEntries

/-! # Encoded modular determinant families

These shared families and access contracts support the native moment, factor,
and layered-power certificates in BerkowitzSpaceEntries. -/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz

open LeanCanny.Encoding
open MatrixPower
open LeanCanny.Computation

structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def ModularFamily.zeroLanguage (F : ModularFamily) : Language := {c | (F.matrix c).det = 0}

/-- Canonical access on every input context. A concrete encoding must provide
validation or defaults satisfying this contract. -/
structure ModularAccess (F : ModularFamily) where
  access : FactorChild.Access
  correct : ∀ c, FactorChild.CorrectAt access c (F.modulus c) (F.matrix c)


end LeanCanny.Algebra.Berkowitz
