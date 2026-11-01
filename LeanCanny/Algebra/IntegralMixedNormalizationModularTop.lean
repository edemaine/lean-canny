/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeTopPower
/-! # Explicit caller-modulus matrix types for normalization identities -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def modularTop (P : Parameters) (F : Family) (q : List Bool) :
    Matrix (Fin (matrixDimension P F q)) (Fin (matrixDimension P F q)) (ZMod (modulus P q)) :=
  (top F (IntegralMixedVirtualTaskBits.saved P q)).map (Int.castRingHom (ZMod (modulus P q)))

def topRow (P : Parameters) (F : Family) (q : List Bool) : Fin (matrixDimension P F q) :=
  ⟨get P .row q % matrixDimension P F q, Nat.mod_lt _ (matrixDimension_pos P F q)⟩

def topCol (P : Parameters) (F : Family) (q : List Bool) : Fin (matrixDimension P F q) :=
  ⟨get P .col q % matrixDimension P F q, Nat.mod_lt _ (matrixDimension_pos P F q)⟩

theorem topPowerValue_modular (P : Parameters) (F : Family) (q : List Bool) :
    topPowerValue P F q = residueBits (((modularTop P F q) ^ get P .target q) (topRow P F q) (topCol P F q)) := rfl

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
