/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRationalSource

/-! # Polynomial-space rational substitution into actual tube systems

Only coordinate polynomial readers remain parameters. Their full space
certificates and canonical modular-query equalities are explicit. Actual source
coefficients and all FP metadata are supplied by the tube/projection modules.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRational

open LeanCanny.Encoding LeanCanny.Computation
open Algebra.MatrixPower Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm coefficientValue

abbrev CoordinateReaders (projection : Bool) (source : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) :=
  IntegerBits.CoordinateReaders (fun c => dimension projection (source c)) n d

-- Preserve the original qualified constructor and field names.
namespace CoordinateReaders
variable {projection : Bool} {source : List Bool → List Bool} {n d : List Bool → ℕ → Polynomial ℤ}

abbrev mk := @IntegerBits.CoordinateReaders.mk (fun c => dimension projection (source c)) n d
abbrev numerator (self : CoordinateReaders projection source n d) := IntegerBits.CoordinateReaders.numerator self
abbrev denominator (self : CoordinateReaders projection source n d) := IntegerBits.CoordinateReaders.denominator self
abbrev numeratorEvaluator (self : CoordinateReaders projection source n d) := IntegerBits.CoordinateReaders.numeratorEvaluator self
abbrev denominatorEvaluator (self : CoordinateReaders projection source n d) := IntegerBits.CoordinateReaders.denominatorEvaluator self
abbrev numerator_eq (self : CoordinateReaders projection source n d) := IntegerBits.CoordinateReaders.numerator_eq self
abbrev denominator_eq (self : CoordinateReaders projection source n d) := IntegerBits.CoordinateReaders.denominator_eq self

end CoordinateReaders

noncomputable def access (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) :
    IntegerBits.Access (family projection source active row n d) :=
  IntegerBits.IndexedSource.access (sourceAccess projection source active row) C

theorem access_controls (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (hs : source ∈ FP) :
    (access projection source active row n d C).ControlsPolyTime :=
  IntegerBits.IndexedSource.access_controls _ (sourceAccess_controls projection source active row hs) C

attribute [local irreducible] family

theorem evaluator (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (family projection source active row n d).value :=
  (access projection source active row n d C).evaluator (access_controls projection source active row n d C hs)
    (coefficientEvaluator projection source active row hs ha hr) C.numeratorEvaluator C.denominatorEvaluator

end LeanCanny.ETR.TubeRational
