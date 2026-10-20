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
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Algebra.MatrixPower Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm coefficientValue

structure CoordinateReaders (projection : Bool) (source : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) where
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  numeratorEvaluator : SpaceFunction numerator
  denominatorEvaluator : SpaceFunction denominator
  numerator_eq : ∀ c i, i < dimension projection (source c) → ∀ k m, 0 < m →
    numerator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((n c i).coeff k : ℤ) : ZMod m)
  denominator_eq : ∀ c i, i < dimension projection (source c) → ∀ k m, 0 < m →
    denominator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((d c i).coeff k : ℤ) : ZMod m)

noncomputable def access (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) :
    IntegerBits.Access (family projection source active row n d) where
  arity := arityCode projection source
  width := widthCode source
  terms := termsCode projection source
  exponent := exponentRead projection source
  coefficient := coefficientValue projection source active row
  numerator := C.numerator
  denominator := C.denominator
  arity_eq := arityCode_eq projection source
  width_eq := widthCode_eq source
  terms_eq := termsCode_eq projection source
  exponent_eq := fun c r _ i hi => exponentRead_packet projection source c r i hi
  coefficient_eq := fun c r _ m hm => coefficientValue_packet projection source active row c r m hm
  numerator_eq := C.numerator_eq
  denominator_eq := C.denominator_eq

theorem access_controls (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (hs : source ∈ FP) :
    (access projection source active row n d C).ControlsPolyTime :=
  ⟨arityCode_mem_FP projection hs, widthCode_mem_FP hs, termsCode_mem_FP projection hs, exponentRead_mem_FP projection hs⟩

attribute [local irreducible] family

noncomputable def evaluator (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (family projection source active row n d).value :=
  (access projection source active row n d C).evaluator (access_controls projection source active row n d C hs)
    (coefficientEvaluator projection source active row hs ha hr) C.numeratorEvaluator C.denominatorEvaluator

end LeanCanny.ETR.TubeRational
