/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayBinarySpace
public import LeanCanny.Algebra.MacaulayPolynomialSpace

/-! # Polynomial Macaulay determinants with binary source degrees

This extends the same coefficient access interface and determinant program.
All original source calls are charged by the native space evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayPolynomial
open LeanCanny.Encoding LeanCanny.Computation MacaulayBits

theorem Access.entryBinaryEvaluator {F : Family} (a : Access F) (h : F.layout.BinaryPolyTime)
    (hm : a.modulus ∈ FP) (E : SpaceFunction a.coefficient) : SpaceFunction a.entry :=
  (entryWithIdentityBinaryEvaluator h (E.precompose sourceInput sourceInput_mem_FP)
    (constantEntry_mem_FP hm)).precompose PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

theorem Access.determinantBinaryControls {F : Family} (a : Access F) (h : F.layout.BinaryPolyTime)
    (hm : a.modulus ∈ FP) (hd : a.degree ∈ FP) : a.determinant.ControlsPolyTime :=
  ⟨FixedWidthPolynomial.countCode_mem_FP h.arity h.width, hm, hd⟩

theorem Access.binaryEvaluator {F : Family} (a : Access F) (h : F.layout.BinaryPolyTime)
    (hm : a.modulus ∈ FP) (hd : a.degree ∈ FP) (E : SpaceFunction a.coefficient) : SpaceFunction F.value :=
  BerkowitzPolynomial.ModularAccess.evaluator a.determinant (a.determinantBinaryControls h hm hd)
    (a.entryBinaryEvaluator h hm E)

end LeanCanny.Algebra.MacaulayPolynomial
